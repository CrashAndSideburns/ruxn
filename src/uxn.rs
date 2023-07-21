use std::ops::IndexMut;
use std::sync::mpsc::{channel, Receiver, Sender};

use crate::devices::Device;

type Result<T> = std::result::Result<T, UxnError>;

/// All possible errors which may occur while a Uxntal program is being run, as specified
/// [here](https://wiki.xxiivv.com/site/uxntal_errors.html).
///
/// As detailed in the specification, [`UxnError::Underflow`](UxnError#variant.Underflow) and
/// [`UxnError::Overflow`](`UxnError#variant.Overflow`) occur only when an underflow or overflow
/// occurs in one of the stacks of the Uxn stack-machine. In particular, it is not detailed whether
/// or not the *program counter* is allowed to underflow or overflow. This does not currently raise
/// an error, but this is subject to change if the specification is clarified.
#[derive(Debug, PartialEq, Eq)]
pub enum UxnError {
    Underflow,
    Overflow,
    ZeroDiv,
}

/// A stack able to hold exactly 0xff bytes, in accordance with the capacity of the working and
/// return stacks of the Uxn stack-machine, as specified
/// [here](https://wiki.xxiivv.com/site/uxntal_stacks.html).
#[derive(Debug)]
pub struct UxnStack {
    // HACK: Giving s a capacity of 256 rather than 255 is a bit of a silly hack which gives quite
    // a few benefits. Since sp points to the location on the stack where the next byte will be
    // placed, we can tell that the stack is at capacity simply by checking whether or not
    // incrementing sp would cause an overflow. It also means that indexing sp with a u8 is always
    // valid, so we can dispense with bounds-checking and use get_unchecked.
    s: [u8; 0x100],
    sp: u8,
}

impl UxnStack {
    /// Constructs a new, empty [`UxnStack`].
    pub fn new() -> Self {
        UxnStack {
            s: [0x00; 0x100],
            sp: 0,
        }
    }

    pub fn pop(&mut self) -> Result<u8> {
        let new_sp = self.sp.checked_sub(1).ok_or(UxnError::Underflow)?;
        let value = unsafe { self.s.get_unchecked(new_sp as usize) };
        self.sp = new_sp;
        Ok(*value)
    }

    // TODO: Write proper documentation.
    fn update_stack_pointer(
        &mut self,
        operand_bytes: u8,
        result_bytes: u8,
        keep_mode: bool,
    ) -> Result<()> {
        // Check that there are enough bytes on the stack to perform the operation.
        if operand_bytes > self.sp {
            return Err(UxnError::Underflow);
        }

        // Compute the new stack pointer. If keep_mode is true, then we expect result_bytes to be
        // pushed to the stack. If keep_mode is false, then we expect operand_bytes to be popped
        // from the stack, and then for result_bytes to be pushed to the stack.
        let new_sp = if keep_mode {
            self.sp
        } else {
            // The subtraction of operand_bytes does not need to be checked, as we have already
            // checked that operand_bytes <= sp.
            self.sp.wrapping_sub(operand_bytes)
        }
        .checked_add(result_bytes)
        .ok_or(UxnError::Overflow)?;

        self.sp = new_sp;

        Ok(())
    }

    // TODO: Write proper documentation.
    fn get(&self, offset: u8) -> u8 {
        unsafe {
            // This never fails, because the index is guaranteed to be in the range 0..=255.
            *self.s.get_unchecked(self.sp.wrapping_sub(offset) as usize)
        }
    }

    // TODO: Write proper documentation.
    fn get2(&self, offset: u8) -> u16 {
        let msb = self.get(offset.wrapping_add(1));
        let lsb = self.get(offset);
        u16::from_be_bytes([msb, lsb])
    }

    // TODO: Write proper documentation.
    fn set(&mut self, offset: u8, value: u8) {
        unsafe {
            *self
                .s
                .get_unchecked_mut(self.sp.wrapping_sub(offset) as usize) = value;
        }
    }

    // TODO: Write proper documentation.
    fn set2(&mut self, offset: u8, value: u16) {
        let value = value.to_be_bytes();
        let msb = value[0];
        let lsb = value[1];
        self.set(offset.wrapping_add(1), msb);
        self.set(offset, lsb);
    }

    // TODO: UxnStack should probably have a saner set of methods. Someone using the Uxn struct may
    // conceivably want to interact with the CPU's internal stacks, so they should have a more
    // extensive and well-thought-out interfact.
}

pub struct Uxn<T> {
    pub ram: T,
    pub pc: u16,
    pub ws: UxnStack,
    pub rs: UxnStack,

    vrx: Receiver<u16>,
    vtx: Sender<u16>,

    pub devices: [Option<Box<dyn Device>>; 16],
}

impl<T> Uxn<T>
where
    T: IndexMut<u16, Output = u8>,
{
    pub fn new(ram: T) -> Self {
        let (vtx, vrx) = channel();
        Uxn {
            ram,
            pc: 0x0100,
            ws: UxnStack::new(),
            rs: UxnStack::new(),

            vrx,
            vtx,

            devices: [
                None, None, None, None, None, None, None, None, None, None, None, None, None, None,
                None, None,
            ],
        }
    }

    pub fn get_vector_queue_sender(&self) -> Sender<u16> {
        self.vtx.clone()
    }

    fn step(&mut self) -> Result<bool> {
        // Fetch instruction and increment program counter.
        let instruction = self.ram[self.pc];
        self.pc = self.pc.wrapping_add(1);

        // Some useful boolean flags.
        let keep_mode = (instruction & 0b10000000) != 0;
        let return_mode = (instruction & 0b01000000) != 0;
        let immediate = (instruction & 0b00011111) == 0;

        // In almost all cases (with the exception of JSR, STH, and JSI), the stack upon which we
        // operate depends only on whether or not the opcode specifies return mode.
        let stack = if return_mode {
            &mut self.rs
        } else {
            &mut self.ws
        };

        // Mask off the keep and return mode bits of the instruction, leaving only the short mode
        // and opcode bits. We only want to apply this mask if the instruction is not an immediate
        // instruction, as if it is immediate then all of the bits are necessary to identify the
        // instruction.
        let masked_instruction = if immediate {
            instruction
        } else {
            instruction & 0b00111111
        };

        // For the sake of avoiding repetition in the match statement, it is worth defining the
        // stack variables upon which we will be operating here. The names for these variables are
        // taken from the reference Uxn implementation at
        // https://git.sr.ht/~rabbits/uxn11/blob/main/src/uxn.c.
        // FIXME: These variable names should be changed at some point. They are not good.
        let t = stack.get(1);
        let n = stack.get(2);
        let l = stack.get(3);
        let h2 = stack.get2(2);
        let t2 = stack.get2(1);
        let n2 = stack.get2(3);
        let l2 = stack.get2(5);

        // HACK: There are definitely some things here that could be tidier.
        match masked_instruction {
            // Immediate instructions.

            // BRK
            0x00 => {
                return Ok(true);
            }

            // JCI
            0x20 => {
                let msb = self.ram[self.pc];
                let lsb = self.ram[self.pc.wrapping_add(1)];
                self.pc = self.pc.wrapping_add(2);
                stack.update_stack_pointer(1, 0, false)?;
                if t != 0 {
                    self.pc = self.pc.wrapping_add(u16::from_be_bytes([msb, lsb]));
                }
            }

            // JMI
            0x40 => {
                let msb = self.ram[self.pc];
                let lsb = self.ram[self.pc.wrapping_add(1)];
                self.pc = self.pc.wrapping_add(2);
                self.pc = self.pc.wrapping_add(u16::from_be_bytes([msb, lsb]));
            }

            // JSI
            0x60 => {
                let msb = self.ram[self.pc];
                let lsb = self.ram[self.pc.wrapping_add(1)];
                self.pc = self.pc.wrapping_add(2);
                self.rs.update_stack_pointer(0, 2, false)?;
                self.rs.set2(1, self.pc);
                self.pc = self.pc.wrapping_add(u16::from_be_bytes([msb, lsb]));
            }

            // LIT
            0x80 => {
                stack.update_stack_pointer(0, 1, true)?;
                stack.set(1, self.ram[self.pc]);
                self.pc = self.pc.wrapping_add(1);
            }

            // LIT2
            0xa0 => {
                stack.update_stack_pointer(0, 2, true)?;
                let msb = self.ram[self.pc];
                let lsb = self.ram[self.pc.wrapping_add(1)];
                stack.set2(1, u16::from_be_bytes([msb, lsb]));
                self.pc = self.pc.wrapping_add(2);
            }

            // LITr
            0xc0 => {
                stack.update_stack_pointer(0, 1, true)?;
                stack.set(1, self.ram[self.pc]);
                self.pc = self.pc.wrapping_add(1);
            }

            // LIT2r
            0xe0 => {
                stack.update_stack_pointer(0, 2, true)?;
                let msb = self.ram[self.pc];
                let lsb = self.ram[self.pc.wrapping_add(1)];
                stack.set2(1, u16::from_be_bytes([msb, lsb]));
                self.pc = self.pc.wrapping_add(2);
            }

            // Non-immediate instructions.

            // INC(2)
            0x01 => {
                stack.update_stack_pointer(1, 1, keep_mode)?;
                stack.set(1, t + 1);
            }
            0x21 => {
                stack.update_stack_pointer(2, 2, keep_mode)?;
                stack.set2(1, t2 + 1);
            }

            // POP(2)
            0x02 => {
                stack.update_stack_pointer(1, 0, keep_mode)?;
            }
            0x22 => {
                stack.update_stack_pointer(2, 0, keep_mode)?;
            }

            // NIP(2)
            0x03 => {
                stack.update_stack_pointer(2, 1, keep_mode)?;
                stack.set(1, t);
            }
            0x23 => {
                stack.update_stack_pointer(4, 2, keep_mode)?;
                stack.set2(1, t2);
            }

            // SWP(2)
            0x04 => {
                stack.update_stack_pointer(2, 2, keep_mode)?;
                stack.set(1, n);
                stack.set(2, t);
            }
            0x24 => {
                stack.update_stack_pointer(4, 4, keep_mode)?;
                stack.set2(1, n2);
                stack.set2(3, t2);
            }

            // ROT(2)
            0x05 => {
                stack.update_stack_pointer(3, 3, keep_mode)?;
                stack.set(1, l);
                stack.set(2, t);
                stack.set(3, n);
            }
            0x25 => {
                stack.update_stack_pointer(6, 6, keep_mode)?;
                stack.set2(1, l2);
                stack.set2(3, t2);
                stack.set2(5, n2);
            }

            // DUP(2)
            0x06 => {
                stack.update_stack_pointer(1, 2, keep_mode)?;
                stack.set(1, t);
                stack.set(2, t);
            }
            0x26 => {
                stack.update_stack_pointer(2, 4, keep_mode)?;
                stack.set2(1, t2);
                stack.set2(3, t2);
            }

            // OVR(2)
            0x07 => {
                stack.update_stack_pointer(2, 3, keep_mode)?;
                stack.set(1, n);
                stack.set(2, t);
                stack.set(3, n);
            }
            0x27 => {
                stack.update_stack_pointer(4, 6, keep_mode)?;
                stack.set2(1, n2);
                stack.set2(3, t2);
                stack.set2(5, n2);
            }

            // EQU(2)
            0x08 => {
                stack.update_stack_pointer(2, 1, keep_mode)?;
                stack.set(1, (n == t).into());
            }
            0x28 => {
                stack.update_stack_pointer(4, 1, keep_mode)?;
                stack.set(1, (n2 == t2).into());
            }

            // NEQ(2)
            0x09 => {
                stack.update_stack_pointer(2, 1, keep_mode)?;
                stack.set(1, (n != t).into());
            }
            0x29 => {
                stack.update_stack_pointer(4, 1, keep_mode)?;
                stack.set(1, (n2 != t2).into());
            }

            // GTH(2)
            0x0a => {
                stack.update_stack_pointer(2, 1, keep_mode)?;
                stack.set(1, (n > t).into());
            }
            0x2a => {
                stack.update_stack_pointer(4, 1, keep_mode)?;
                stack.set(1, (n2 > t2).into());
            }

            // LTH(2)
            0x0b => {
                stack.update_stack_pointer(2, 1, keep_mode)?;
                stack.set(1, (n < t).into());
            }
            0x2b => {
                stack.update_stack_pointer(4, 1, keep_mode)?;
                stack.set(1, (n2 < t2).into());
            }

            // JMP(2)
            0x0c => {
                stack.update_stack_pointer(1, 0, keep_mode)?;
                self.pc = self.pc.wrapping_add_signed(i8::from_be_bytes([t]).into());
            }
            0x2c => {
                stack.update_stack_pointer(2, 0, keep_mode)?;
                self.pc = t2;
            }

            // JCN(2)
            0x0d => {
                stack.update_stack_pointer(2, 0, keep_mode)?;
                if n != 0 {
                    self.pc = self.pc.wrapping_add_signed(i8::from_be_bytes([t]).into());
                }
            }
            0x2d => {
                stack.update_stack_pointer(3, 0, keep_mode)?;
                if l != 0 {
                    self.pc = t2;
                }
            }

            // JSR(2)
            0x0e => {
                stack.update_stack_pointer(1, 0, keep_mode)?;
                self.rs.update_stack_pointer(0, 2, false)?;
                self.rs.set2(1, self.pc);
                self.pc = self.pc.wrapping_add_signed(i8::from_be_bytes([t]).into());
            }
            0x2e => {
                stack.update_stack_pointer(2, 0, keep_mode)?;
                self.rs.update_stack_pointer(0, 2, false)?;
                self.rs.set2(1, self.pc);
                self.pc = t2
            }

            // STH(2)
            0x0f => {
                stack.update_stack_pointer(1, 0, keep_mode)?;
                let other_stack = if return_mode {
                    &mut self.ws
                } else {
                    &mut self.rs
                };
                other_stack.update_stack_pointer(0, 1, false)?;
                other_stack.set(1, t);
            }
            0x2f => {
                stack.update_stack_pointer(2, 0, keep_mode)?;
                let other_stack = if return_mode {
                    &mut self.ws
                } else {
                    &mut self.rs
                };
                other_stack.update_stack_pointer(0, 2, false)?;
                other_stack.set2(1, t2);
            }

            // LDZ(2)
            0x10 => {
                stack.update_stack_pointer(1, 1, keep_mode)?;
                stack.set(1, self.ram[t.into()]);
            }
            0x30 => {
                stack.update_stack_pointer(1, 2, keep_mode)?;
                stack.set(1, self.ram[t.wrapping_add(1).into()]);
                stack.set(2, self.ram[t.into()]);
            }

            // STZ(2)
            0x11 => {
                stack.update_stack_pointer(2, 0, keep_mode)?;
                self.ram[t.into()] = n;
            }
            0x31 => {
                stack.update_stack_pointer(3, 0, keep_mode)?;
                self.ram[t.wrapping_add(1).into()] = n;
                self.ram[t.into()] = l;
            }

            // LDR(2)
            0x12 => {
                stack.update_stack_pointer(1, 1, keep_mode)?;
                stack.set(
                    1,
                    self.ram[self.pc.wrapping_add_signed(i8::from_be_bytes([t]).into())],
                );
            }
            0x32 => {
                stack.update_stack_pointer(1, 2, keep_mode)?;
                stack.set(
                    1,
                    self.ram[self
                        .pc
                        .wrapping_add_signed(i8::from_be_bytes([t]).into())
                        .wrapping_add(1)],
                );
                stack.set(
                    2,
                    self.ram[self.pc.wrapping_add_signed(i8::from_be_bytes([t]).into())],
                );
            }

            // STR(2)
            0x13 => {
                stack.update_stack_pointer(2, 0, keep_mode)?;
                self.ram[self.pc.wrapping_add_signed(i8::from_be_bytes([t]).into())] = n;
            }
            0x33 => {
                stack.update_stack_pointer(3, 0, keep_mode)?;
                self.ram[self.pc.wrapping_add_signed(i8::from_be_bytes([t]).into())] = l;
                self.ram[self
                    .pc
                    .wrapping_add_signed(i8::from_be_bytes([t]).into())
                    .wrapping_add(1)] = n;
            }

            // LDA(2)
            0x14 => {
                stack.update_stack_pointer(2, 1, keep_mode)?;
                stack.set(1, self.ram[t2]);
            }
            0x34 => {
                stack.update_stack_pointer(2, 2, keep_mode)?;
                stack.set(1, self.ram[t2.wrapping_add(1)]);
                stack.set(2, self.ram[t2]);
            }

            // STA(2)
            0x15 => {
                stack.update_stack_pointer(3, 0, keep_mode)?;
                self.ram[t2] = l;
            }
            0x35 => {
                stack.update_stack_pointer(4, 0, keep_mode)?;
                let value = n2.to_be_bytes();
                self.ram[t2] = value[0];
                self.ram[t2.wrapping_add(1)] = value[1];
            }

            // DEI(2)
            0x16 => {
                stack.update_stack_pointer(1, 1, keep_mode)?;
                todo!();
            }
            0x36 => {
                stack.update_stack_pointer(1, 2, keep_mode)?;
                todo!();
            }

            // DEO(2)
            0x17 => {
                stack.update_stack_pointer(2, 0, keep_mode)?;
                todo!();
            }
            0x37 => {
                stack.update_stack_pointer(3, 0, keep_mode)?;
                todo!();
            }

            // ADD(2)
            0x18 => {
                stack.update_stack_pointer(2, 1, keep_mode)?;
                stack.set(1, n.wrapping_add(t));
            }
            0x38 => {
                stack.update_stack_pointer(4, 2, keep_mode)?;
                stack.set2(1, n2.wrapping_add(t2));
            }

            // SUB(2)
            0x19 => {
                stack.update_stack_pointer(2, 1, keep_mode)?;
                stack.set(1, n.wrapping_sub(t));
            }
            0x39 => {
                stack.update_stack_pointer(4, 2, keep_mode)?;
                stack.set2(1, n2.wrapping_sub(t2));
            }

            // MUL(2)
            0x1a => {
                stack.update_stack_pointer(2, 1, keep_mode)?;
                stack.set(1, n.wrapping_mul(t));
            }
            0x3a => {
                stack.update_stack_pointer(4, 2, keep_mode)?;
                stack.set2(1, n2.wrapping_mul(t2));
            }

            // DIV(2)
            0x1b => {
                let quotient = n.checked_div(t).ok_or(UxnError::ZeroDiv)?;
                stack.update_stack_pointer(2, 1, keep_mode)?;
                stack.set(1, quotient);
            }
            0x3b => {
                let quotient = n2.checked_div(t2).ok_or(UxnError::ZeroDiv)?;
                stack.update_stack_pointer(4, 2, keep_mode)?;
                stack.set2(1, quotient);
            }

            // AND(2)
            0x1c => {
                stack.update_stack_pointer(2, 1, keep_mode)?;
                stack.set(1, n & t);
            }
            0x3c => {
                stack.update_stack_pointer(4, 2, keep_mode)?;
                stack.set2(1, n2 & t2);
            }

            // ORA(2)
            0x1d => {
                stack.update_stack_pointer(2, 1, keep_mode)?;
                stack.set(1, n | t);
            }
            0x3d => {
                stack.update_stack_pointer(4, 2, keep_mode)?;
                stack.set2(1, n2 | t2);
            }

            // EOR(2)
            0x1e => {
                stack.update_stack_pointer(2, 1, keep_mode)?;
                stack.set(1, n ^ t);
            }
            0x3e => {
                stack.update_stack_pointer(4, 2, keep_mode)?;
                stack.set2(1, n2 ^ t2);
            }

            // SFT(2)
            0x1f => {
                stack.update_stack_pointer(2, 1, keep_mode)?;
                stack.set(1, (n >> (t & 0x0f)) << ((t & 0xf0) >> 4));
            }
            0x3f => {
                stack.update_stack_pointer(3, 2, keep_mode)?;
                stack.set2(1, (h2 >> (t & 0x0f)) << ((t & 0xf0) >> 4));
            }

            // Impossible.
            _ => {
                unreachable!();
            }
        }

        Ok(false)
    }

    pub fn run_vector(&mut self) -> Result<()> {
        loop {
            if self.step()? {
                break;
            }
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // A simple RAM implementation for testing purposes. The reason for using a HashMap for
    // addresses outside of the range of some vector is to allow the construction of TestRam
    // directly from the output of uxnasm. In testing, reads to and writes from RAM are fairly
    // uncommon, so this shouldn't substantially impact test performance.
    struct TestRam {
        program: Vec<u8>,
        variables: std::collections::HashMap<u16, u8>,
    }

    impl std::ops::Index<u16> for TestRam {
        type Output = u8;

        fn index(&self, index: u16) -> &Self::Output {
            self.program
                .get((index - 0x0100) as usize)
                .or_else(|| self.variables.get(&index))
                .unwrap_or(&0x00)
        }
    }

    impl std::ops::IndexMut<u16> for TestRam {
        fn index_mut(&mut self, index: u16) -> &mut Self::Output {
            self.program
                .get_mut((index - 0x0100) as usize)
                .unwrap_or_else(|| self.variables.entry(index).or_insert(0x00))
        }
    }

    impl TestRam {
        fn from_tal(tal: &str) -> Self {
            let mut assembler = std::process::Command::new("uxnasm")
                .args(["/dev/stdin", "/dev/stdout"])
                .stdin(std::process::Stdio::piped())
                .stdout(std::process::Stdio::piped())
                .stderr(std::process::Stdio::null())
                .spawn()
                .expect("uxnasm is not installed");
            std::io::Write::write(&mut assembler.stdin.take().unwrap(), tal.as_bytes()).unwrap();
            let program = assembler.wait_with_output().unwrap().stdout;

            TestRam {
                program,
                variables: std::collections::HashMap::new(),
            }
        }
    }

    // TODO: This is very much just a proof of concept test. More extensive tests will be added in
    // the future.
    #[test]
    fn test_add() {
        let mut cpu = Uxn::new(TestRam::from_tal("#01 #02 ADD"));
        cpu.run_vector().unwrap();
        assert_eq!(cpu.ws.pop(), Ok(0x03));
    }
}
