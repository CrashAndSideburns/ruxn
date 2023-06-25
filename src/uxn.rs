use std::error::Error;
use std::ops::{Index, IndexMut};

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
    s: [u8; 0xff],
    sp: u8,
}

impl UxnStack {
    /// Constructs a new, empty [`UxnStack`].
    pub fn new() -> Self {
        UxnStack {
            s: [0x00; 0xff],
            sp: 0,
        }
    }

    /// Return the byte at index `offset` on the stack if there are at least `offset` bytes on the
    /// stack. Calling with `offset == 0` results in undefined behaviour.
    ///
    /// # Examples
    ///
    /// ```
    /// use ruxn::uxn::UxnStack;
    ///
    /// let mut stack = UxnStack::new();
    /// stack.push(0x02).unwrap();
    /// stack.push(0x01).unwrap();
    /// 
    /// assert_eq!(Ok(0x01), stack.get(1));
    /// assert_eq!(Ok(0x02), stack.get(2));
    /// ```
    ///
    /// ```
    /// use ruxn::uxn::{UxnStack, UxnError};
    ///
    /// let mut stack = UxnStack::new();
    /// stack.push(0x00).unwrap();
    ///
    /// assert_eq!(Err(UxnError::Underflow), stack.get(2));
    /// ```
    ///
    /// # Errors
    ///
    /// Returns [`UxnError::Underflow`](self::UxnError#variant.Underflow) if there are fewer than
    /// `offset` bytes on the stack.
    ///
    /// # Panics
    ///
    /// May panic if called with `offset == 0`.
    pub fn get(&self, offset: u8) -> Result<u8> {
        let index = self.sp.checked_sub(offset).ok_or(UxnError::Underflow)?;
        Ok(self.s[index as usize])
    }

    /// Return the short with LSB at index `offset` on the stack if there are at least `offset+1`
    /// bytes on the stack. Calling with `offset == 0` results in undefined behaviour.
    ///
    /// # Examples
    ///
    /// ```
    /// use ruxn::uxn::UxnStack;
    ///
    /// let mut stack = UxnStack::new();
    /// stack.push(0x03).unwrap();
    /// stack.push(0x02).unwrap();
    /// stack.push(0x01).unwrap();
    ///
    /// assert_eq!(Ok(0x0201), stack.get2(1));
    /// assert_eq!(Ok(0x0302), stack.get2(2));
    /// ```
    ///
    /// ```
    /// use ruxn::uxn::{UxnStack, UxnError};
    ///
    /// let mut stack = UxnStack::new();
    /// stack.push(0x00).unwrap();
    ///
    /// assert_eq!(Err(UxnError::Underflow), stack.get2(2));
    /// assert_eq!(Err(UxnError::Underflow), stack.get2(1));
    /// ```
    ///
    /// # Errors
    ///
    /// Returns [`UxnError::Underflow`](self::UxnError#variant.Underflow) if there are fewer than
    /// `offset+1` bytes on the stack.
    ///
    /// # Panics
    ///
    /// May panic if called with `offset == 0`.
    pub fn get2(&self, offset: u8) -> Result<u16> {
        let msb = self.get(offset.checked_add(1).ok_or(UxnError::Underflow)?)?;
        // We can be a bit cavalier about checking for errors here. If we got to this point, we
        // know that self.sp - offset does not underflow and is a good index.
        let lsb = self.s[(self.sp - offset) as usize];
        Ok(u16::from_be_bytes([msb, lsb]))
    }

    /// Set the byte at index `offset` on the stack to `value` if there are at least `offset`
    /// bytes on the stack. If `offset == 0`, `value` will be placed on top of the stack if
    /// it is not full, but the stack pointer will not be incremented.
    ///
    /// # Examples
    ///
    /// ```
    /// use ruxn::uxn::UxnStack;
    ///
    /// let mut stack = UxnStack::new();
    /// stack.push(0x02).unwrap();
    /// stack.push(0x01).unwrap();
    ///
    /// assert_eq!(Ok(()), stack.set(2, 0x03));
    /// assert_eq!(Ok(0x03), stack.get(2));
    ///
    /// assert_eq!(Ok(()), stack.set(0, 0x00));
    /// assert_eq!(Ok(0x01), stack.pop());
    /// ```
    ///
    /// ```
    /// use ruxn::uxn::{UxnStack, UxnError};
    ///
    /// let mut stack = UxnStack::new();
    /// stack.push(0x00).unwrap();
    ///
    /// assert_eq!(Err(UxnError::Underflow), stack.set(2, 0x01));
    /// ```
    ///
    /// ```
    /// use ruxn::uxn::{UxnStack, UxnError};
    ///
    /// let mut stack = UxnStack::new();
    /// for _ in 0x00..0xff {
    ///     stack.push(0x00).unwrap();
    /// }
    ///
    /// assert_eq!(Err(UxnError::Overflow), stack.set(0, 0x01));
    /// ```
    ///
    /// # Errors
    ///
    /// Returns [`UxnError::Underflow`](self::UxnError#variant.Underflow) if there are fewer than
    /// `offset` bytes on the stack. Returns
    /// [`UxnError::Overflow`](self::UxnError#variant.Overflow) if the stack is full and `offset ==
    /// 0`. In either case, the stack remains unmodified.
    pub fn set(&mut self, offset: u8, value: u8) -> Result<()> {
        *self
            .s
            .get_mut(self.sp.checked_sub(offset).ok_or(UxnError::Underflow)? as usize)
            .ok_or(UxnError::Overflow)? = value;
        Ok(())
    }

    /// Set the short with LSB at index `offset` on the stack to `value` if there are at least
    /// `offset+1` bytes on the stack. If `offset == 0`, `value` will be placed on top of the stack
    /// if it has room for at least two more bytes, but the stack pointer will not be incremented.
    ///
    /// # Examples
    /// 
    /// ```
    /// use ruxn::uxn::UxnStack;
    ///
    /// let mut stack = UxnStack::new();
    /// stack.push2(0x0302).unwrap();
    /// stack.push(0x01).unwrap();
    ///
    /// assert_eq!(Ok(()), stack.set2(1, 0x0504));
    /// assert_eq!(Ok(0x0504), stack.get2(1));
    /// assert_eq!(Ok(0x0305), stack.get2(2));
    ///
    /// assert_eq!(Ok(()), stack.set(0, 0x0000));
    /// assert_eq!(Ok(0x0504), stack.pop2());
    /// ```
    ///
    /// ```
    /// use ruxn::uxn::{UxnStack, UxnError};
    ///
    /// let mut stack = UxnStack::new();
    /// stack.push(0x00).unwrap();
    ///
    /// assert_eq!(Err(UxnError::Underflow), stack.set2(1, 0x01));
    /// assert_eq!(Err(UxnError::Underflow), stack.set2(2, 0x01));
    /// ```
    ///
    /// ```
    /// use ruxn::uxn::{UxnStack, UxnError};
    ///
    /// let mut stack = UxnStack::new();
    /// for _ in 0x00..0xfe {
    ///     stack.push(0x00).unwrap();
    /// }
    ///
    /// assert_eq!(Err(UxnError::Overflow), stack.set2(0, 0x0102));
    /// ```
    ///
    /// # Errors
    ///
    /// Returns [`UxnError::Underflow`](self::UxnError#variant.Underflow) if there are fewer than
    /// `offset+1` bytes on the stack. Returns
    /// [`UxnError::Overflow`](self::UxnError#variant.Overflow) if the stack does not have room for
    /// two more bytes and `offset == 0`. In either case, the stack remains unmodified.
    pub fn set2(&mut self, offset: u8, value: u16) -> Result<()> {
        let value = value.to_be_bytes();
        let msb = value[0];
        let lsb = value[1];
        if offset == 0 {
            *self.s.get_mut(self.sp.checked_add(1).ok_or(UxnError::Overflow)? as usize).ok_or(UxnError::Overflow)? = lsb;
            // We can be a bit cavalier about checking for errors here. If we got to this point, we
            // know that self.sp is a good index.
            self.s[self.sp as usize] = msb;
        } else {
            self.set(offset.checked_add(1).ok_or(UxnError::Underflow)?, msb)?;
            // We can be a bit cavalier about checking for errors here. If we got to this point, we
            // know that self.sp - offset does not underflow and is a good index.
            self.s[(self.sp - offset) as usize] = lsb;
        }
        Ok(())
    }

    /// Pop a byte from the stack if it is not empty.
    ///
    /// # Examples
    /// ```
    /// use ruxn::uxn::UxnStack;
    ///
    /// let mut stack = UxnStack::new();
    /// stack.push(0x01).unwrap();
    ///
    /// assert_eq!(Ok(0x01), stack.pop());
    /// ```
    ///
    /// ```
    /// use ruxn::uxn::{UxnStack, UxnError};
    ///
    /// let mut stack = UxnStack::new();
    ///
    /// assert_eq!(Err(UxnError::Underflow), stack.pop());
    /// ```
    ///
    /// # Errors
    ///
    /// Returns [`UxnError::Underflow`](self::UxnError#variant.Underflow) if the stack is already
    /// empty, in which case it remains unmodified.
    pub fn pop(&mut self) -> Result<u8> {
        let value = self.get(1)?;
        self.sp -= 1;
        Ok(value)
    }

    /// Pop a short from the stack if there are at least two bytes on the stack.
    ///
    /// # Examples
    ///
    /// ```
    /// use ruxn::uxn::UxnStack;
    ///
    /// let mut stack = UxnStack::new();
    /// stack.push2(0x0102).unwrap();
    ///
    /// assert_eq!(Ok(0x0102), stack.pop2());
    ///
    /// stack.push(0x01).unwrap();
    /// stack.push(0x02).unwrap();
    ///
    /// assert_eq!(Ok(0x0102), stack.pop2());
    /// ```
    ///
    /// ```
    /// use ruxn::uxn::{UxnStack, UxnError};
    ///
    /// let mut stack = UxnStack::new();
    ///
    /// assert_eq!(Err(UxnError::Underflow), stack.pop2());
    ///
    /// stack.push(0x01).unwrap();
    ///
    /// assert_eq!(Err(UxnError::Underflow), stack.pop2());
    /// assert_eq!(Ok(0x01), stack.pop());
    /// ```
    ///
    /// # Errors
    ///
    /// Returns [`UxnError::Underflow`](self::UxnError#variant.Underflow) if the stack does not
    /// contain at least two bytes, in which case it remains unmodified.
    pub fn pop2(&mut self) -> Result<u16> {
        let value = self.get2(1)?;
        self.sp -= 2;
        Ok(value)
    }

    /// Pushes a byte onto the stack if it is not full.
    ///
    /// # Examples
    ///
    /// ```
    /// use ruxn::uxn::UxnStack;
    ///
    /// let mut stack = UxnStack::new();
    ///
    /// assert_eq!(Ok(()), stack.push(0x01));
    /// assert_eq!(Ok(0x01), stack.pop());
    /// ```
    ///
    /// ```
    /// use ruxn::uxn::{UxnStack, UxnError};
    ///
    /// let mut stack = UxnStack::new();
    /// for _ in 0x00..0xff {
    ///     stack.push(0x01).unwrap();
    /// }
    ///
    /// assert_eq!(Err(UxnError::Overflow), stack.push(0x02));
    /// ```
    ///
    /// # Errors
    ///
    /// Returns [`UxnError::Overflow`](self::UxnError#variant.Overflow) if the stack is full, in
    /// which case it remains unmodified.
    pub fn push(&mut self, value: u8) -> Result<()> {
        self.set(0, value)?;
        self.sp += 1;
        Ok(())
    }

    /// Pushes a short onto the stack if it has room for at least two more bytes.
    ///
    /// # Examples
    ///
    /// ```
    /// use ruxn::uxn::UxnStack;
    ///
    /// let mut stack = UxnStack::new();
    ///
    /// assert_eq!(Ok(()), stack.push2(0x0102));
    /// assert_eq!(Ok(0x02), stack.pop());
    /// assert_eq!(Ok(0x01), stack.pop());
    /// ```
    ///
    /// ```
    /// use ruxn::uxn::{UxnStack, UxnError};
    ///
    /// let mut stack = UxnStack::new();
    /// for _ in 0x00..0xfe {
    ///     stack.push(0x01).unwrap();
    /// }
    ///
    /// assert_eq!(Err(UxnError::Overflow), stack.push2(0x0203));
    /// assert_eq!(Ok(0x01), stack.pop());
    /// ```
    ///
    /// # Errors
    ///
    /// Returns [`UxnError::Overflow`](self::UxnError#variant.Overflow) if the stack does not have
    /// room for two more bytes, in which case it remains unmodified.
    pub fn push2(&mut self, value: u16) -> Result<()> {
        self.set2(0, value)?;
        self.sp += 2;
        Ok(())
    }
}

pub struct Uxn<T> {
    pub ram: T,
    pc: u16,
    ws: UxnStack,
    rs: UxnStack,

    // TODO: I'm not sure how I want devices to work for now. This is mostly a placeholder.
    devices: [u8; 256],
}

impl<T> Uxn<T>
where
    T: IndexMut<u16, Output = u8>,
{
    pub fn new(ram: T) -> Self {
        todo!();
    }

    fn step(&mut self) -> Result<()> {
        todo!();
    }

    pub fn run(&mut self) {
        todo!();
    }
}
