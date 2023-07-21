pub trait Device {
    fn read_byte(&mut self, address: u8) -> u8;
    fn write_byte(&mut self, address: u8, byte: u8);
    fn read_short(&mut self, address: u8) -> u16;
    fn write_short(&mut self, address: u8, short: u16);
}
