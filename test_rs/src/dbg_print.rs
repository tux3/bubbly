use crate::TOHOST_PTR;

fn debug_print_byte(c: u8) {
    const DEVICE_CHAR: u64 =          0x0100_0000_0000_0000;
    const DEVICE_COMMAND_WRITE: u64 = 0x0001_0000_0000_0000;

    let cmd = DEVICE_CHAR | DEVICE_COMMAND_WRITE | (c as u64);
    unsafe { core::ptr::write_volatile(TOHOST_PTR, cmd) };
}

pub fn debug_println(str: &str) {
    for c in str.as_bytes() {
        debug_print_byte(*c);
    }
    debug_print_byte(b'\n');
}
