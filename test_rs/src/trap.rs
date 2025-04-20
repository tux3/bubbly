use riscv::register;
use riscv::register::mtvec::{Mtvec, TrapMode};

pub fn set_direct_trap_handler(handler: unsafe extern "C" fn()) {
    unsafe {
        let mut mtvec = Mtvec::from_bits(0);
        mtvec.set_address(handler as usize);
        mtvec.set_trap_mode(TrapMode::Direct);
        register::mtvec::write(mtvec);
    }
}

pub fn increment_mepc() {
    let mut mepc = register::mepc::read();
    let instr = unsafe { core::ptr::read_volatile(mepc as *const u8) };
    if instr & 0b11 == 0b11 {
        mepc += 4; // Non-compressed instr
    } else {
        mepc += 2; // Compressed instr
    }
    unsafe { register::mepc::write(mepc) };
}
