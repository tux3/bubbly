use riscv::register;
use riscv::register::mtvec::{Mtvec, TrapMode};

/// Defines a trap handler
#[macro_export]
macro_rules! trap_handler {
    ($name:ident, $body:block) => {
        #[unsafe(link_section = ".trap_handler")]
        #[unsafe(no_mangle)]
        pub unsafe extern "C" fn ${concat($name, _impl)}() $body

        #[unsafe(link_section = ".trap_handler")]
        #[unsafe(no_mangle)]
        #[unsafe(naked)]
        pub unsafe extern "C" fn $name() {
            trap_save_and_call!(${concat($name, _impl)});
        }
    };
}


/// Used to define a trap handler ASM trampoline
#[macro_export]
macro_rules! trap_save_and_call {
    ($trap_handler:ident) => {
        unsafe {
            core::arch::naked_asm!(
                "addi sp, sp, -128",
                "sd ra, 0(sp)",
                "sd t0, 8(sp)",
                "sd t1, 16(sp)",
                "sd t2, 24(sp)",
                "sd t3, 32(sp)",
                "sd t4, 40(sp)",
                "sd t5, 48(sp)",
                "sd t6, 56(sp)",
                "sd a0, 64(sp)",
                "sd a1, 72(sp)",
                "sd a2, 80(sp)",
                "sd a3, 88(sp)",
                "sd a4, 96(sp)",
                "sd a5, 104(sp)",
                "sd a6, 112(sp)",
                "sd a7, 120(sp)",
                "lla a0, {trap_handler}",
                "jalr a0",
                "ld ra, 0(sp)",
                "ld t0, 8(sp)",
                "ld t1, 16(sp)",
                "ld t2, 24(sp)",
                "ld t3, 32(sp)",
                "ld t4, 40(sp)",
                "ld t5, 48(sp)",
                "ld t6, 56(sp)",
                "ld a0, 64(sp)",
                "ld a1, 72(sp)",
                "ld a2, 80(sp)",
                "ld a3, 88(sp)",
                "ld a4, 96(sp)",
                "ld a5, 104(sp)",
                "ld a6, 112(sp)",
                "ld a7, 120(sp)",
                "addi sp, sp, 128",
                "mret",
                trap_handler = sym $trap_handler
            )
        };
    };
}

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
