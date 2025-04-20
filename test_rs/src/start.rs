use riscv::register;
use riscv::register::mtvec::{Mtvec, TrapMode};
use crate::{halt, report_fail, SRAM_BASE, SRAM_SIZE};

unsafe extern "C" {
    fn main() -> ();
}

/// Common test entry point
/// We expect main to report success or failure before returning
/// If main forgets, we count this as a failure
#[unsafe(link_section = ".start")]
#[unsafe(no_mangle)]
unsafe extern "C" fn start() -> ! {
    unsafe {
        const STACK_PTR: usize = SRAM_BASE + SRAM_SIZE;
        core::arch::asm!(
        "add sp, {sp}, 0",
        sp = in(reg) STACK_PTR,
        );

        let mut mtvec = Mtvec::from_bits(0);
        mtvec.set_address(default_trap_handler as usize);
        mtvec.set_trap_mode(TrapMode::Direct);
        register::mtvec::write(mtvec);
    }

    unsafe { main(); }

    report_fail();
    halt();
}

#[unsafe(link_section = ".trap_handler")]
#[unsafe(no_mangle)]
unsafe extern "C" fn default_trap_handler() -> ! {
    report_fail();
    halt();
}
