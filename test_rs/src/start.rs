use riscv::register;
use riscv::register::mtvec::{Mtvec, TrapMode};
use crate::{halt, report_fail, SRAM_BASE, SRAM_SIZE};

unsafe extern "C" {
    fn main() -> ();
}


/// Entry point. We need to set up the stack in pure asm.
#[unsafe(link_section = ".start")]
#[unsafe(no_mangle)]
#[unsafe(naked)]
unsafe extern "C" fn start() -> ! {
    const STACK_PTR: usize = SRAM_BASE + SRAM_SIZE;
    unsafe {
        core::arch::naked_asm!(
            "la sp, {sp}",
            "j start_rust",
            sp = const STACK_PTR,
        )
    }
}

/// Continuation from `start`
#[unsafe(link_section = ".start")]
#[unsafe(no_mangle)]
unsafe extern "C" fn start_rust() -> ! {
    // Setup default trap handler
    unsafe {
        let mut mtvec = Mtvec::from_bits(0);
        mtvec.set_address(default_trap_handler as usize);
        mtvec.set_trap_mode(TrapMode::Direct);
        register::mtvec::write(mtvec);
    }

    // We expect main to report success or failure before returning
    unsafe { main(); }

    // If main forgets to report success/failure, we count this as a failure
    report_fail();

    // Simulation should stop immediately on the report_fail clock cycle,
    // but in case ifetch/exec run ahead, we give them an empty loop to spin in
    halt();
}

#[unsafe(link_section = ".trap_handler")]
#[unsafe(no_mangle)]
unsafe extern "C" fn default_trap_handler() -> ! {
    report_fail();
    halt();
}
