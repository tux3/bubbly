#![no_std]

use core::hint::unreachable_unchecked;
use core::panic::PanicInfo;
use riscv::register;
use riscv::register::mtvec::{Mtvec, TrapMode};

// TODO: Should use the linker script to leave a fixed size for the stack at the end
const SRAM_BASE: usize = 0x08000000000;
const SRAM_SIZE: usize = 32 * 1024;
const PLATFORM_BASE: usize = 0x20000000000;

const GPIO_PTR_FAIL: *mut u8 = (PLATFORM_BASE + 0x10) as *mut u8;
const GPIO_PTR_SUCCESS: *mut u8 = (PLATFORM_BASE + 0x11) as *mut u8;

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

/// Report test failure by setting the fail GPIO pin
pub fn report_fail() {
    unsafe { core::ptr::write_volatile(GPIO_PTR_FAIL, 1u8) };
}

/// Report test success by setting the success GPIO pin
pub fn report_success() {
    unsafe { core::ptr::write_volatile(GPIO_PTR_SUCCESS, 1u8) };
}

pub fn halt() -> ! {
    loop {
        riscv::asm::wfi();
    }
}

#[panic_handler]
pub unsafe fn panic_handler(_panic: &PanicInfo<'_>) -> ! {
    // SAFETY: Because we build with panic_immediate_abort, this is never actually called
    unsafe { unreachable_unchecked() }
}
