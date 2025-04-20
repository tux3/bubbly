#![no_std]
#![no_main]
#![feature(naked_functions)]
#![feature(macro_metavar_expr_concat)]

mod start;
mod dbg_print;
pub use dbg_print::{debug_println};
mod trap;
pub use trap::{set_direct_trap_handler, increment_mepc};

use core::hint::unreachable_unchecked;
use core::panic::PanicInfo;

// TODO: Should use the linker script to leave a fixed size for the stack at the end
const SRAM_BASE: usize = 0x0;
const SRAM_SIZE: usize = 32 * 1024;

const PLATFORM_BASE: usize = 0x8000000000;
const GPIO_PTR_FAIL: *mut u8 = (PLATFORM_BASE + 0x10) as *mut u8;
const GPIO_PTR_SUCCESS: *mut u8 = (PLATFORM_BASE + 0x11) as *mut u8;

const TOHOST_PTR: *mut u64 = 0x20000000000 as *mut u64;

#[panic_handler]
pub unsafe fn panic_handler(_panic: &PanicInfo<'_>) -> ! {
    // SAFETY: Because we build with panic_immediate_abort, this is never actually called
    unsafe { unreachable_unchecked() }
}

pub fn halt() -> ! {
    loop {
        riscv::asm::wfi();
    }
}

/// Report test failure by setting the fail GPIO pin
pub fn report_fail() {
    unsafe { core::ptr::write_volatile(GPIO_PTR_FAIL, 1u8) };
}

/// Report test success by setting the success GPIO pin
pub fn report_success() {
    unsafe { core::ptr::write_volatile(GPIO_PTR_SUCCESS, 1u8) };
}

pub fn fatal(msg: &str) -> ! {
    debug_println(msg);
    report_fail();
    halt();
}
