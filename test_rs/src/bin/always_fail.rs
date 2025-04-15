#![no_std]
#![no_main]

use core::hint::unreachable_unchecked;

const SRAM_BASE: usize = 0x08000000000;
const SRAM_SIZE: usize = 32 * 1024;
const PLATFORM_BASE: usize = 0x20000000000;

const GPIO_PTR_FAIL: *mut u8 = (PLATFORM_BASE + 0x10) as *mut u8;
const GPIO_PTR_SUCCESS: *mut u8 = (PLATFORM_BASE + 0x11) as *mut u8;

#[unsafe(link_section = ".start")]
#[unsafe(no_mangle)]
unsafe extern "C" fn start() -> ! {
    unsafe {
        const STACK_PTR: usize = SRAM_BASE + SRAM_SIZE;
        core::arch::asm!(
        "add sp, {sp}, 0",
        sp = in(reg) STACK_PTR,
        );
    }

    main();
    halt();
}

#[panic_handler]
unsafe fn panic_handler(_panic: &core::panic::PanicInfo<'_>) -> ! {
    // SAFETY: Because we build with panic_immediate_abort, this is never actually called
    unsafe { unreachable_unchecked() }
}

#[unsafe(link_section = ".trap_handler")]
#[unsafe(no_mangle)]
unsafe extern "C" fn trap_handler() {
    report_fail();
    halt();
}

fn report_fail() {
    unsafe { core::ptr::write_volatile(GPIO_PTR_FAIL, 1u8) };
}

fn report_success() {
    unsafe { core::ptr::write_volatile(GPIO_PTR_SUCCESS, 1u8) };
}

fn halt() -> ! {
    loop {
        riscv::asm::wfi();
    }
}

fn main() {
    report_fail();
}
