#![no_std]
#![no_main]
#![feature(const_mut_refs)]

mod ethernet_mmio;
use crate::ethernet_mmio::*;

use core::arch::asm;
use riscv::register;
use riscv::register::mtvec::TrapMode;

const SRAM_BASE: usize = 0x08000000000;
const GPIO_BASE: usize = 0x20000000000;

const BOARD_MAC_ADDR: u64 = 0x00183e035117;
const ETH_FRAME_BUF_SIZE: usize = 1520; // Leave extra space for 64bit writes

fn set_led(on: bool) {
    let led_ptr = GPIO_BASE as *mut u8;
    unsafe { core::ptr::write_volatile(led_ptr, on as u8); }
}

unsafe fn main() -> ! {
    set_led(true);

    let eth_frame_buf: &mut [u8; ETH_FRAME_BUF_SIZE] = &mut *(SRAM_BASE as *mut _);

    let mut led_enable = true;
    let mut last_mcycle = register::mcycle::read64();
    loop {
        if let Some(frame) = eth_recv_frame(eth_frame_buf) {
            eth_send_frame(frame.payload, frame.src_mac, frame.ethertype());
        }

        let mcycle = register::mcycle::read64();
        if mcycle - last_mcycle > 15_000_000 {
            last_mcycle = mcycle;
            led_enable = !led_enable;
            set_led(led_enable);

            let tmp_data = &[0u8, 1u8, 2u8, 3u8, 4u8, 5u8, 6u8, 7u8, 8u8, 9u8, 10u8];
            eth_send_frame(tmp_data, 0xffff_ffff_ffff, 0x0);
        }
    }
}

#[link_section = ".start"]
#[no_mangle]
unsafe extern "C" fn _start() -> ! {
    const STACK_PTR: usize = SRAM_BASE + 4096 - 8;
    asm!(
    "add sp, {sp}, 0",
    sp = in(reg) STACK_PTR,
    );

    register::mtvec::write(panic as usize, TrapMode::Direct);

    eth_mmio_set_tx_src_mac(BOARD_MAC_ADDR);

    main()
}

#[panic_handler]
unsafe fn panic(_panic: &core::panic::PanicInfo<'_>) -> ! {
    let panic_led = (GPIO_BASE + 2) as *mut u8;
    *panic_led = 1;
    loop {}
}
