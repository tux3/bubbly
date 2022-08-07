#![no_std]
#![no_main]
#![feature(const_mut_refs)]

mod ethernet_mmio;
use crate::ethernet_mmio::*;

use core::arch::asm;
use core::mem::transmute;
use riscv::register;
use riscv::register::mtvec::TrapMode;

const SRAM_BASE: usize = 0x08000000000;
const GPIO_BASE: usize = 0x20000000000;

const BOARD_MAC_ADDR: u64 = 0x00183e035117;
const ETH_FRAME_BUF_SIZE: usize = 1520; // Leave extra space for 64bit writes

fn set_led(on: bool) {
    let led_ptr = GPIO_BASE as *mut u8;
    unsafe {
        core::ptr::write_volatile(led_ptr, on as u8);
    }
}

unsafe fn copy_and_exec(payload: &[u8]) -> ! {
    let dst_ptr = (SRAM_BASE + 4096) as *mut u8;
    core::ptr::copy_nonoverlapping(payload.as_ptr(), dst_ptr, payload.len());
    let dst_ptr = dst_ptr as *const ();
    let dst_fn: unsafe extern "C" fn() -> ! = transmute(dst_ptr);
    dst_fn();
}

unsafe fn main() -> ! {
    set_led(true);

    let eth_frame_buf: &mut [u8; ETH_FRAME_BUF_SIZE] = &mut *(SRAM_BASE as *mut _);

    let mut start_msg_sent = false;
    let mut led_enable = true;
    let mut last_mcycle = register::mcycle::read64();
    loop {
        if let Some(frame) = ip_recv_packet(eth_frame_buf) {
            send_ip_packet(frame.payload, frame.src_ip, frame.proto());
        }

        let mcycle = register::mcycle::read64();
        if mcycle - last_mcycle > 15_000_000 {
            last_mcycle = mcycle;
            led_enable = !led_enable;
            set_led(led_enable);
        }

        if !start_msg_sent && mcycle > 150_000_000 {
            // The eth interface takes a WHILE to be ready, so we delay the hello message
            start_msg_sent = true;
            send_udp(b"Rust server started", 0xFFFF_FFFF, 0, 4444);
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

    register::mscratch::write(copy_and_exec as usize);
    register::mtvec::write(panic as usize, TrapMode::Direct);

    eth_mmio_set_tx_src_mac(BOARD_MAC_ADDR);
    eth_mmio_set_ip_dscp_ecn_src_ip(0, u32::from_be_bytes([192, 168, 1, 110]));
    eth_mmio_set_gateway_ip_netmask(u32::from_be_bytes([192, 168, 1, 254]), 0xFF_FF_FF_00);

    main()
}

#[panic_handler]
unsafe fn panic(_panic: &core::panic::PanicInfo<'_>) -> ! {
    let panic_led = (GPIO_BASE + 2) as *mut u8;
    *panic_led = 1;
    loop {}
}
