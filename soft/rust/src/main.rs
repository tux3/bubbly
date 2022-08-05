#![no_std]
#![no_main]
#![feature(const_mut_refs)]

mod ethernet_mmio;
use crate::ethernet_mmio::*;

use core::arch::asm;
use core::mem::transmute;
use riscv::register;
use riscv::register::mtvec::TrapMode;
use xxhash_rust::xxh64::xxh64;

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
    //eth_send_frame(b"Rust server started", 0xffff_ffff_ffff, 0x0);

    let eth_frame_buf: &mut [u8; ETH_FRAME_BUF_SIZE] = &mut *(SRAM_BASE as *mut _);

    let mut led_enable = true;
    let mut last_mcycle = register::mcycle::read64();
    loop {
        if let Some(frame) = eth_recv_frame(eth_frame_buf) {
            if frame.ethertype() == 0xB007 {
                // "BOOT" ethertype
                let expected_hash = frame.dst_mac().to_le_bytes();
                let payload_hash = xxh64(frame.payload, 0).to_le_bytes();
                if expected_hash[..6] != payload_hash[..6] {
                    eth_send_frame(
                        b"Invalid boot payload hash",
                        frame.src_mac,
                        frame.ethertype(),
                    );
                    eth_send_frame(&expected_hash[..6], frame.src_mac, frame.ethertype());
                } else {
                    eth_send_frame(b"Booting payload", frame.src_mac, frame.ethertype());
                    let copy_and_exec_ptr = register::mscratch::read() as *const ();
                    let copy_and_exec_fn: fn(&[u8]) -> ! = transmute(copy_and_exec_ptr);
                    copy_and_exec_fn(frame.payload);
                }
            } else {
                eth_send_frame(frame.payload, frame.src_mac, frame.ethertype());
            }
        }

        let mcycle = register::mcycle::read64();
        if mcycle - last_mcycle > 30_000_000 {
            last_mcycle = mcycle;
            led_enable = !led_enable;
            set_led(led_enable);
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
    eth_mmio_set_src_ip_gateway_ip(
        u32::from_be_bytes([192, 168, 1, 110]),
        u32::from_be_bytes([192, 168, 1, 254]),
    );
    eth_mmio_set_netmask(0xFF_FF_FF_00);

    main()
}

#[panic_handler]
unsafe fn panic(_panic: &core::panic::PanicInfo<'_>) -> ! {
    let panic_led = (GPIO_BASE + 2) as *mut u8;
    *panic_led = 1;
    loop {}
}
