#![no_std]
#![no_main]
#![feature(const_mut_refs)]
#![feature(split_array)]
#![feature(panic_info_message)]
#![warn(unsafe_op_in_unsafe_fn)]

mod ethernet_mmio;
use crate::ethernet_mmio::*;
mod dhcp;
mod iface;
mod socket;

use crate::dhcp::get_ethernet_dhcp_lease;
use crate::iface::MmioInterface;
use crate::socket::{Socket, UdpSocket};
use core::arch::asm;
use core::mem::transmute;
use riscv::register;
use riscv::register::mtvec::TrapMode;

const SRAM_BASE: usize = 0x08000000000;
const GPIO_BASE: usize = 0x20000000000;

const BOARD_MAC_ADDR: u64 = 0x00183e035117;
const RX_BUF_SIZE: usize = 1500;

fn set_led(on: bool) {
    let led_ptr = GPIO_BASE as *mut u8;
    unsafe {
        core::ptr::write_volatile(led_ptr, on as u8);
    }
}

unsafe fn copy_and_exec(payload: &[u8]) -> ! {
    // SAFETY: None of this is safe!
    unsafe {
        let dst_ptr = (SRAM_BASE + 4096) as *mut u8;
        core::ptr::copy_nonoverlapping(payload.as_ptr(), dst_ptr, payload.len());
        let dst_ptr = dst_ptr as *const ();
        let dst_fn: unsafe extern "C" fn() -> ! = transmute(dst_ptr);
        dst_fn();
    }
}

pub fn log_msg_udp(msg: impl AsRef<[u8]>) {
    send_udp(msg.as_ref(), 0xFFFF_FFFF, 0, 4444);
}

fn configure_dhcp<'b>(rx_buf: &'b mut [u8], iface: &mut MmioInterface<'b>) {
    if let Ok(lease) = get_ethernet_dhcp_lease(iface, rx_buf) {
        log_msg_udp("Received DHCP lease, configuring interface");
        eth_mmio_set_ip_dscp_ecn_src_ip(0, lease.ip);
        eth_mmio_set_gateway_ip_netmask(lease.router, lease.subnet_mask);
    } else {
        log_msg_udp("Failed to get DHCP lease, setting static IP");
        eth_mmio_set_ip_dscp_ecn_src_ip(0, u32::from_be_bytes([192, 168, 1, 110]));
        eth_mmio_set_gateway_ip_netmask(u32::from_be_bytes([192, 168, 1, 254]), 0xFF_FF_FF_00);
    }
}

fn main() -> ! {
    set_led(true);

    let rx_buf = &mut [0u8; RX_BUF_SIZE];
    let mut iface = MmioInterface::new();
    configure_dhcp(rx_buf, &mut iface);
    log_msg_udp(b"Rust server started");

    let mut led_enable = true;
    let mut last_mcycle = register::mcycle::read64();
    loop {
        if let Some(frame) = ip_recv_packet(rx_buf) {
            send_ip_packet(frame.payload, frame.header.src_ip, frame.header.proto());
        }

        let mcycle = register::mcycle::read64();
        if mcycle - last_mcycle > 15_000_000 {
            last_mcycle = mcycle;
            led_enable = !led_enable;
            set_led(led_enable);
        }
    }
}

#[link_section = ".start"]
#[no_mangle]
unsafe extern "C" fn _start() -> ! {
    unsafe {
        const STACK_PTR: usize = SRAM_BASE + 4096 - 8;
        asm!(
        "add sp, {sp}, 0",
        sp = in(reg) STACK_PTR,
        );

        register::mscratch::write(copy_and_exec as usize);
        register::mtvec::write(panic as usize, TrapMode::Direct);
    }

    eth_mmio_set_tx_src_mac(BOARD_MAC_ADDR);

    main()
}

#[panic_handler]
unsafe fn panic(panic: &core::panic::PanicInfo<'_>) -> ! {
    let panic_led = (GPIO_BASE + 2) as *mut u8;
    unsafe { *panic_led = 1 };

    if let Some(fmt_args) = panic.message() {
        if let Some(msg) = fmt_args.as_str() {
            log_msg_udp(b"RUST SERVER PANIC:\n");
            log_msg_udp(msg.as_bytes());
        } else {
            log_msg_udp(b"RUST SERVER PANIC");
        }
    }
    loop {}
}
