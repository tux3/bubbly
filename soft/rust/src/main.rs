#![no_std]
#![no_main]
#![feature(split_array)]
#![feature(panic_info_message)]
#![feature(naked_functions)]
#![feature(asm_const)]
#![warn(unsafe_op_in_unsafe_fn)]

mod dhcp;
mod ethernet_mmio;
mod iface;
mod netboot;
mod ping;
mod socket;
mod start_and_fault_vectors;

use crate::iface::MmioInterface;
use crate::ping::handle_ping;
use crate::socket::{send_udp, IcmpSocket, IcmpType, ReadableSocket, UdpSocket};
use riscv::register;

const SRAM_BASE: usize = 0x08000000000;
const GPIO_BASE: usize = 0x20000000000;

const SRAM_SIZE: usize = 32 * 1024;
const RX_BUF_SIZE: usize = 12 * 1024;
const CODE_FREE_SPACE: usize = SRAM_SIZE - RX_BUF_SIZE - 1024; // Leave some stack space..

fn set_led(on: bool) {
    let led_ptr = GPIO_BASE as *mut u8;
    unsafe {
        core::ptr::write_volatile(led_ptr, on as u8);
    }
}

pub fn log_msg_udp(msg: impl AsRef<[u8]>) {
    send_udp(msg.as_ref(), 0xFFFF_FFFF, 0, 4444);
}

fn main() -> ! {
    set_led(true);

    dhcp::configure_dhcp();
    log_msg_udp(b"Rust server started");

    let mut rx_buf = [0u8; RX_BUF_SIZE];
    let mut rx_ping_buf = [0u8; 128]; // We don't have tons of RAM, can drop huge pings
    let mut iface = MmioInterface::<'_, 2>::new();
    let boot_sock = UdpSocket::new_with_src_port(&mut rx_buf, 0xB007, 0xFFFF_FFFF, 0);
    let boot_sock_token = iface.add_socket(boot_sock);
    let icmp_sock_token = iface.add_socket(IcmpSocket::new(&mut rx_ping_buf));

    let mut led_enable = true;
    let mut last_mcycle = register::mcycle::read64();
    loop {
        if iface.poll() {
            netboot::handle_boot_request(iface.get_socket(&boot_sock_token));
            handle_ping(iface.get_typed_socket(&icmp_sock_token));
        }

        let mcycle = register::mcycle::read64();
        if mcycle - last_mcycle > 15_000_000 {
            last_mcycle = mcycle;
            led_enable = !led_enable;
            set_led(led_enable);
        }
    }
}
