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
use crate::socket::{ReadableSocket, Socket, UdpSocket};
use core::arch::asm;
use core::mem::transmute;
use riscv::register;
use riscv::register::mtvec::TrapMode;
use xxhash_rust::xxh64::xxh64;

const SRAM_BASE: usize = 0x08000000000;
const GPIO_BASE: usize = 0x20000000000;

const BOARD_MAC_ADDR: u64 = 0x00183e035117;
const RX_BUF_SIZE: usize = 16 * 1024;

fn set_led(on: bool) {
    let led_ptr = GPIO_BASE as *mut u8;
    unsafe {
        core::ptr::write_volatile(led_ptr, on as u8);
    }
}

unsafe fn copy_and_exec(payload: &[u8]) -> ! {
    // SAFETY: None of this is safe!
    unsafe {
        let dst_ptr = SRAM_BASE as *mut u8;
        core::ptr::copy_nonoverlapping(payload.as_ptr(), dst_ptr, payload.len());
        let dst_ptr = dst_ptr as *const ();
        let dst_fn: unsafe extern "C" fn() -> ! = transmute(dst_ptr);
        dst_fn();
    }
}

pub fn log_msg_udp(msg: impl AsRef<[u8]>) {
    send_udp(msg.as_ref(), 0xFFFF_FFFF, 0, 4444);
}

fn configure_dhcp<'b>() {
    let mut dhcp_rx_buf = [0u8; 500];
    let mut iface = MmioInterface::new();

    if let Ok(lease) = get_ethernet_dhcp_lease(&mut iface, &mut dhcp_rx_buf) {
        log_msg_udp("Received DHCP lease, configuring interface");
        eth_mmio_set_ip_dscp_ecn_src_ip(0, lease.ip);
        eth_mmio_set_gateway_ip_netmask(lease.router, lease.subnet_mask);
    } else {
        log_msg_udp("Failed to get DHCP lease, setting static IP");
        eth_mmio_set_ip_dscp_ecn_src_ip(0, u32::from_be_bytes([192, 168, 1, 110]));
        eth_mmio_set_gateway_ip_netmask(u32::from_be_bytes([192, 168, 1, 254]), 0xFF_FF_FF_00);
    }
}

fn handle_boot_request(sock: &mut dyn ReadableSocket) {
    let payload = sock.peek_recv_buf();
    if payload.len() < 3 + 8 {
        // If we get a datagram shorter than the header, this is 100% junk
        sock.clear_recv_buf();
        return;
    }

    let full_len =
        ((payload[2] as usize) << 16) | ((payload[1] as usize) << 8) | payload[0] as usize;

    if full_len + 8 + 3 > RX_BUF_SIZE {
        log_msg_udp("Boot payload longer than RX buffer! Discarding");
        sock.clear_recv_buf();
        return;
    }

    if payload.len() < 3 + 8 + full_len {
        // Don't clear recv buffer, and tell peer we're ready for more (our hardware rx buffer is smol)
        send_udp(
            &(payload.len() as u32).to_le_bytes(),
            sock.peer_ip(),
            0xB007,
            sock.peer_port(),
        );
        return;
    } else if payload.len() > 3 + 8 + full_len {
        log_msg_udp("Boot payload longer than header length");
        sock.clear_recv_buf();
        return;
    }

    let expected_hash = &payload[3..11];
    let payload_hash = xxh64(&payload[3 + 8..], 0).to_le_bytes();
    if expected_hash != payload_hash {
        log_msg_udp(b"Invalid boot payload hash");
        log_msg_udp(&expected_hash);
        log_msg_udp(&payload_hash);
        sock.clear_recv_buf();
    } else {
        log_msg_udp(b"Booting payload");
        let copy_and_exec_ptr = register::mscratch::read() as *const ();
        let copy_and_exec_fn: fn(&[u8]) -> ! = unsafe { transmute(copy_and_exec_ptr) };
        copy_and_exec_fn(&payload[3 + 8..]);
    }
}

fn main() -> ! {
    set_led(true);

    configure_dhcp();
    log_msg_udp(b"Rust server started");

    let mut rx_buf = [0u8; RX_BUF_SIZE];
    let mut iface = MmioInterface::<'_, 1>::new();
    let sock = UdpSocket::new_with_src_port(&mut rx_buf, 0xB007, 0xFFFF_FFFF, 0);
    let sock_token = iface.add_socket(Socket::Udp(sock));

    let mut led_enable = true;
    let mut last_mcycle = register::mcycle::read64();
    loop {
        if iface.poll() {
            handle_boot_request(iface.get_socket(&sock_token));
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
    unsafe {
        const STACK_PTR: usize = SRAM_BASE + 1024 * 32;
        asm!(
        "add sp, {sp}, 0",
        sp = in(reg) STACK_PTR,
        );

        if register::mscratch::read() == 0 {
            register::mscratch::write(copy_and_exec as usize);
        }
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
