#![no_std]
#![no_main]
#![feature(split_array)]
#![feature(panic_info_message)]
#![warn(unsafe_op_in_unsafe_fn)]

mod ethernet_mmio;
use crate::ethernet_mmio::*;
mod dhcp;
mod iface;
mod netboot;
mod socket;

use crate::iface::MmioInterface;
use crate::socket::{ReadableSocket, Socket, UdpSocket};
use riscv::register::{self, mtvec::TrapMode};

const SRAM_BASE: usize = 0x08000000000;
const GPIO_BASE: usize = 0x20000000000;

const BOARD_MAC_ADDR: u64 = 0x00183e035117;
const SRAM_SIZE: usize = 32 * 1024;
const RX_BUF_SIZE: usize = 12 * 1024;
const CODE_FREE_SPACE: usize = SRAM_SIZE - RX_BUF_SIZE;

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
    let mut iface = MmioInterface::<'_, 1>::new();
    let sock = UdpSocket::new_with_src_port(&mut rx_buf, 0xB007, 0xFFFF_FFFF, 0);
    let sock_token = iface.add_socket(Socket::Udp(sock));

    let mut led_enable = true;
    let mut last_mcycle = register::mcycle::read64();
    loop {
        if iface.poll() {
            netboot::handle_boot_request(iface.get_socket(&sock_token));
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
unsafe extern "C" fn start() -> ! {
    unsafe {
        const STACK_PTR: usize = SRAM_BASE + SRAM_SIZE;
        core::arch::asm!(
        "add sp, {sp}, 0",
        sp = in(reg) STACK_PTR,
        );

        if register::mscratch::read() == 0 {
            register::mscratch::write(netboot::unzip_and_exec as usize);
        }
        register::mtvec::write(panic as usize, TrapMode::Direct);
    }

    eth_mmio_set_tx_src_mac(BOARD_MAC_ADDR);

    main()
}

#[panic_handler]
unsafe fn panic(panic: &core::panic::PanicInfo<'_>) -> ! {
    let panic_led = (GPIO_BASE + 2) as *mut u8;
    unsafe { core::ptr::write_volatile(panic_led, 1) };

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
