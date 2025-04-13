#![no_std]
#![no_main]
#![feature(split_array)]
#![feature(naked_functions)]
#![feature(concat_bytes)]
#![feature(let_chains)]
#![warn(unsafe_op_in_unsafe_fn)]
#![allow(clippy::unusual_byte_groupings)]

mod dhcp;
mod ethernet_mmio;
mod iface;
mod leds;
mod mdns;
mod mtime;
mod netboot;
mod ping;
mod socket;
mod start_and_traps;

const SRAM_BASE: usize = 0x08000000000;
const PLATFORM_BASE: usize = 0x20000000000;

const SRAM_SIZE: usize = 32 * 1024;
const RX_BUF_SIZE: usize = 12 * 1024;

pub fn log_msg_udp(msg: impl AsRef<[u8]>) {
    socket::send_udp(msg.as_ref(), 0xFFFF_FFFF, 0, 4444);
}

fn main() -> ! {
    use crate::mdns::{MDNS_IP, MDNS_PORT};
    use crate::socket::{IcmpSocket, UdpSocket};

    leds::set_led(leds::LED::Led0, true);

    dhcp::configure_dhcp();
    log_msg_udp(b"Rust server started");

    let rx_buf = &mut [0u8; RX_BUF_SIZE];
    let rx_ping = &mut [0u8; 128]; // We don't have tons of RAM, just drop huge pings
    let rx_mdns = &mut [0u8; 128];
    let mut iface = iface::MmioInterface::<'_, 3>::new();
    let boot_sock = UdpSocket::new_with_src_port(rx_buf, 0xB007, 0xFFFF_FFFF, 0);
    let boot_sock_token = iface.add_socket(boot_sock);
    let mdns_sock = UdpSocket::new_with_src(rx_mdns, MDNS_IP, MDNS_PORT, 0xFFFF_FFFF, MDNS_PORT);
    let mdns_sock_token = iface.add_socket(mdns_sock);
    let icmp_sock_token = iface.add_socket(IcmpSocket::new(rx_ping));

    loop {
        if iface.poll_wait() {
            netboot::handle_boot_request(iface.get_socket(&boot_sock_token));
            mdns::handle_request(iface.get_socket(&mdns_sock_token));
            ping::handle_ping(iface.get_typed_socket(&icmp_sock_token));
        }
    }
}
