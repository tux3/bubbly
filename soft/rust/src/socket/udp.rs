use crate::ethernet_mmio::{
    eth_mmio_get_ip_dscp_ecn_src_ip, eth_mmio_tx_data, finish_ip_packet, start_ip_packet,
    RxIpHeader, IP_MTU,
};
use crate::log_msg_udp;
use crate::socket::*;
use crate::start_and_traps::{disable_interrupts, enable_interrupts};

pub struct UdpSocket<'b> {
    rx_buf: &'b mut [u8],
    rx_len: Option<usize>,

    src_ip: u32,
    dst_ip: u32,
    src_port: u16,
    dst_port: u16,

    peer_ip: u32,
    peer_port: u16,
}

impl<'b> UdpSocket<'b> {
    pub const IP_PROTO: u8 = 0x11;

    #[allow(dead_code)]
    pub fn new(rx_buf: &'b mut [u8], dst_ip: u32, dst_port: u16) -> Self {
        let src_ip = eth_mmio_get_ip_dscp_ecn_src_ip() as u32;
        Self::new_with_src(rx_buf, src_ip, 0, dst_ip, dst_port)
    }

    pub fn new_with_src_port(
        rx_buf: &'b mut [u8],
        src_port: u16,
        dst_ip: u32,
        dst_port: u16,
    ) -> Self {
        let src_ip = eth_mmio_get_ip_dscp_ecn_src_ip() as u32;
        Self::new_with_src(rx_buf, src_ip, src_port, dst_ip, dst_port)
    }

    pub fn new_with_src(
        rx_buf: &'b mut [u8],
        src_ip: u32,
        src_port: u16,
        dst_ip: u32,
        dst_port: u16,
    ) -> Self {
        Self {
            rx_buf,
            rx_len: None,
            src_ip,
            dst_ip,
            src_port,
            dst_port,
            peer_ip: 0,
            peer_port: 0,
        }
    }

    fn rx_len(&self) -> usize {
        self.rx_len.unwrap_or(0)
    }

    pub fn should_receive_packet(&mut self, header: &RxIpHeader, payload_start: &[u8]) -> bool {
        if header.proto() != Self::IP_PROTO
            || (header.dst_ip != self.src_ip && self.src_ip != 0)
            || (header.src_ip != self.dst_ip && self.dst_ip != 0xFFFF_FFFF && (self.dst_ip >> 8) != (224u32 << 16) )
            || (header.ip_payload_len() as usize) < 8 // UDP header
            || header.ip_payload_len() as usize - 8 > (self.rx_buf.len() - self.rx_len())
        {
            return false;
        }

        // OK to split because we checked ip hdr len (enforced by hardware)
        let (hdr_ports, _rest): (&[u8; 6], _) = payload_start.split_first_chunk().unwrap();
        let src_port = u16::from_be_bytes([hdr_ports[0], hdr_ports[1]]);
        let dst_port = u16::from_be_bytes([hdr_ports[2], hdr_ports[3]]);
        let udp_len = u16::from_be_bytes([hdr_ports[4], hdr_ports[5]]);

        if udp_len != header.ip_payload_len() {
            log_msg_udp("Received UDP message len doesn't match IP hdr len");
            return false;
        }

        if (src_port != self.dst_port && self.dst_port != 0) || dst_port != self.src_port {
            return false;
        }

        self.peer_ip = header.src_ip;
        self.peer_port = src_port;
        true
    }

    pub fn writable_rx_buf(&mut self) -> &mut [u8] {
        let l = self.rx_len();
        &mut self.rx_buf[l..]
    }

    pub fn add_written_count(&mut self, written: usize) {
        self.rx_len.replace(self.rx_len() + written);
    }
}

impl<'b> From<UdpSocket<'b>> for Socket<'b> {
    fn from(s: UdpSocket<'b>) -> Socket<'b> {
        Socket::Udp(s)
    }
}

impl ReadableSocket for UdpSocket<'_> {
    fn peek_recv_buf(&self) -> Option<&[u8]> {
        self.rx_len.map(|l| &self.rx_buf[..l])
    }

    fn clear_recv_buf(&mut self) {
        self.rx_len = None;
    }

    fn peer_ip(&self) -> u32 {
        self.peer_ip
    }

    fn peer_port(&self) -> u16 {
        self.peer_port
    }
}

fn send_udp_header_and_first_six_bytes(payload: &[u8], header_start: u64) {
    // 7 first bytes of UDP header
    eth_mmio_tx_data(header_start);
    // 1 last byte of header (ignored checksum), 6 bytes of payload
    let mut buf = [0, 0, 0, 0, 0, 0, 0, 7];
    unsafe { core::ptr::copy_nonoverlapping(payload.as_ptr(), buf.as_mut_ptr().add(1), 6) };
    eth_mmio_tx_data(u64::from_le_bytes(buf));
}

pub fn send_udp(mut payload: &[u8], dst_ip: u32, src_port: u16, dst_port: u16) {
    const UDP_DATAGRAM_MTU: usize = IP_MTU - 8;

    let prev_mie = disable_interrupts(); // Interrupt handlers may want to send packets

    let udp_header_start = (7u64 << 56)
        | (((8 + UDP_DATAGRAM_MTU as u16).swap_bytes() as u64) << 32)
        | ((dst_port.swap_bytes() as u64) << 16)
        | (src_port.swap_bytes() as u64);
    while payload.len() >= UDP_DATAGRAM_MTU {
        start_ip_packet(UDP_DATAGRAM_MTU + 8, dst_ip, UdpSocket::IP_PROTO);
        send_udp_header_and_first_six_bytes(payload, udp_header_start);
        finish_ip_packet(&payload[6..UDP_DATAGRAM_MTU]);
        payload = &payload[UDP_DATAGRAM_MTU..];
    }
    if !payload.is_empty() {
        let udp_header_last = (7u64 << 56)
            | (((8 + payload.len() as u16).swap_bytes() as u64) << 32)
            | ((dst_port.swap_bytes() as u64) << 16)
            | (src_port.swap_bytes() as u64);
        start_ip_packet(payload.len() + 8, dst_ip, UdpSocket::IP_PROTO);
        if payload.len() > 6 {
            send_udp_header_and_first_six_bytes(payload, udp_header_last);
            finish_ip_packet(&payload[6..]);
        } else {
            // 7 first bytes of UDP header
            eth_mmio_tx_data(udp_header_last);
            // 1 last byte of header (ignored checksum), remaining payload and last flag
            let last_tx_flag = 0b0100_0000u8;
            let tx_flags = last_tx_flag | (payload.len() as u8 + 1);
            let mut buf = [0, 0, 0, 0, 0, 0, 0, tx_flags];
            unsafe {
                core::ptr::copy_nonoverlapping(
                    payload.as_ptr(),
                    buf.as_mut_ptr().add(1),
                    payload.len(),
                )
            };
            eth_mmio_tx_data(u64::from_le_bytes(buf));
        }
    }

    if prev_mie {
        enable_interrupts();
    }
}
