use crate::{eth_mmio_get_ip_dscp_ecn_src_ip, log_msg_udp, RxIpHeader};

pub enum Socket<'b> {
    Udp(UdpSocket<'b>),
}

pub trait ReadableSocket {
    fn peek_recv_buf(&self) -> &[u8];
    fn clear_recv_buf(&mut self);
    fn peer_ip(&self) -> u32;
    fn peer_port(&self) -> u16;
}

impl ReadableSocket for Socket<'_> {
    fn peek_recv_buf(&self) -> &[u8] {
        match self {
            Socket::Udp(s) => s.peek_recv_buf(),
        }
    }

    fn clear_recv_buf(&mut self) {
        match self {
            Socket::Udp(s) => s.clear_recv_buf(),
        }
    }

    fn peer_ip(&self) -> u32 {
        match self {
            Socket::Udp(s) => s.peer_ip(),
        }
    }

    fn peer_port(&self) -> u16 {
        match self {
            Socket::Udp(s) => s.peer_port(),
        }
    }
}

pub struct UdpSocket<'b> {
    rx_buf: &'b mut [u8],
    rx_len: usize,

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
            rx_len: 0,
            src_ip,
            dst_ip,
            src_port,
            dst_port,
            peer_ip: 0,
            peer_port: 0,
        }
    }

    pub fn should_receive_packet(&mut self, header: &RxIpHeader, payload_start: &[u8]) -> bool {
        if (header.dst_ip != self.src_ip && self.src_ip != 0)
            || (header.src_ip != self.dst_ip && self.dst_ip != 0xFFFF_FFFF)
            || header.proto() != Self::IP_PROTO
            || header.ip_hdr_len() as usize - 20 < 8 // UDP header
            || header.ip_hdr_len() as usize - 20 - 8 > (self.rx_buf.len() - self.rx_len)
        {
            return false;
        }

        // OK to split because we checked ip hdr len (enforced by hardware)
        let (hdr_ports, _rest): (&[u8; 6], _) = payload_start.split_array_ref();
        let src_port = u16::from_be_bytes([hdr_ports[0], hdr_ports[1]]);
        let dst_port = u16::from_be_bytes([hdr_ports[2], hdr_ports[3]]);
        let udp_len = u16::from_be_bytes([hdr_ports[4], hdr_ports[5]]);

        if udp_len != header.ip_hdr_len() - 20 {
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
        &mut self.rx_buf[self.rx_len..]
    }

    pub fn add_written_count(&mut self, written: usize) {
        self.rx_len += written;
    }
}

impl ReadableSocket for UdpSocket<'_> {
    fn peek_recv_buf(&self) -> &[u8] {
        &self.rx_buf[..self.rx_len]
    }

    fn clear_recv_buf(&mut self) {
        self.rx_len = 0;
    }

    fn peer_ip(&self) -> u32 {
        self.peer_ip
    }

    fn peer_port(&self) -> u16 {
        self.peer_port
    }
}
