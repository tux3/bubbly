mod udp;
pub use udp::*;
mod icmp;
pub use icmp::*;

pub enum Socket<'b> {
    Udp(UdpSocket<'b>),
    Icmp(IcmpSocket<'b>),
}

pub trait ReadableSocket {
    /// Returns None if nothing was received since the last call to clear_recv_buf
    fn peek_recv_buf(&self) -> Option<&[u8]>;
    fn clear_recv_buf(&mut self);
    fn peer_ip(&self) -> u32;
    fn peer_port(&self) -> u16;
}

impl ReadableSocket for Socket<'_> {
    fn peek_recv_buf(&self) -> Option<&[u8]> {
        match self {
            Socket::Udp(s) => s.peek_recv_buf(),
            Socket::Icmp(s) => s.peek_recv_buf(),
        }
    }

    fn clear_recv_buf(&mut self) {
        match self {
            Socket::Udp(s) => s.clear_recv_buf(),
            Socket::Icmp(s) => s.clear_recv_buf(),
        }
    }

    fn peer_ip(&self) -> u32 {
        match self {
            Socket::Udp(s) => s.peer_ip(),
            Socket::Icmp(s) => s.peer_ip(),
        }
    }

    fn peer_port(&self) -> u16 {
        match self {
            Socket::Udp(s) => s.peer_port(),
            Socket::Icmp(s) => s.peer_port(),
        }
    }
}
