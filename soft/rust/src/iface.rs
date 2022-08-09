use crate::socket::{ReadableSocket, Socket};
use crate::{
    eth_mmio_get_tx_src_mac, ip_discard_recv_packet, ip_finish_recv_packet, ip_start_recv_packet,
    log_msg_udp, IcmpSocket, UdpSocket,
};
use core::any::TypeId;
use tinyvec::ArrayVec;

pub struct SocketToken {
    idx: usize,
}

pub struct MmioInterface<'b, const NSOCKS: usize = 4> {
    sockets: ArrayVec<[Option<Socket<'b>>; NSOCKS]>,
}

impl<'s, const NSOCKS: usize> MmioInterface<'s, NSOCKS> {
    pub fn new() -> Self {
        Self {
            sockets: Default::default(),
        }
    }

    pub fn add_socket(&mut self, sock: impl Into<Socket<'s>>) -> SocketToken {
        self.sockets.push(Some(sock.into()));
        SocketToken {
            idx: self.sockets.len() - 1,
        }
    }

    #[allow(dead_code)]
    pub fn sockets(&'s mut self) -> impl Iterator<Item = &mut dyn ReadableSocket> {
        self.sockets
            .iter_mut()
            .filter_map(|s| s.as_mut().map(|s| s as &mut dyn ReadableSocket))
    }

    pub fn get_socket(&mut self, token: &SocketToken) -> &mut dyn ReadableSocket {
        self.sockets[token.idx].as_mut().unwrap()
    }

    pub fn get_typed_socket<T: 'static>(&mut self, token: &SocketToken) -> &mut T {
        let ptr = match self.sockets[token.idx].as_mut().unwrap() {
            Socket::Udp(s) if TypeId::of::<UdpSocket>() == TypeId::of::<T>() => {
                s as *mut UdpSocket as *mut T
            }
            Socket::Icmp(s) if TypeId::of::<IcmpSocket>() == TypeId::of::<T>() => {
                s as *mut IcmpSocket as *mut T
            }
            _ => panic!("Invalid type for get_typed_socket"),
        };
        // SAFETY: We checked type IDs above
        unsafe { &mut *ptr as &mut T }
    }

    pub fn remove_socket(&mut self, token: SocketToken) {
        self.sockets[token.idx] = None;
    }

    // Returns true if at least one registered socket has received data
    // Note that if multiple sockets match a packet, we currently only return data to the first match
    // Guaranteed to receive no more than a single packet at a time (which keeps Socket::clear_recv_buf usable)
    pub fn poll(&mut self) -> bool {
        let mut partial_read = match ip_start_recv_packet() {
            None => return false,
            Some(r) => r,
        };
        if partial_read.header.is_fragmented() {
            log_msg_udp("Received fragmented IP packet, discarding");
            ip_discard_recv_packet(partial_read);
            return false;
        }

        let local_mac = eth_mmio_get_tx_src_mac();
        if partial_read.header.dst_mac() != local_mac
            && partial_read.header.dst_mac() != 0xFFFF_FFFF_FFFF
        {
            log_msg_udp("Received packet for wrong MAC address, we are not a switch!");
            ip_discard_recv_packet(partial_read);
            return false;
        }

        for sock in self.sockets.iter_mut() {
            let sock = match sock.as_mut() {
                None => continue,
                Some(s) => s,
            };
            match sock {
                Socket::Icmp(s) => {
                    if s.should_receive_packet(
                        &partial_read.header,
                        &partial_read.read_buf[..partial_read.len_read],
                    ) {
                        let payload_len = (partial_read.header.ip_payload_len() - 8) as usize;

                        // Skip ICMP header (8 bytes)
                        // should_receive_packet checked that we have at least a complete header,
                        // so we don't need to check len >= 8
                        partial_read
                            .read_buf
                            .copy_within(8..partial_read.len_read, 0);
                        partial_read.len_read -= 8;

                        // SAFETY: should_receive_packet checks it has enough room to receive
                        unsafe { ip_finish_recv_packet(partial_read, s.writable_rx_buf()) };
                        s.add_written_count(payload_len);
                        return true;
                    }
                }
                Socket::Udp(s) => {
                    if s.should_receive_packet(
                        &partial_read.header,
                        &partial_read.read_buf[..partial_read.len_read],
                    ) {
                        let payload_len = (partial_read.header.ip_payload_len() - 8) as usize;

                        // Skip UDP header (8 bytes)
                        // should_receive_packet checked that we have at least a complete header,
                        // so we don't need to check len >= 8
                        partial_read
                            .read_buf
                            .copy_within(8..partial_read.len_read, 0);
                        partial_read.len_read -= 8;

                        // SAFETY: should_receive_packet checks it has enough room to receive
                        unsafe { ip_finish_recv_packet(partial_read, s.writable_rx_buf()) };
                        s.add_written_count(payload_len);
                        return true;
                    }
                }
            }
        }

        // No match
        ip_discard_recv_packet(partial_read);
        false
    }
}
