use crate::socket::{ReadableSocket, Socket};
use crate::{
    eth_mmio_get_tx_src_mac, eth_mmio_rx_data, ip_discard_recv_packet, ip_finish_recv_packet,
    ip_start_recv_packet, log_msg_udp,
};
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

    pub fn add_socket(&mut self, sock: Socket<'s>) -> SocketToken {
        self.sockets.push(Some(sock));
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
            ip_discard_recv_packet();
            return false;
        }

        let local_mac = eth_mmio_get_tx_src_mac();
        if partial_read.header.dst_mac() != local_mac
            && partial_read.header.dst_mac() != 0xFFFF_FFFF_FFFF
        {
            log_msg_udp("Received packet for wrong MAC address, we are not a switch!");
            ip_discard_recv_packet();
            return false;
        }

        for sock in self.sockets.iter_mut() {
            let sock = match sock.as_mut() {
                None => continue,
                Some(s) => s,
            };
            match sock {
                Socket::Udp(s) => {
                    if s.should_receive_packet(
                        &partial_read.header,
                        &partial_read.read_buf[..partial_read.len_read],
                    ) {
                        let payload_len = (partial_read.header.ip_hdr_len() - 20 - 8) as usize;

                        // Skip UDP header (1 byte remaining unread, a partial read is 7 bytes)
                        // should_receive_packet checked that we have at least a complete header,
                        // so we don't need to check len != 0 or partial_read.complete here
                        partial_read.len_read = 0;
                        let data = eth_mmio_rx_data();
                        let complete = data >= 0xC000_0000_0000_0000;
                        let len = ((data >> 56) & 0b111) as usize - 1; // Skip last UDP header byte
                        let buf = s.writable_rx_buf();

                        // SAFETY: should_receive_packet checks it has enough room to receive
                        unsafe {
                            core::ptr::copy_nonoverlapping(
                                (&data as *const u64 as *const u8).add(1), // Skip last UDP header byte
                                buf.as_mut_ptr(),
                                len,
                            );

                            if !complete {
                                ip_finish_recv_packet(partial_read, &mut buf[len..]);
                            }
                        }
                        s.add_written_count(payload_len);
                        return true;
                    }
                }
            }
        }

        // No match
        ip_discard_recv_packet();
        false
    }
}
