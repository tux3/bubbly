use crate::socket::send_pong;
use crate::{log_msg_udp, IcmpSocket, IcmpType, ReadableSocket};

pub fn handle_ping(sock: &mut IcmpSocket) {
    let payload = match sock.peek_recv_buf() {
        None => return,
        Some(p) => p,
    };
    if sock.icmp_type() != IcmpType::EchoRequest as u8 {
        sock.clear_recv_buf();
        return;
    }

    if !sock.checksum_valid() {
        log_msg_udp("Received ping with invalid checksum!");
        sock.clear_recv_buf();
        return;
    }

    send_pong(sock.peer_ip(), sock.identifier(), sock.seq_num(), payload);
    sock.clear_recv_buf();
}
