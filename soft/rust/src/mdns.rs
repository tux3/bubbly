use crate::ethernet_mmio::eth_mmio_get_ip_dscp_ecn_src_ip;
use crate::{log_msg_udp, send_udp, ReadableSocket};

macro_rules! LOCAL_DOMAIN {
    () => {
        b"\x06bubbly\x05local\x00"
    };
}
pub const MDNS_IP: u32 = u32::from_be_bytes([224, 0, 0, 251]);
pub const MDNS_PORT: u16 = 5353;

pub fn handle_request(sock: &mut dyn ReadableSocket) {
    let payload = match sock.peek_recv_buf() {
        None => return,
        Some(p) => p,
    };
    if payload.len() < 12 {
        sock.clear_recv_buf();
        return;
    }
    let (hdr, mut qdata): (&[u8; 12], _) = payload.split_array_ref();
    let ident = u16::from_be_bytes([hdr[0], hdr[1]]);
    let flags = u16::from_be_bytes([hdr[2], hdr[3]]);
    // Ignore recursion desired and reserved fields
    if flags & 0b1_1111_1_1_0_1_000_1111 != 0 {
        sock.clear_recv_buf();
        return;
    }

    let mut num_questions = u16::from_be_bytes([hdr[4], hdr[5]]);
    let num_anwsers = u16::from_be_bytes([hdr[6], hdr[7]]);
    let num_auth_rr = u16::from_be_bytes([hdr[8], hdr[9]]);
    let num_additional_rr = u16::from_be_bytes([hdr[10], hdr[11]]);
    if num_anwsers != 0 || num_auth_rr != 0 {
        sock.clear_recv_buf();
        return;
    }

    let mut can_answer = false;
    let mut should_qu = false;
    'parse: while !qdata.is_empty() && num_questions > 0 {
        if qdata.len() < LOCAL_DOMAIN!().len() + 2 + 2 {
            break;
        }
        if qdata.starts_with(LOCAL_DOMAIN!()) {
            qdata = &qdata[LOCAL_DOMAIN!().len()..];
            let qtype = u16::from_be_bytes([qdata[0], qdata[1]]);
            let qclass = u16::from_be_bytes([qdata[2], qdata[3]]) & 0x7F_FF;
            should_qu = qdata[2] & 0x80 == 0x80;
            qdata = &qdata[4..];
            if (qtype == 1 || qtype == 255) && (qclass == 1 || qclass == 255) {
                can_answer = true;
                break; // No need to parse other answers..
            }
        } else {
            // Skip question
            loop {
                let label_len = qdata[0] as usize;
                if label_len >= 0xC0 {
                    log_msg_udp("mDNS name compression not supported");
                    break 'parse;
                }
                if qdata.len() < label_len + 1 + 2 + 2 {
                    log_msg_udp("Invalid mDNS question record len!");
                    break 'parse;
                }
                if label_len == 0 {
                    qdata = &qdata[1 + 4..]; // Skip qtype/class fields
                    break;
                }
                qdata = &qdata[1 + label_len..];
            }
        }

        num_questions -= 1;
    }
    if num_questions == 0 && num_additional_rr == 0 && !qdata.is_empty() {
        log_msg_udp("Unexpected trialing data in mDNS query");
    }

    if can_answer {
        let dst_ip = if should_qu { sock.peer_ip() } else { MDNS_IP };
        send_mdns_response(dst_ip, ident);
    }

    sock.clear_recv_buf();
}

fn send_mdns_response(dst_ip: u32, ident: u16) {
    let ident = ident.to_be_bytes();
    #[rustfmt::skip]
    let mut buf: [u8; 40] = *concat_bytes!([
            0, 0, // Ident (placeholder, because concat_bytes is const)
            0x84, 0x00, // Standard authoritative reply flags
            0x00, 0x00, // Num questions
            0x00, 0x01, // Num answers
            0x00, 0x00, // Num auth rr
            0x00, 0x00, // Num additional rr
        ],
        LOCAL_DOMAIN!(),
        [
            0x00, 0x01, // RTYPE
            0x80, 0x01, // CACHE-FLUSH/RRTYPE
            0x00, 0x00, 0x0e, 0x10, // TTL (3600s)
            0x00, 0x04, // RDATA LEN
            0x00, 0x00, 0x00, 0x00 // RDATA (placeholder, because concat_bytes is const)
        ]
    );
    buf[0] = ident[0];
    buf[1] = ident[1];
    let self_ip = (eth_mmio_get_ip_dscp_ecn_src_ip() as u32).to_be_bytes();
    buf[buf.len() - 4] = self_ip[0];
    buf[buf.len() - 3] = self_ip[1];
    buf[buf.len() - 2] = self_ip[2];
    buf[buf.len() - 1] = self_ip[3];

    send_udp(&buf, dst_ip, 5353, 5353);
}
