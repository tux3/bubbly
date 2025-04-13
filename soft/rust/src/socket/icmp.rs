use crate::ethernet_mmio::{send_ip_packet, RxIpHeader, IP_MTU};
use crate::log_msg_udp;
use crate::socket::{ReadableSocket, Socket};

#[derive(Copy, Clone, Eq, PartialEq)]
#[repr(u8)]
pub enum IcmpType {
    EchoReply = 0,
    EchoRequest = 8,
}

pub struct IcmpSocket<'b> {
    rx_buf: &'b mut [u8],
    rx_len: Option<usize>,

    // These are the last receive packet's properties
    // Since our iface only receives one IP packet at a time when polled, you will see each
    icmp_type: u8,
    icmp_code: u8,
    checksum: u16,
    identifier: u16,
    seq_num: u16,

    peer_ip: u32,
}

impl<'b> IcmpSocket<'b> {
    pub const IP_PROTO: u8 = 0x1;

    pub fn new(rx_buf: &'b mut [u8]) -> Self {
        Self {
            rx_buf,
            rx_len: None,
            icmp_type: 0,
            icmp_code: 0,
            checksum: 0,
            identifier: 0,
            seq_num: 0,
            peer_ip: 0,
        }
    }

    fn rx_len(&self) -> usize {
        self.rx_len.unwrap_or(0)
    }

    pub fn should_receive_packet(&mut self, header: &RxIpHeader, payload_start: &[u8]) -> bool {
        if header.proto() != Self::IP_PROTO
            || (header.ip_payload_len() as usize) < 8 // ICMP header
            || header.ip_payload_len() as usize - 8 > (self.rx_buf.len() - self.rx_len())
        {
            return false;
        }

        // OK to split because we checked ip hdr len (enforced by hardware)
        let (hdr_data, _rest): (&[u8; 8], _) = payload_start.split_first_chunk().unwrap();
        let icmp_type = hdr_data[0];
        let icmp_code = hdr_data[1];
        let checksum = u16::from_be_bytes([hdr_data[2], hdr_data[3]]);
        let identifier = u16::from_be_bytes([hdr_data[4], hdr_data[5]]);
        let seq_num = u16::from_be_bytes([hdr_data[6], hdr_data[7]]);

        if icmp_type == IcmpType::EchoReply as u8 || icmp_type == IcmpType::EchoRequest as u8 {
            if icmp_code != 0 {
                log_msg_udp("Invalid ICMP echo with non-zero subtype code");
                return false;
            }
        } else {
            // Not handled for now
            return false;
        }

        self.peer_ip = header.src_ip;
        self.icmp_type = icmp_type;
        self.icmp_code = icmp_code;
        self.checksum = checksum;
        self.identifier = identifier;
        self.seq_num = seq_num;

        true
    }

    pub fn writable_rx_buf(&mut self) -> &mut [u8] {
        let l = self.rx_len();
        &mut self.rx_buf[l..]
    }

    pub fn add_written_count(&mut self, written: usize) {
        self.rx_len.replace(self.rx_len() + written);
    }

    pub fn checksum_valid(&self) -> bool {
        self.checksum
            == compute_checksum(
                self.icmp_type,
                self.icmp_code,
                self.identifier,
                self.seq_num,
                (self as &dyn ReadableSocket).peek_recv_buf().unwrap(),
            )
    }

    pub fn icmp_type(&self) -> u8 {
        self.icmp_type
    }

    pub fn identifier(&self) -> u16 {
        self.identifier
    }

    pub fn seq_num(&self) -> u16 {
        self.seq_num
    }
}

impl<'b> From<IcmpSocket<'b>> for Socket<'b> {
    fn from(s: IcmpSocket<'b>) -> Socket<'b> {
        Socket::Icmp(s)
    }
}

impl ReadableSocket for IcmpSocket<'_> {
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
        0
    }
}

pub fn compute_checksum(
    icmp_type: u8,
    icmp_code: u8,
    identifier: u16,
    seq_num: u16,
    mut data: &[u8],
) -> u16 {
    let type_code = ((icmp_type as u32) << 8) | icmp_code as u32;
    let mut sum = type_code + identifier as u32 + seq_num as u32;
    while data.len() >= 2 {
        sum += u16::from_be_bytes([data[0], data[1]]) as u32;
        data = &data[2..];
    }
    if !data.is_empty() {
        sum += u16::from_be_bytes([data[0], 0]) as u32;
    }
    !(sum as u16 + (sum >> 16) as u16)
}

fn send_icmp_echo(kind: IcmpType, identifier: u16, seq_num: u16, dst_ip: u32, payload: &[u8]) {
    const MAX_TX_DATA_LEN: usize = IP_MTU - 8;
    assert!(payload.len() <= MAX_TX_DATA_LEN);

    let checksum = compute_checksum(kind as u8, 0, identifier, seq_num, payload).to_be_bytes();
    let identifier = identifier.to_be_bytes();
    let seq_num = seq_num.to_be_bytes();

    let mut buf = [0u8; IP_MTU];
    #[rustfmt::skip]
    buf[0..8].copy_from_slice(&[
        kind as u8, 0,
        checksum[0], checksum[1],
        identifier[0], identifier[1],
        seq_num[0], seq_num[1],
    ]);
    buf[8..payload.len() + 8].copy_from_slice(payload);
    send_ip_packet(&buf[..payload.len() + 8], dst_ip, IcmpSocket::IP_PROTO);
}

#[allow(dead_code)]
pub fn send_ping(dst_ip: u32, identifier: u16, seq_num: u16, payload: &[u8]) {
    send_icmp_echo(IcmpType::EchoRequest, identifier, seq_num, dst_ip, payload);
}

#[allow(dead_code)]
pub fn send_pong(dst_ip: u32, identifier: u16, seq_num: u16, payload: &[u8]) {
    send_icmp_echo(IcmpType::EchoReply, identifier, seq_num, dst_ip, payload);
}
