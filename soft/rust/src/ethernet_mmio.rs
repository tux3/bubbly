const ETHERNET_MMIO_BASE: usize = 0x30000000000;
pub const ETH_MTU: usize = 1500;
pub const IP_MTU: usize = ETH_MTU - 20;
const MMIO_TX_SRC_MAC: *mut u64 = ETHERNET_MMIO_BASE as _;
const MMIO_IP_TTL_PROTO_LEN_DST_IP: *mut u64 = (ETHERNET_MMIO_BASE + 0x8) as _;
const MMIO_TX_DATA: *mut u64 = (ETHERNET_MMIO_BASE + 0x10) as _;
const MMIO_RX_SRC_MAC: *mut u64 = (ETHERNET_MMIO_BASE + 0x18) as _;
const MMIO_RX_DST_MAC_TYPE: *mut u64 = (ETHERNET_MMIO_BASE + 0x20) as _;
const MMIO_RX_DATA: *mut u64 = (ETHERNET_MMIO_BASE + 0x28) as _;
const MMIO_IP_DSCP_ECN_SRC_IP: *mut u64 = (ETHERNET_MMIO_BASE + 0x30) as _;
const MMIO_GATEWAY_IP_NETMASK: *mut u64 = (ETHERNET_MMIO_BASE + 0x38) as _;
const MMIO_RX_SRC_IP_DST_IP: *mut u64 = (ETHERNET_MMIO_BASE + 0x40) as _;
const MMIO_RX_TTL_PROTO_ID_LEN_FRAG: *mut u64 = (ETHERNET_MMIO_BASE + 0x48) as _;
const MMIO_RX_DSCP_ECN_VER_IHL_CHKSUM: *mut u64 = (ETHERNET_MMIO_BASE + 0x50) as _;

pub fn eth_mmio_set_tx_src_mac(mac: u64) {
    unsafe {
        core::ptr::write_volatile(MMIO_TX_SRC_MAC, mac);
    }
}

pub fn eth_mmio_get_tx_src_mac() -> u64 {
    unsafe { core::ptr::read_volatile(MMIO_TX_SRC_MAC) }
}

pub fn eth_mmio_set_tx_ttl_proto_len_dst_ip(ttl: u8, proto: u8, len: u16, dst_ip: u32) {
    unsafe {
        core::ptr::write_volatile(
            MMIO_IP_TTL_PROTO_LEN_DST_IP,
            ((ttl as u64) << 56) | ((proto as u64) << 48) | ((len as u64) << 32) | dst_ip as u64,
        );
    }
}

pub fn eth_mmio_tx_data(payload_and_flags: u64) {
    unsafe {
        core::ptr::write_volatile(MMIO_TX_DATA, payload_and_flags);
    }
}

pub fn eth_mmio_get_rx_src_mac() -> u64 {
    unsafe { core::ptr::read_volatile(MMIO_RX_SRC_MAC) }
}

pub fn eth_mmio_get_rx_dst_mac_ethertype() -> u64 {
    unsafe { core::ptr::read_volatile(MMIO_RX_DST_MAC_TYPE) }
}

pub fn eth_mmio_get_rx_src_ip_dst_ip() -> u64 {
    unsafe { core::ptr::read_volatile(MMIO_RX_SRC_IP_DST_IP) }
}

pub fn eth_mmio_get_rx_ttl_proto_id_len_frag() -> u64 {
    unsafe { core::ptr::read_volatile(MMIO_RX_TTL_PROTO_ID_LEN_FRAG) }
}

pub fn eth_mmio_get_rx_ecn_ver_ihl_chksum() -> u32 {
    unsafe { core::ptr::read_volatile(MMIO_RX_DSCP_ECN_VER_IHL_CHKSUM) as u32 }
}

pub fn eth_mmio_rx_data() -> u64 {
    unsafe { core::ptr::read_volatile(MMIO_RX_DATA) }
}

pub fn eth_mmio_set_ip_dscp_ecn_src_ip(dscp_ecn: u8, src_ip: u32) {
    unsafe {
        core::ptr::write_volatile(
            MMIO_IP_DSCP_ECN_SRC_IP,
            ((dscp_ecn as u64) << 32) | src_ip as u64,
        );
    }
}

pub fn eth_mmio_get_ip_dscp_ecn_src_ip() -> u64 {
    unsafe { core::ptr::read_volatile(MMIO_IP_DSCP_ECN_SRC_IP) }
}

pub fn eth_mmio_set_gateway_ip_netmask(gateway_ip: u32, mask: u32) {
    unsafe {
        core::ptr::write_volatile(
            MMIO_GATEWAY_IP_NETMASK,
            ((gateway_ip as u64) << 32) | mask as u64,
        );
    }
}

pub fn eth_mmio_reset_state() {
    eth_mmio_set_tx_src_mac(0);
    eth_mmio_set_tx_ttl_proto_len_dst_ip(0, 0, 0, 0);
    eth_mmio_set_ip_dscp_ecn_src_ip(0, 0);
    eth_mmio_set_gateway_ip_netmask(0, 0);
}

pub struct RxIpHeader {
    pub src_mac: u64,
    pub dst_mac_type: u64,
    pub src_ip: u32,
    pub dst_ip: u32,
    pub ttl_proto_id_len_frag: u64,
    pub ecn_ver_ihl_chksum: u32,
}

pub struct RxIpPacket<'buf> {
    pub header: RxIpHeader,
    pub payload: &'buf [u8],
}

impl RxIpHeader {
    #[allow(dead_code)]
    pub fn dst_mac(&self) -> u64 {
        self.dst_mac_type & 0xFFFF_FFFF_FFFF
    }

    #[allow(dead_code)]
    pub fn ethertype(&self) -> u16 {
        (self.dst_mac_type >> 48) as u16
    }

    #[allow(dead_code)]
    pub fn fragment_flags(&self) -> u8 {
        ((self.ttl_proto_id_len_frag >> 13) & 0x3) as u8
    }

    #[allow(dead_code)]
    pub fn fragment_offset(&self) -> u16 {
        (self.ttl_proto_id_len_frag & 0x1FFF) as u16
    }

    #[allow(dead_code)]
    pub fn ip_full_len(&self) -> u16 {
        (self.ttl_proto_id_len_frag >> 16) as u16
    }

    #[allow(dead_code)]
    pub fn ip_payload_len(&self) -> u16 {
        self.ip_full_len() - 20
    }

    #[allow(dead_code)]
    pub fn identifier(&self) -> u16 {
        (self.ttl_proto_id_len_frag >> 32) as u16
    }

    #[allow(dead_code)]
    pub fn proto(&self) -> u8 {
        (self.ttl_proto_id_len_frag >> 48) as u8
    }

    #[allow(dead_code)]
    pub fn ttl(&self) -> u8 {
        (self.ttl_proto_id_len_frag >> 56) as u8
    }

    pub fn is_fragmented(&self) -> bool {
        self.fragment_offset() != 0 || self.fragment_flags() & 0b001 != 0
    }
}

pub struct RxIpPartialRead {
    pub header: RxIpHeader,
    pub read_buf: [u8; 14],
    pub len_read: usize,
    pub complete: bool,
}

/// This reads up to the 14 first bytes, so that we have a full header for most protocols
pub fn ip_start_recv_packet() -> Option<RxIpPartialRead> {
    let mut data = eth_mmio_rx_data();
    if data == 0 {
        return None;
    }
    let data_ptr = &data as *const u64 as *const u8;
    let mut len = ((data >> 56) & 0b111) as usize;
    let complete = data >= 0xC000_0000_0000_0000;

    let src_ip_dst_ip = eth_mmio_get_rx_src_ip_dst_ip();
    let mut partial_read = RxIpPartialRead {
        header: RxIpHeader {
            src_mac: eth_mmio_get_rx_src_mac(),
            dst_mac_type: eth_mmio_get_rx_dst_mac_ethertype(),
            src_ip: (src_ip_dst_ip >> 32) as u32,
            dst_ip: (src_ip_dst_ip & 0xFFFF_FFFF) as u32,
            ttl_proto_id_len_frag: eth_mmio_get_rx_ttl_proto_id_len_frag(),
            ecn_ver_ihl_chksum: eth_mmio_get_rx_ecn_ver_ihl_chksum(),
        },
        read_buf: [0; 2 * 7],
        len_read: len,
        complete,
    };
    let read_buf_ptr = partial_read.read_buf.as_mut_ptr();
    unsafe { core::ptr::copy_nonoverlapping(data_ptr, read_buf_ptr, len) };

    if !complete {
        data = eth_mmio_rx_data();
        len = ((data >> 56) & 0b111) as usize;
        unsafe {
            core::ptr::copy_nonoverlapping(data_ptr, read_buf_ptr.add(partial_read.len_read), len)
        };
        partial_read.len_read += len;
        partial_read.complete = data >= 0xC000_0000_0000_0000;
    }

    Some(partial_read)
}

// NOTE: This does NOT check the buffer is large enough for a full MTU-sized packet!
pub unsafe fn ip_finish_recv_packet(partial_read: RxIpPartialRead, buf: &mut [u8]) -> RxIpPacket {
    let mut read = 0;
    unsafe {
        core::ptr::copy_nonoverlapping(
            partial_read.read_buf.as_ptr(),
            buf.as_mut_ptr(),
            partial_read.len_read,
        )
    };
    let mut complete = partial_read.complete;
    read += partial_read.len_read;

    while !complete {
        let data = eth_mmio_rx_data();
        let data_ptr = &data as *const u64 as *const u8;
        complete = data >= 0xC000_0000_0000_0000;
        let len = ((data >> 56) & 0b111) as usize;
        unsafe { core::ptr::copy_nonoverlapping(data_ptr, buf.as_mut_ptr().add(read), len) };
        read += len;
    }

    RxIpPacket {
        header: partial_read.header,
        payload: &buf[..read],
    }
}

pub fn ip_discard_recv_packet(partial_read: RxIpPartialRead) {
    if partial_read.complete {
        return;
    }
    while eth_mmio_rx_data() < 0xC000_0000_0000_0000 {
        // Throw away data
    }
}

#[allow(dead_code)]
pub fn ip_recv_packet(buf: &mut [u8]) -> Option<RxIpPacket> {
    // Partial read wants at least 14 bytes. Just refuse tiny buffers.
    if buf.len() < 14 {
        return None;
    }
    let partial_read = match ip_start_recv_packet() {
        None => return None,
        Some(r) => r,
    };
    if buf.len() < partial_read.header.ip_full_len() as usize - 20 {
        ip_discard_recv_packet(partial_read);
        None
    } else {
        // SAFETY: We trust the IP header's len field, the hardware checks it
        unsafe { Some(ip_finish_recv_packet(partial_read, buf)) }
    }
}

pub fn start_ip_packet(payload_len: usize, dst_ip: u32, proto: u8) {
    assert!(payload_len <= u16::MAX as usize - 20);
    eth_mmio_set_tx_ttl_proto_len_dst_ip(64, proto, (payload_len + 20) as u16, dst_ip);
}

pub fn finish_ip_packet(mut payload: &[u8]) {
    let initial_flags: u8 = 7;
    let mut data_buf = [0, 0, 0, 0, 0, 0, 0, initial_flags];
    while payload.len() > 7 {
        unsafe { core::ptr::copy_nonoverlapping(payload.as_ptr(), data_buf.as_mut_ptr(), 7) };
        eth_mmio_tx_data(u64::from_le_bytes(data_buf));
        payload = &payload[7..];
    }
    unsafe {
        core::ptr::copy_nonoverlapping(payload.as_ptr(), data_buf.as_mut_ptr(), payload.len())
    };
    let last_tx_flag = 0b0100_0000u8;
    data_buf[7] = last_tx_flag | payload.len() as u8;
    eth_mmio_tx_data(u64::from_le_bytes(data_buf));
}

#[allow(dead_code)]
pub fn send_ip_packet(payload: &[u8], dst_ip: u32, proto: u8) {
    start_ip_packet(payload.len(), dst_ip, proto);
    finish_ip_packet(payload)
}
