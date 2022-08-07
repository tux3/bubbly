const ETHERNET_MMIO_BASE: usize = 0x30000000000;
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

pub fn eth_mmio_get_rx_ecn_ver_ihl_chksum() -> u64 {
    unsafe { core::ptr::read_volatile(MMIO_RX_DSCP_ECN_VER_IHL_CHKSUM) }
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

pub fn eth_mmio_set_gateway_ip_netmask(gateway_ip: u32, mask: u32) {
    unsafe {
        core::ptr::write_volatile(
            MMIO_GATEWAY_IP_NETMASK,
            ((gateway_ip as u64) << 32) | mask as u64,
        );
    }
}

pub struct RxIpPacket<'buf> {
    pub src_mac: u64,
    pub dst_mac_type: u64,
    pub src_ip: u32,
    pub dst_ip: u32,
    pub payload: &'buf [u8],
}

impl RxIpPacket<'_> {
    #[allow(dead_code)]
    pub fn dst_mac(&self) -> u64 {
        self.dst_mac_type & 0xFFFF_FFFF_FFFF
    }

    #[allow(dead_code)]
    pub fn ethertype(&self) -> u16 {
        (self.dst_mac_type >> 48) as u16
    }
}

pub fn ip_recv_packet(buf: &mut [u8]) -> Option<RxIpPacket> {
    let mut read = 0;
    let mut data = eth_mmio_rx_data();
    if data == 0 {
        return None;
    }
    let data_ptr = &data as *const u64 as *const u8;
    let len = ((data >> 56) & 0b111) as usize;
    unsafe { core::ptr::copy_nonoverlapping(data_ptr, buf.as_mut_ptr().add(read), len) };
    read += len;

    while data < 0xC000_0000_0000_0000 {
        data = eth_mmio_rx_data();
        let len = ((data >> 56) & 0b111) as usize;
        unsafe { core::ptr::copy_nonoverlapping(data_ptr, buf.as_mut_ptr().add(read), len) };
        read += len;
    }

    let src_ip_dst_ip = eth_mmio_get_rx_src_ip_dst_ip();
    Some(RxIpPacket {
        src_mac: eth_mmio_get_rx_src_mac(),
        dst_mac_type: eth_mmio_get_rx_dst_mac_ethertype(),
        src_ip: (src_ip_dst_ip >> 32) as u32,
        dst_ip: (src_ip_dst_ip & 0xFFFF_FFFF) as u32,
        payload: &buf[..read],
    })
}

pub fn send_ip_packet(mut payload: &[u8], dst_ip: u32, proto: u8) {
    assert!(payload.len() <= u16::MAX as usize);
    eth_mmio_set_tx_ttl_proto_len_dst_ip(64, proto, payload.len() as u16, dst_ip);

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
