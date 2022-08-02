const ETHERNET_MMIO_BASE: usize = 0x30000000000;
const ETH_MMIO_TX_SRC_MAC: *mut u64 = ETHERNET_MMIO_BASE as _;
const ETH_MMIO_TX_DST_MAC_TYPE: *mut u64 = (ETHERNET_MMIO_BASE + 0x8) as _;
const ETH_MMIO_TX_DATA: *mut u64 = (ETHERNET_MMIO_BASE + 0x10) as _;
const ETH_MMIO_RX_SRC_MAC: *mut u64 = (ETHERNET_MMIO_BASE + 0x18) as _;
const ETH_MMIO_RX_DST_MAC_TYPE: *mut u64 = (ETHERNET_MMIO_BASE + 0x20) as _;
const ETH_MMIO_RX_DATA: *mut u64 = (ETHERNET_MMIO_BASE + 0x28) as _;

pub fn eth_mmio_set_tx_src_mac(mac: u64) {
    unsafe { core::ptr::write_volatile(ETH_MMIO_TX_SRC_MAC, mac); }
}

pub fn eth_mmio_set_tx_dst_mac_ethertype(mac: u64, ethertype: u16) {
    unsafe { core::ptr::write_volatile(ETH_MMIO_TX_DST_MAC_TYPE, ((ethertype as u64) << 48) | mac); }
}

pub fn eth_mmio_write_tx_data(payload_and_flags: u64) {
    unsafe { core::ptr::write_volatile(ETH_MMIO_TX_DATA, payload_and_flags); }
}

pub fn eth_mmio_get_rx_src_mac() -> u64 {
    unsafe { core::ptr::read_volatile(ETH_MMIO_RX_SRC_MAC) }
}

pub fn eth_mmio_get_rx_dst_mac_ethertype() -> u64 {
    unsafe { core::ptr::read_volatile(ETH_MMIO_RX_DST_MAC_TYPE) }
}

pub fn eth_mmio_read_rx_data() -> u64 {
    unsafe { core::ptr::read_volatile(ETH_MMIO_RX_DATA) }
}

pub struct RxEthernetFrame<'buf> {
    pub src_mac: u64,
    pub dst_mac_type: u64,
    pub payload: &'buf [u8]
}

impl RxEthernetFrame<'_> {
    #[allow(dead_code)]
    pub fn dst_mac(&self) -> u64 {
        self.dst_mac_type & 0xFFFF_FFFF_FFFF
    }

    #[allow(dead_code)]
    pub fn ethertype(&self) -> u16 {
        (self.dst_mac_type >> 48) as u16
    }
}

pub fn eth_recv_frame(buf: &mut [u8]) -> Option<RxEthernetFrame> {
    let mut read = 0;
    let mut data = eth_mmio_read_rx_data();
    if data == 0 {
        return None
    }
    let data_ptr = &data as *const u64 as *const u8;
    let len = ((data >> 56) & 0b111) as usize;
    unsafe { core::ptr::copy_nonoverlapping(data_ptr, buf.as_mut_ptr().add(read), len) };
    read += len;

    while data < 0xC000_0000_0000_0000 {
        data = eth_mmio_read_rx_data();
        let len = ((data >> 56) & 0b111) as usize;
        unsafe { core::ptr::copy_nonoverlapping(data_ptr, buf.as_mut_ptr().add(read), len) };
        read += len;
    }

    Some(RxEthernetFrame {
        src_mac: eth_mmio_get_rx_src_mac(),
        dst_mac_type: eth_mmio_get_rx_dst_mac_ethertype(),
        payload: &buf[..read]
    })
}

pub fn eth_send_frame(mut payload: &[u8], dst_mac: u64, ethertype: u16) {
    eth_mmio_set_tx_dst_mac_ethertype(dst_mac, ethertype);

    let initial_flags: u8 = 7;
    let mut data_buf = [0, 0, 0, 0, 0, 0, 0, initial_flags];
    while payload.len() > 7 {
        unsafe { core::ptr::copy_nonoverlapping(payload.as_ptr(), data_buf.as_mut_ptr(), 7) };
        eth_mmio_write_tx_data(u64::from_le_bytes(data_buf));
        payload = &payload[7..];
    }
    unsafe { core::ptr::copy_nonoverlapping(payload.as_ptr(), data_buf.as_mut_ptr(), payload.len()) };
    let last_tx_flag = 0b0100_0000u8;
    data_buf[7] = last_tx_flag | payload.len() as u8;
    eth_mmio_write_tx_data(u64::from_le_bytes(data_buf));
}
