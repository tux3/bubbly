use crate::ethernet_mmio::*;
use crate::iface::SocketToken;
use crate::{log_msg_udp, send_udp, MmioInterface, Socket, UdpSocket};
use riscv::register::mcycle;

const DHCP_MAGIC: [u8; 4] = [0x63, 0x82, 0x53, 0x63];
// Intervals are in cycles
const TICK_CYCLES: u64 = 50_000_000u64;
const DISCOVER_RETRY_INTERVAL: u64 = TICK_CYCLES;
const DISCOVER_TIMEOUT: u64 = 16 * TICK_CYCLES;
const REQUEST_RETRY_INTERVAL: u64 = TICK_CYCLES;
const REQUEST_TIMEOUT: u64 = 6 * TICK_CYCLES;

const DEBUG_LOG: bool = false;

fn dhcp_debug_log(msg: impl AsRef<[u8]>) {
    if DEBUG_LOG {
        log_msg_udp(msg);
    }
}

#[derive(Eq, PartialEq, Copy, Clone)]
#[repr(u8)]
enum MsgType {
    Discover = 1,
    Offer = 2,
    Request = 3,
    Ack = 5,
    Nack = 6,
}

struct DhcpReply {
    pub kind: MsgType,
    pub xid: u32,
    pub yiaddr: u32,
    pub siaddr: u32,
    pub dhcp_server: u32,
    pub subnet_mask: u32,
    pub router: u32,
}

pub struct DhcpLease {
    pub ip: u32,
    pub subnet_mask: u32,
    pub router: u32,
}

fn fill_dhcp_client_request(buf: &mut [u8], txid: u32, ciaddr: u32, siaddr: u32, kind: MsgType) {
    let txid = txid.to_le_bytes();
    let ciaddr = ciaddr.to_be_bytes();
    let siaddr = siaddr.to_be_bytes();
    let mac_addr = eth_mmio_get_tx_src_mac().to_le_bytes();
    #[rustfmt::skip]
    buf[..243].copy_from_slice(&[
        0x1, 0x1, 0x6, 0x0, // DHCP Discover, ethernet type
        txid[0], txid[1], txid[2], txid[3],
        0, 0, 0, 0, // SECS & FLAGS
        ciaddr[0], ciaddr[1], ciaddr[2], ciaddr[3], // CIADDR
        0, 0, 0, 0, // YIADDR
        siaddr[0], siaddr[1], siaddr[2], siaddr[3], // SIADDR
        0, 0, 0, 0, // GIADDR
        // CHADDR
        mac_addr[5], mac_addr[4], mac_addr[3], mac_addr[2], mac_addr[1], mac_addr[0], 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0,
        // Server name
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // Boot file name
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // Magic cookie
        DHCP_MAGIC[0], DHCP_MAGIC[1], DHCP_MAGIC[2], DHCP_MAGIC[3],
        // Options (TLV)
        0x35, 0x01, kind as u8, // DHCP msg type
    ]);
}

fn dhcp_discover(txid: u32) {
    let mut buf = [0; 249];
    fill_dhcp_client_request(&mut buf, txid, 0, 0, MsgType::Discover);
    #[rustfmt::skip]
    buf[243..249].copy_from_slice(&[
        // Options (TLV)
        0x37, 0x3, // Parameter request list (each is an option code)
            0x1,  // Request subnet mask
            0x3,  // Router
            0x6,  // DNS server
        0xFF, // End of options
    ]);
    send_udp(&buf, 0xFFFF_FFFF, 68, 67);
}

fn dhcp_request(dhcp_server: u32, txid: u32, yiaddr: u32, siaddr: u32) {
    let mut buf = [0; 256];
    fill_dhcp_client_request(&mut buf, txid, yiaddr, siaddr, MsgType::Request);
    let yiaddr = yiaddr.to_be_bytes();
    let dhcp_server = dhcp_server.to_be_bytes();
    #[rustfmt::skip]
    buf[243..256].copy_from_slice(&[
        // Options (TLV)
        0x32, 0x4, yiaddr[0], yiaddr[1], yiaddr[2], yiaddr[3], // Request addr
        0x36, 0x4, dhcp_server[0], dhcp_server[1], dhcp_server[2], dhcp_server[3], // DHCP server
        0xFF, // End of options
    ]);
    send_udp(&buf, 0xFFFF_FFFF, 68, 67);
}

fn parse_dhcp_reply(buf: &[u8]) -> Option<DhcpReply> {
    if buf.len() < 241 {
        dhcp_debug_log("DHCP reply shorter than minimum");
        return None;
    }
    if buf[236] != DHCP_MAGIC[0]
        || buf[237] != DHCP_MAGIC[1]
        || buf[238] != DHCP_MAGIC[2]
        || buf[239] != DHCP_MAGIC[3]
    {
        dhcp_debug_log("DHCP reply has invalid magic value");
        return None;
    }
    if buf[0] != 0x2 || buf[1] != 0x1 || buf[2] != 0x6 {
        return None;
    }
    let xid = u32::from_le_bytes([buf[4], buf[5], buf[6], buf[7]]);

    // SECS/FLAGS
    if buf[8..12] != [0; 4] {
        dhcp_debug_log("DHCP reply has invalid SECS/FLAGS");
        return None;
    }
    let yiaddr = u32::from_be_bytes([buf[16], buf[17], buf[18], buf[19]]);
    let siaddr = u32::from_be_bytes([buf[20], buf[21], buf[22], buf[23]]);
    let client_mac =
        u64::from_be_bytes([0, 0, buf[28], buf[29], buf[30], buf[31], buf[32], buf[33]]);
    if client_mac != eth_mmio_get_tx_src_mac() || buf[34..44] != [0; 10] {
        dhcp_debug_log("DHCP reply doesn't match local MAC address");
        return None;
    }
    if buf[44..236] != [0; 192] {
        dhcp_debug_log("DHCP reply has non-zero server host name or boot file name, rejecting");
        return None;
    }

    let mut kind = None;
    let mut dhcp_server = 0;
    let mut subnet_mask = 0;
    let mut router = 0;
    let mut option_pos = 240;
    while buf[option_pos] != 0xFF {
        let opt = buf[option_pos];
        if option_pos + 1 >= buf.len() {
            dhcp_debug_log("DHCP reply options truncated");
            return None;
        }
        let opt_len = buf[option_pos + 1] as usize;
        if option_pos + 1 + opt_len + 1 >= buf.len() {
            dhcp_debug_log("DHCP reply options truncated");
            return None;
        }
        if opt == 0x35 {
            // DHCP reply type
            if opt_len != 1 {
                dhcp_debug_log("DHCP reply has invalid message type option len");
                return None;
            }
            kind = Some(match buf[option_pos + 2] {
                2 => MsgType::Offer,
                5 => MsgType::Ack,
                6 => MsgType::Nack,
                _ => {
                    dhcp_debug_log("DHCP reply has unexpected message type");
                    return None;
                }
            });
        } else if opt == 0x36 {
            // DHCP server
            if opt_len != 4 {
                dhcp_debug_log("DHCP reply has invalid DHCP server option len");
                return None;
            }
            dhcp_server = u32::from_be_bytes([
                buf[option_pos + 2],
                buf[option_pos + 3],
                buf[option_pos + 4],
                buf[option_pos + 5],
            ]);
        } else if opt == 0x1 {
            // Subnet mask
            if opt_len != 4 {
                dhcp_debug_log("DHCP reply has invalid subnet mask option len");
                return None;
            }
            subnet_mask = u32::from_be_bytes([
                buf[option_pos + 2],
                buf[option_pos + 3],
                buf[option_pos + 4],
                buf[option_pos + 5],
            ]);
        } else if opt == 0x3 {
            // Router
            if opt_len != 4 {
                dhcp_debug_log("DHCP reply has invalid router option len");
                return None;
            }
            router = u32::from_be_bytes([
                buf[option_pos + 2],
                buf[option_pos + 3],
                buf[option_pos + 4],
                buf[option_pos + 5],
            ]);
        }
        option_pos += opt_len + 2;
    }
    let kind = match kind {
        None => {
            dhcp_debug_log("DHCP reply missing message type option");
            return None;
        }
        Some(k) => k,
    };

    Some(DhcpReply {
        kind,
        xid,
        yiaddr,
        siaddr,
        dhcp_server,
        subnet_mask,
        router,
    })
}

fn get_dhcp_offer(iface: &mut MmioInterface, sock_token: &SocketToken) -> Result<DhcpReply, ()> {
    let start_mcycle = mcycle::read64();
    let mut cur_mcycle = start_mcycle;
    let mut last_send_time = start_mcycle;
    let mut retry_interval = DISCOVER_RETRY_INTERVAL;
    dhcp_discover(last_send_time as u32);
    loop {
        if cur_mcycle - start_mcycle > DISCOVER_TIMEOUT {
            return Err(());
        }
        if cur_mcycle - last_send_time >= retry_interval {
            last_send_time = cur_mcycle;
            dhcp_discover(last_send_time as u32);
            retry_interval *= 2;
        }

        if iface.poll() {
            let sock = iface.get_socket(&sock_token);
            let maybe_reply = parse_dhcp_reply(sock.peek_recv_buf());
            sock.clear_recv_buf();
            if let Some(reply) = maybe_reply && reply.kind == MsgType::Offer {
                if reply.xid == last_send_time as u32 {
                    return Ok(reply);
                }
            }
        }

        cur_mcycle = mcycle::read64();
    }
}

fn get_dhcp_ack_or_nack(
    iface: &mut MmioInterface,
    sock_token: &SocketToken,
    offer: DhcpReply,
) -> Result<DhcpReply, Option<DhcpReply>> {
    let start_mcycle = mcycle::read64();
    let mut cur_mcycle = start_mcycle;
    let mut last_send_time = start_mcycle;
    let mut retry_interval = REQUEST_RETRY_INTERVAL;
    dhcp_request(offer.dhcp_server, offer.xid, offer.yiaddr, offer.siaddr);
    loop {
        if cur_mcycle - start_mcycle > REQUEST_TIMEOUT {
            return Err(None);
        }
        if cur_mcycle - last_send_time >= retry_interval {
            last_send_time = cur_mcycle;
            dhcp_request(offer.dhcp_server, offer.xid, offer.yiaddr, offer.siaddr);
            retry_interval *= 2;
        }

        if iface.poll() {
            let sock = iface.get_socket(&sock_token);
            let maybe_reply = parse_dhcp_reply(sock.peek_recv_buf());
            sock.clear_recv_buf();
            match maybe_reply {
                Some(reply) if reply.kind == MsgType::Ack => {
                    if reply.xid == offer.xid as u32 {
                        return Ok(reply);
                    }
                }
                Some(reply) if reply.kind == MsgType::Nack => {
                    if reply.xid == offer.xid as u32 {
                        return Err(Some(reply));
                    }
                }
                _ => {}
            }
        }

        cur_mcycle = mcycle::read64();
    }
}

pub fn get_ethernet_dhcp_lease<'b>(
    iface: &mut MmioInterface<'b>,
    rx_buf: &'b mut [u8],
) -> Result<DhcpLease, ()> {
    eth_mmio_set_ip_dscp_ecn_src_ip(0, 0);

    let sock = UdpSocket::new_with_src(rx_buf, 0, 68, 0xFFFF_FFFF, 67);
    let sock_token = iface.add_socket(Socket::Udp(sock));
    let offer = get_dhcp_offer(iface, &sock_token)?;

    let lease = match get_dhcp_ack_or_nack(iface, &sock_token, offer) {
        Ok(lease) => lease,
        Err(_) => return Err(()), // Nack or timeout
    };
    iface.remove_socket(sock_token);

    Ok(DhcpLease {
        ip: lease.yiaddr,
        subnet_mask: lease.subnet_mask,
        router: lease.router,
    })
}

pub fn configure_dhcp<'b>() {
    let mut dhcp_rx_buf = [0u8; 500];
    let mut iface = MmioInterface::new();

    if let Ok(lease) = get_ethernet_dhcp_lease(&mut iface, &mut dhcp_rx_buf) {
        log_msg_udp("Received DHCP lease, configuring interface");
        eth_mmio_set_ip_dscp_ecn_src_ip(0, lease.ip);
        eth_mmio_set_gateway_ip_netmask(lease.router, lease.subnet_mask);
    } else {
        log_msg_udp("Failed to get DHCP lease, setting static IP");
        eth_mmio_set_ip_dscp_ecn_src_ip(0, u32::from_be_bytes([192, 168, 1, 110]));
        eth_mmio_set_gateway_ip_netmask(u32::from_be_bytes([192, 168, 1, 254]), 0xFF_FF_FF_00);
    }
}
