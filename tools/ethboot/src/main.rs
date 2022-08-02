use std::mem;
use std::path::PathBuf;
use clap::Parser;
use anyhow::{anyhow, Result};
use socket2::{Domain, Protocol, SockAddr, Socket, Type};
use libc::{sockaddr_storage, sockaddr_ll, socklen_t, c_int, ETH_ALEN, c_uchar};
use xxhash_rust::xxh64::xxh64;

#[derive(Parser, Debug)]
#[clap(author, version, about, long_about = None)]
struct Args {
    /// Name of the interface
    #[clap(short, long, default_value = "eth0")]
    iface: String,

    /// Payload to boot
    #[clap(short, long)]
    payload: PathBuf,
}

fn main() -> Result<()> {
    let args = Args::parse();

    let mut payload = std::fs::read(&args.payload)?;
    println!("Sending boot payload {} on interface {}", args.payload.display(), &args.iface);

    let mut if_idx = None;
    let mut mac_addr = None;
    for iface in default_net::interface::get_interfaces() {
        if iface.name == args.iface {
            if_idx = Some(iface.index);
            mac_addr = iface.mac_addr;
        }
    }
    let if_idx = if_idx.ok_or_else(|| anyhow!("Couldn't find interface {}", args.iface))?;
    let mac_addr = mac_addr.ok_or_else(|| anyhow!("Couldn't get MAC address for interface {}", args.iface))?;
    let ipproto_raw = Protocol::from(255);
    let sock = Socket::new(Domain::PACKET, Type::RAW, Some(ipproto_raw))?;

    let dst_mac = &[0u8; 6];
    let addr = unsafe {
        let mut addr_storage: sockaddr_storage = mem::zeroed();
        let addr = mem::transmute::<&mut sockaddr_storage, &mut sockaddr_ll>(&mut addr_storage);
        addr.sll_ifindex = if_idx as c_int;
        addr.sll_halen = ETH_ALEN as c_uchar;
        addr.sll_addr[0..6].copy_from_slice(dst_mac);
        SockAddr::new(addr_storage, mem::size_of::<sockaddr_ll>() as socklen_t)
    };

    let hash: Vec<u8> = xxh64(&payload, 0).to_le_bytes()[0..6].iter().rev().copied().collect();
    let mut eth_payload = Vec::new();
    eth_payload.extend_from_slice(&hash); // Dest MAC
    eth_payload.extend_from_slice(&mac_addr.octets()); // Src MAC
    eth_payload.extend_from_slice(&[0xB0, 0x07]); // Ethertype ("BOOT" ethertype)
    eth_payload.append(&mut payload);

    sock.send_to(&eth_payload, &addr)?;

    Ok(())
}
