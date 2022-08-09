use anyhow::Result;
use clap::Parser;
use std::net::ToSocketAddrs;
use std::net::UdpSocket;
use std::path::PathBuf;
use xxhash_rust::xxh64::xxh64;

#[derive(Parser, Debug)]
#[clap(author, version, about, long_about = None)]
struct Args {
    /// IP address of the target
    #[clap(short, long, default_value = "192.168.1.110")]
    target: String,

    /// Payload to boot
    #[clap(short, long)]
    payload: PathBuf,
}

fn main() -> Result<()> {
    let args = Args::parse();

    let payload = std::fs::read(&args.payload)?;
    println!(
        "Sending boot payload {} to {}",
        args.payload.display(),
        &args.target
    );

    let socket = UdpSocket::bind("0.0.0.0:0")?;
    let target_addr = (args.target.as_str(), 0xB007)
        .to_socket_addrs()?
        .next()
        .unwrap();

    let hash = xxh64(&payload, 0).to_le_bytes();
    let mut header = Vec::new();
    header.extend_from_slice(&payload.len().to_le_bytes()[..3]);
    header.extend_from_slice(&hash);
    socket.send_to(&header, &target_addr)?;
    let mut total_sent = header.len();
    wait_for_ack(&socket, total_sent);

    let mtu = 1500 - 20 - 8;
    let mut payload = &payload[..];
    while payload.len() > mtu {
        socket.send_to(&payload[..mtu], &target_addr)?;
        total_sent += mtu;
        wait_for_ack(&socket, total_sent);
        payload = &payload[mtu..];
    }
    socket.send_to(payload, &target_addr)?;

    Ok(())
}

fn wait_for_ack(sock: &UdpSocket, total_sent: usize) {
    let mut recv_buf = [0u8; 4];
    sock.recv(&mut recv_buf)
        .expect("Did not receive expected ACK from device");
    let acked_size = u32::from_le_bytes(recv_buf);
    if acked_size as usize != total_sent {
        panic!(
            "Device ACKed {} bytes received, but we sent {}",
            acked_size, total_sent
        );
    }
}
