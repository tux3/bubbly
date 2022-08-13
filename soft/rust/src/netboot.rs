use crate::ethernet_mmio::eth_mmio_reset_state;
use crate::socket::{send_udp, ReadableSocket};
use crate::start_and_traps::disable_interrupts;
use crate::{log_msg_udp, set_led, LED, RX_BUF_SIZE, SRAM_BASE, SRAM_SIZE};
use core::mem::transmute;
use lzss::{Lzss, SliceReader, SliceWriter};
use riscv::register;
use xxhash_rust::xxh64::xxh64;

// Enforce we leave a bit of free stack space so it doesn't stack clash on next boot...
// Much rather deal with this check failing too eagerly than stack overwriting code :)
// Isn't it fun, not having any paging or memory protection?
const CODE_FREE_SPACE: usize = SRAM_SIZE - RX_BUF_SIZE - 2048;

// Not an exhaustive reset, but we can clean up a few things before rebooting
fn reset_platform_state() {
    disable_interrupts();
    unsafe { core::arch::asm!("csrrw x0, mie, x0") };

    eth_mmio_reset_state();
    set_led(LED::Led0, false);
    set_led(LED::Led1, false);
    set_led(LED::Panic, false);
}

pub unsafe fn unzip_and_exec(payload: &[u8]) -> ! {
    assert!(payload.len() <= CODE_FREE_SPACE);

    // SAFETY: None of this is safe!
    unsafe {
        let dst_ptr = SRAM_BASE as *mut u8;
        let dst_slice = core::slice::from_raw_parts_mut(dst_ptr, CODE_FREE_SPACE);

        type BootLzss = Lzss<11, 4, 0x00, { 1 << 11 }, { 2 << 11 }>;
        BootLzss::decompress(SliceReader::new(payload), SliceWriter::new(dst_slice))
            .expect("Failed to unzip exec payload");

        reset_platform_state();

        let dst_ptr = dst_ptr as *const ();
        let dst_fn: unsafe extern "C" fn() -> ! = transmute(dst_ptr);
        dst_fn();
    }
}

pub fn handle_boot_request(sock: &mut dyn ReadableSocket) {
    let payload = match sock.peek_recv_buf() {
        None => return,
        Some(p) => p,
    };
    if payload.len() < 3 + 8 {
        // If we get a datagram shorter than the header, this is 100% junk
        sock.clear_recv_buf();
        return;
    }

    let full_len =
        ((payload[2] as usize) << 16) | ((payload[1] as usize) << 8) | payload[0] as usize;

    if full_len + 8 + 3 > RX_BUF_SIZE {
        log_msg_udp("Boot payload longer than RX buffer! Discarding");
        sock.clear_recv_buf();
        return;
    }

    if payload.len() < 3 + 8 + full_len {
        // Don't clear recv buffer, and tell peer we're ready for more (our hardware rx buffer is smol)
        send_udp(
            &(payload.len() as u32).to_le_bytes(),
            sock.peer_ip(),
            0xB007,
            sock.peer_port(),
        );
        return;
    }
    if payload.len() > 3 + 8 + full_len {
        log_msg_udp("Boot payload longer than header length");
        sock.clear_recv_buf();
        return;
    }

    let expected_hash = &payload[3..11];
    let payload_hash = xxh64(&payload[3 + 8..], 0).to_le_bytes();
    if expected_hash != payload_hash {
        log_msg_udp(b"Invalid boot payload hash");
        log_msg_udp(&expected_hash);
        log_msg_udp(&payload_hash);
        sock.clear_recv_buf();
    } else {
        log_msg_udp(b"Booting payload");
        let unzip_and_exec_ptr = register::mscratch::read() as *const ();
        let unzip_and_exec_fn: fn(&[u8]) -> ! = unsafe { transmute(unzip_and_exec_ptr) };
        unzip_and_exec_fn(&payload[3 + 8..]);
    }
}
