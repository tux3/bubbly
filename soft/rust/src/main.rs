#![no_std]
#![no_main]
#![feature(const_mut_refs)]

use core::arch::asm;
use riscv::register;

const SRAM_BASE: usize = 0x18000000000;
const GPIO_BASE: usize = 0x20000000000;
const ETHERNET_MMIO_BASE: usize = 0x30000000000;
const ETH_MMIO_TX_SRC_MAC: *mut u64 = ETHERNET_MMIO_BASE as _;
const ETH_MMIO_TX_DST_MAC_TYPE: *mut u64 = (ETHERNET_MMIO_BASE + 0x8) as _;
const ETH_MMIO_TX_DATA: *mut u64 = (ETHERNET_MMIO_BASE + 0x10) as _;
const ETH_MMIO_RX_SRC_MAC: *mut u64 = (ETHERNET_MMIO_BASE + 0x18) as _;
const ETH_MMIO_RX_DST_MAC_TYPE: *mut u64 = (ETHERNET_MMIO_BASE + 0x20) as _;
const ETH_MMIO_RX_DATA: *mut u64 = (ETHERNET_MMIO_BASE + 0x28) as _;

const BOARD_MAC_ADDR: u64 = 0x00183e035117;
const ETH_FRAME_BUF_SIZE: usize = 1520; // Leave extra space for 64bit writes

// True if we read a frame
unsafe fn eth_recv_frame(buf: &mut [u8; ETH_FRAME_BUF_SIZE]) -> Option<usize> {
    None
}

fn eth_mmio_tx_data(payload_and_flags: u64) {
    unsafe { core::ptr::write_volatile(ETH_MMIO_TX_DATA, payload_and_flags); }
}

fn eth_send_frame(mut frame: &[u8]) {
    while frame.len() > 7 {
        let flags: u64 = 7;
        let payload = flags << (7 * 8);
        let mut payload_buf = payload.to_le_bytes();
        unsafe { core::ptr::copy_nonoverlapping(frame.as_ptr(), payload_buf.as_mut_ptr(), 7) };
        eth_mmio_tx_data(u64::from_le_bytes(payload_buf));

        frame = &frame[7..];
    }

    let last_flag = 0b0100_0000u8;
    let flags: u64 = last_flag as u64 | frame.len() as u64;
    let payload = flags << (7 * 8);
    let mut payload_buf = payload.to_le_bytes();
    unsafe { core::ptr::copy_nonoverlapping(frame.as_ptr(), payload_buf.as_mut_ptr(), frame.len()) };
    eth_mmio_tx_data(u64::from_le_bytes(payload_buf));
}

unsafe fn main() -> ! {
    let leds: &mut [u8; 3] = &mut *(GPIO_BASE as *mut _);
    leds[0] = 1;

    let eth_frame_buf: &mut [u8; ETH_FRAME_BUF_SIZE] = &mut *(SRAM_BASE as *mut _);

    let ethertype = 0x0; // Invalid, but easy to spot in Wireshark
    let broadcast_mac = 0xffff_ffff_ffffu64;
    core::ptr::write_volatile(ETH_MMIO_TX_DST_MAC_TYPE, (ethertype << 48) | broadcast_mac);
    leds[1] = 1;

    let mut led_enable = 0;
    let mut last_mcycle = register::mcycle::read64();
    loop {
        if let Some(size) = eth_recv_frame(eth_frame_buf) {
            eth_send_frame(&eth_frame_buf[..size]);
        }

        let mcycle = register::mcycle::read64();
        if mcycle - last_mcycle > 15_000_000 {
            last_mcycle = mcycle;
            led_enable = !led_enable;
            leds[0] = led_enable;

            let tmp_data = &[0u8, 1u8, 2u8, 3u8, 4u8, 5u8, 6u8, 7u8, 8u8, 9u8, 10u8];
            eth_send_frame(tmp_data);
        }
    }
}

#[link_section = ".start"]
#[no_mangle]
pub unsafe extern "C" fn _start() -> ! {
    const STACK_PTR: usize = SRAM_BASE + 4096 - 8;
    asm!(
    "add sp, {sp}, 0",
    sp = in(reg) STACK_PTR,
    );

    core::ptr::write_volatile(ETH_MMIO_TX_SRC_MAC, BOARD_MAC_ADDR);

    main()
}

#[panic_handler]
unsafe fn panic(_panic: &core::panic::PanicInfo<'_>) -> ! {
    let panic_led = (GPIO_BASE + 2) as *mut u8;
    *panic_led = 1;
    loop {}
}
