#![no_std]
#![no_main]
#![feature(const_mut_refs)]

use riscv::register;

const GPIO_BASE: i64 = 0x20000000000;
const ETHERNET_MMIO_BASE: i64 = 0x30000000000;
const ETH_SRC_MAC: *mut u64 = ETHERNET_MMIO_BASE as _;
const ETH_DST_MAC_TYPE: *mut u64 = (ETHERNET_MMIO_BASE + 8) as _;

const BOARD_MAC_ADDR: u64 = 0x00183e035117;

#[no_mangle]
pub unsafe extern "C" fn _start() -> ! {
    let leds: &mut [u8; 3] = &mut *(GPIO_BASE as *mut _);
    leds[0] = 1;

    *ETH_SRC_MAC = BOARD_MAC_ADDR;
    let ethertype = 0x0806u64; // ARP
    let broadcast_mac = 0xffff_ffff_ffffu64;
    *ETH_DST_MAC_TYPE = (ethertype << 48) | broadcast_mac;

    let mut led_enable = 0;
    let mut last_mcycle = register::mcycle::read64();
    loop {
        let mcycle = register::mcycle::read64();
        if mcycle - last_mcycle > 15_000_000 {
            last_mcycle = mcycle;
            led_enable = !led_enable;
            leds[0] = led_enable;
        }
    }
}

#[panic_handler]
unsafe fn panic(_panic: &core::panic::PanicInfo<'_>) -> ! {
    let panic_led = (GPIO_BASE+2) as *mut u8;
    *panic_led = 1;
    loop {}
}
