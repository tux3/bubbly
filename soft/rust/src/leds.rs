use crate::PLATFORM_BASE;

const LEDS_BASE: usize = PLATFORM_BASE + 0x10;

pub enum LED {
    Led0 = 0,
    Led1 = 1,
    Panic = 2,
}

#[allow(dead_code)]
pub fn set_led(led: LED, state: bool) {
    let led_ptr = (LEDS_BASE + led as usize) as *mut u8;
    unsafe { core::ptr::write_volatile(led_ptr, state as u8) };
}

#[allow(dead_code)]
pub fn get_led(led: LED) -> bool {
    let led_ptr = (LEDS_BASE + led as usize) as *mut u8;
    unsafe { core::ptr::read_volatile(led_ptr) != 0 }
}

#[allow(dead_code)]
pub fn toggle_led(led: LED) {
    let led_ptr = (LEDS_BASE + led as usize) as *mut u8;
    let state = unsafe { core::ptr::read_volatile(led_ptr) };
    unsafe { core::ptr::write_volatile(led_ptr, !state) };
}
