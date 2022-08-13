use crate::PLATFORM_BASE;

const MTIME_PTR: *mut u64 = PLATFORM_BASE as _;
const MTIMECMP_PTR: *mut u64 = (PLATFORM_BASE + 0x8) as _;

const MTIME_HZ: u64 = 1_000_000;

#[allow(dead_code)]
pub const fn mtime_to_usecs(mtime: u64) -> u64 {
    mtime / (MTIME_HZ / 1000 / 1000)
}

#[allow(dead_code)]
pub const fn mtime_to_msecs(mtime: u64) -> u64 {
    mtime / (MTIME_HZ / 1000)
}

#[allow(dead_code)]
pub const fn usecs_to_mtime(usecs: u64) -> u64 {
    usecs * (MTIME_HZ / 1000 / 1000)
}

#[allow(dead_code)]
pub const fn msecs_to_mtime(msecs: u64) -> u64 {
    msecs * (MTIME_HZ / 1000)
}

#[allow(dead_code)]
pub fn read_mtime() -> u64 {
    unsafe { core::ptr::read_volatile(MTIME_PTR) }
}

#[allow(dead_code)]
pub fn read_mtimecmp() -> u64 {
    unsafe { core::ptr::read_volatile(MTIMECMP_PTR) }
}

#[allow(dead_code)]
pub fn write_mtime(value: u64) {
    unsafe { core::ptr::write_volatile(MTIME_PTR, value) };
}

#[allow(dead_code)]
pub fn write_mtimecmp(value: u64) {
    unsafe { core::ptr::write_volatile(MTIMECMP_PTR, value) };
}
