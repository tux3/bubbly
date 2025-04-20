#![no_std]
#![no_main]

use test_rs::report_success;

#[unsafe(no_mangle)]
pub unsafe extern "C" fn main() {
    report_success();
}
