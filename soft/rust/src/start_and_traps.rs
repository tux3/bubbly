use crate::ethernet_mmio::eth_mmio_set_tx_src_mac;
use crate::leds::{set_led, toggle_led, LED};
use crate::mtime::{msecs_to_mtime, read_mtime, write_mtime, write_mtimecmp};
use crate::{log_msg_udp, main, netboot, SRAM_BASE, SRAM_SIZE};
use core::hint::unreachable_unchecked;
use core::sync::atomic::{AtomicBool, Ordering};
use riscv::register::{self, mtvec::TrapMode};

pub const TIMER_INT_MASK: u64 = 0x80;
pub const ETHERNET_RX_MASK: u64 = 0x0001_0000;
pub const BUTTONS_INTS_MASK: u64 = 0x001E_0000;

const BOARD_MAC_ADDR: u64 = 0x00183e035117;
const TIMER_INTERVAL_MS: u64 = 250;
static HAS_FAULTED: AtomicBool = AtomicBool::new(false);

#[link_section = ".start"]
#[no_mangle]
unsafe extern "C" fn start() -> ! {
    unsafe {
        const STACK_PTR: usize = SRAM_BASE + SRAM_SIZE;
        core::arch::asm!(
        "add sp, {sp}, 0",
        sp = in(reg) STACK_PTR,
        );

        if register::mscratch::read() == 0 {
            register::mscratch::write(netboot::unzip_and_exec as usize);
        }
        HAS_FAULTED.store(false, Ordering::Release);
        register::mtvec::write(trap_handler_asm as usize, TrapMode::Direct);
    }

    eth_mmio_set_tx_src_mac(BOARD_MAC_ADDR);

    write_mtime(0);
    write_mtimecmp(0);

    unmask_interrupts(BUTTONS_INTS_MASK | ETHERNET_RX_MASK | TIMER_INT_MASK);
    enable_interrupts();

    main()
}

pub fn clear_pending_interrupts(mask: u64) {
    unsafe { core::arch::asm!("csrrc x0, mip, {}", in(reg) mask) };
}

pub fn mask_interrupts(mask: u64) {
    unsafe { core::arch::asm!("csrrc x0, mie, {}", in(reg) mask) };
}

pub fn unmask_interrupts(mask: u64) {
    unsafe { core::arch::asm!("csrrs x0, mie, {}", in(reg) mask) };
}

// Return previous state of mstatus.MIE
pub fn disable_interrupts() -> bool {
    let mut prev_mstatus: u64;
    const MIE_MASK: u64 = 0b1000;
    unsafe { core::arch::asm!("csrrc {}, mstatus, {}", out(reg) prev_mstatus, in(reg) MIE_MASK) };
    prev_mstatus & MIE_MASK != 0
}

// Return previous state of mstatus.MIE
pub fn enable_interrupts() -> bool {
    let mut prev_mstatus: u64;
    const MIE_MASK: u64 = 0b1000;
    unsafe { core::arch::asm!("csrrs {}, mstatus, {}", out(reg) prev_mstatus, in(reg) MIE_MASK) };
    prev_mstatus & MIE_MASK != 0
}

#[link_section = ".trap_handler"]
#[no_mangle]
#[naked]
unsafe extern "C" fn trap_handler_asm() {
    unsafe {
        core::arch::asm!(
            "addi sp, sp, -128",
            "sd ra, 0(sp)",
            "sd t0, 8(sp)",
            "sd t1, 16(sp)",
            "sd t2, 24(sp)",
            "sd t3, 32(sp)",
            "sd t4, 40(sp)",
            "sd t5, 48(sp)",
            "sd t6, 56(sp)",
            "sd a0, 64(sp)",
            "sd a1, 72(sp)",
            "sd a2, 80(sp)",
            "sd a3, 88(sp)",
            "sd a4, 96(sp)",
            "sd a5, 104(sp)",
            "sd a6, 112(sp)",
            "sd a7, 120(sp)",
            "lla a0, trap_handler",
            "jalr a0",
            "ld ra, 0(sp)",
            "ld t0, 8(sp)",
            "ld t1, 16(sp)",
            "ld t2, 24(sp)",
            "ld t3, 32(sp)",
            "ld t4, 40(sp)",
            "ld t5, 48(sp)",
            "ld t6, 56(sp)",
            "ld a0, 64(sp)",
            "ld a1, 72(sp)",
            "ld a2, 80(sp)",
            "ld a3, 88(sp)",
            "ld a4, 96(sp)",
            "ld a5, 104(sp)",
            "ld a6, 112(sp)",
            "ld a7, 120(sp)",
            "addi sp, sp, 128",
            "mret",
            options(noreturn)
        )
    };
}

#[derive(Eq, PartialEq, Copy, Clone)]
#[repr(u8)]
enum ExceptionCause {
    IllegalInstr = 2,
    ECallMMode = 11,
}

#[derive(Eq, PartialEq, Copy, Clone)]
#[repr(u8)]
#[allow(dead_code)]
enum InterruptCause {
    Timer = 7,
    EthernetRx = 16,
    Platform1 = 17,
    Platform2 = 18,
    Platform3 = 19,
    Platform4 = 20,
}

#[link_section = ".trap_handler"]
#[no_mangle]
unsafe extern "C" fn trap_handler() {
    let mcause = register::mcause::read();
    if mcause.is_interrupt() {
        if mcause.code() == InterruptCause::Timer as usize {
            toggle_led(LED::Led0);

            let mtime = read_mtime();
            let mut next_mtimecmp = mtime + msecs_to_mtime(TIMER_INTERVAL_MS);
            while next_mtimecmp < mtime {
                next_mtimecmp += msecs_to_mtime(TIMER_INTERVAL_MS);
            }
            write_mtimecmp(next_mtimecmp);
        } else if mcause.code() == InterruptCause::EthernetRx as usize {
            // For now we we just use this interrupt as a WFI wakeup, and we rx outside the handler
            // We can't clear it here, because it will just trigger again if not handled
            // That means we have to mask it until regular code has it handled and can clear it
            mask_interrupts(ETHERNET_RX_MASK);
            return;
        } else if mcause.code() >= InterruptCause::Platform1 as usize
            && mcause.code() <= InterruptCause::Platform4 as usize
        {
            log_msg_udp("Received platform interrupt!");
            log_msg_udp(register::mepc::read().to_be_bytes());
            log_msg_udp(mcause.bits().to_be_bytes());
        } else {
            log_msg_udp("Unexpected interrupt, continuing");
            log_msg_udp(mcause.bits().to_be_bytes());
        }

        unsafe {
            core::arch::asm!("csrrc x0, mip, {clear_mask}", clear_mask = in(reg) (1u64 << mcause.code()))
        };
        return;
    }

    let mcause = mcause.code();
    if mcause == ExceptionCause::ECallMMode as usize {
        log_msg_udp("ECALL received");
        increment_mepc();
        return;
    }

    set_led(LED::Panic, true);
    if HAS_FAULTED.swap(true, Ordering::AcqRel) {
        log_msg_udp("NESTED TRAP");
        log_msg_udp(mcause.to_be_bytes());
        log_msg_udp(register::mepc::read().to_be_bytes());
        log_msg_udp(register::mtval::read().to_be_bytes());
    } else {
        if mcause == ExceptionCause::IllegalInstr as usize {
            // This is what panic!() does since we build with panic_immediate_abort
            log_msg_udp("ILLEGAL INSTRUCTION TRAP, sending mepc/mtval");
        } else {
            log_msg_udp("TRAP HANDLER, sending mcause/mepc/mtval");
            log_msg_udp(mcause.to_be_bytes());
        }
        log_msg_udp(register::mepc::read().to_be_bytes());
        log_msg_udp(register::mtval::read().to_be_bytes());
    }

    loop {
        unsafe { riscv::asm::wfi() };
    }
}

fn increment_mepc() {
    let mut mepc = register::mepc::read();
    let instr = unsafe { core::ptr::read_volatile(mepc as *const u8) };
    if instr & 0b11 == 0b11 {
        mepc += 4; // Non-compressed instr
    } else {
        mepc += 2; // Compressed instr
    }
    register::mepc::write(mepc);
}

#[panic_handler]
unsafe fn panic_handler(_panic: &core::panic::PanicInfo<'_>) -> ! {
    // SAFETY: Because we build with panic_immediate_abort, this is never actually called
    unsafe { unreachable_unchecked() }
}
