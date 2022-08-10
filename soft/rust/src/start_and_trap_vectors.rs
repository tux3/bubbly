use crate::ethernet_mmio::eth_mmio_set_tx_src_mac;
use crate::{log_msg_udp, main, netboot, GPIO_BASE, SRAM_BASE, SRAM_SIZE};
use core::hint::unreachable_unchecked;
use core::sync::atomic::{AtomicBool, Ordering};
use riscv::register::{self, mtvec::TrapMode};

const BOARD_MAC_ADDR: u64 = 0x00183e035117;
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

    unsafe {
        core::arch::asm!("csrrw x0, mie, {}", in(reg) 0x000F_0000);
        register::mstatus::set_mie();
    }

    main()
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
    Platform0 = 16,
    Platform1 = 17,
    Platform2 = 18,
    Platform3 = 19,
}

#[link_section = ".trap_handler"]
#[no_mangle]
unsafe extern "C" fn trap_handler() {
    let mcause = register::mcause::read();
    if mcause.is_interrupt() {
        if mcause.code() >= InterruptCause::Platform0 as usize
            && mcause.code() <= InterruptCause::Platform3 as usize
        {
            log_msg_udp("Received platform interrupt!");
            log_msg_udp(register::mepc::read().to_be_bytes());
        } else {
            log_msg_udp("Unexpected interrupt, continuing");
        }
        log_msg_udp(mcause.bits().to_be_bytes());

        unsafe {
            core::arch::asm!("csrrc x0, mip, {clear_mask}", clear_mask = in(reg) (1u64 << mcause.code()))
        };
        return;
    }

    let trap_led = (GPIO_BASE + 2) as *mut u8;
    unsafe { core::ptr::write_volatile(trap_led, 1) };

    let mcause = mcause.code();
    if mcause == ExceptionCause::ECallMMode as usize {
        log_msg_udp("ECALL received");
        increment_mepc();
        return;
    }

    if HAS_FAULTED.swap(true, Ordering::AcqRel) {
        log_msg_udp("NESTED TRAP");
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
