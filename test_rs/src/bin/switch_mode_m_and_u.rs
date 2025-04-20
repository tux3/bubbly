#![no_std]
#![no_main]
#![feature(naked_functions)]
#![feature(macro_metavar_expr_concat)]

use core::arch::asm;
use riscv::interrupt::Exception;
use riscv::register::mstatus::MPP;
use test_rs::{debug_println, fatal, halt, increment_mepc, report_fail, report_success, set_direct_trap_handler, trap_handler, trap_save_and_call};

#[unsafe(no_mangle)]
pub unsafe extern "C" fn main() {
    set_direct_trap_handler(trap_handler_from_m);
    unsafe { riscv::asm::ecall() };
    debug_println("Back from trap handler from M");

    // The second trap handler expects to be called from user mode
    set_direct_trap_handler(trap_handler_from_u);
    unsafe {
        riscv::register::mscratch::write(0);
        riscv::register::mstatus::set_mpp(MPP::User);
        riscv::register::mepc::write(user_func as usize);
        asm!("mret", options(noreturn));
    };

    #[allow(unreachable_code)]
    debug_println("unreachable code after mret from main");
    report_fail();
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn user_func() {
    debug_println("Reached user_func");

    unsafe { riscv::asm::ecall() };
    debug_println("Back from trap handler after user ecall");

    riscv::asm::wfi();
    debug_println("Back from trap handler after illegal user WFI");

    riscv::register::mstatus::read();
    debug_println("Back from trap handler after illegal user CSR access");

    report_success();
    halt();
}

trap_handler!(trap_handler_from_m, {
    debug_println("Trap handler from M");

    let mcause = riscv::register::mcause::read();
    if mcause.is_interrupt() {
        fatal("Unexpected interrupt!")
    }

    let mcause = mcause.code();
    if mcause == Exception::MachineEnvCall as usize {
        increment_mepc();
    } else {
        fatal("Expected MachineEnvCall")
    }
});

trap_handler!(trap_handler_from_u, {
    debug_println("Trap handler from U");

    let mcause = riscv::register::mcause::read();
    if mcause.is_interrupt() {
        fatal("Unexpected interrupt!")
    }

    let mcause = mcause.code();
    if mcause == Exception::UserEnvCall as usize {
        increment_mepc();
        set_direct_trap_handler(trap_handler_from_u_expect_illegal_instruction);
    } else {
        fatal("Expected UserEnvCall")
    }
});

trap_handler!(trap_handler_from_u_expect_illegal_instruction, {
    debug_println("Trap handler from U, expecting illegal instruction");

    let mcause = riscv::register::mcause::read();
    if mcause.is_interrupt() {
        fatal("Unexpected interrupt!")
    }

    let mcause = mcause.code();
    if mcause == Exception::IllegalInstruction as usize {
        increment_mepc();
        let mscratch = riscv::register::mscratch::read() + 1;
        unsafe { riscv::register::mscratch::write(mscratch); }

        if mscratch > 2 {
            fatal("Expected only 2 illegal instructions from user code, but got more")
        }
    } else {
        fatal("Expected IllegalInstruction")
    }
});
