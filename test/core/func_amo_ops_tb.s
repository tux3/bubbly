// clang --target=riscv64 -march=rv64gc x.s -o x.o -nostdlib -mno-relax -Wl,--section-start=.text=0 && objdump x.o -D -M numeric
.global _start

.section .text
.org 0

_start:
addi x1, x0, %lo(.sram_ptr_ptr)
lr.d x2, (x1)
addi x1, x1, 0x8
lr.w x3, (x1)
addi x1, x1, -0x8

li x5, 20*8
add x5, x2, x5
li x4, 0x1A43C20F
.prepare_mem:
sd x4, (x5)
addi x5, x5, -8
bge x5, x2, .prepare_mem

li x4, 0x980C4A11A2E3B5F4
add x5, x0, x2

.run:
amoswap.w.aq x10, x4, (x5)
addi x5, x5, 8
amoadd.w.aq x11, x4, (x5)
addi x5, x5, 8
amoand.w.aq x12, x4, (x5)
addi x5, x5, 8
amoor.w.aq x13, x4, (x5)
addi x5, x5, 8
amoxor.w.aq x14, x4, (x5)
addi x5, x5, 8
amomax.w.aq x15, x4, (x5)
addi x5, x5, 8
amomaxu.w.aq x16, x4, (x5)
addi x5, x5, 8
amomin.w.aq x17, x4, (x5)
addi x5, x5, 8
amominu.w.aq x18, x4, (x5)

addi x5, x2, 0x50

amoswap.d.aq x20, x4, (x5)
addi x5, x5, 8
amoadd.d.aq x21, x4, (x5)
addi x5, x5, 8
amoand.d.aq x22, x4, (x5)
addi x5, x5, 8
amoor.d.aq x23, x4, (x5)
addi x5, x5, 8
amoxor.d.aq x24, x4, (x5)
addi x5, x5, 8
amomax.d.aq x25, x4, (x5)
addi x5, x5, 8
amomaxu.d.aq x26, x4, (x5)
addi x5, x5, 8
amomin.d.aq x27, x4, (x5)
addi x5, x5, 8
amominu.d.aq x28, x4, (x5)

.4byte 0x0000006f

.sram_ptr_ptr:
.4byte 0xAAAABBBB
.4byte 0xCCCCDDDD


