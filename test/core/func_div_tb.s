// clang --target=riscv64 -march=rv64gc x.s -o x.o -nostdlib -mno-relax -Wl,--section-start=.text=0 && objdump x.o -D -M numeric
.global _start

.section .text
.org 0

_start:
li x1, 0xFF22334455667788
li x2, 0xAABB0077
li x3, 0x1234

div x4, x1, x2
divu x5, x1, x2
rem x6, x1, x2
remu x7, x1, x2
divw x8, x1, x2
divw x9, x2, x3
divuw x10, x1, x2
divuw x11, x2, x3
remw x12, x1, x2
remw x13, x2, x3
remuw x14, x1, x2
remuw x15, x2, x3

.div_by_zero:
div x16, x1, x0
divw x17, x1, x0
divu x18, x1, x0
divuw x19, x1, x0
rem x20, x1, x0
remw x21, x1, x0
remu x22, x1, x0
remuw x23, x1, x0

li x1, 0x8000000000000000
li x2, 0x80000000
li x3, 0xFFFFFFFFFFFFFFFF

.signed_overflow:
div x24, x1, x3
rem x25, x1, x3
divw x26, x2, x3
remw x27, x2, x3

.padding:
.4byte 0x00000000
.4byte 0x00000000




