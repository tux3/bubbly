// clang --target=riscv64 -march=rv64gc x.s -o x.o -nostdlib -mno-relax -Wl,--section-start=.text=0 && objdump x.o -D -M numeric
.global _start

.section .text
.org 0

_start:
li x1, 0xFF22334455667788
li x2, 0xAABB0077
li x3, 0x87654321

mul x4, x1, x2
mulh x5, x1, x2
mulhu x6, x1, x2
mulhsu x7, x1, x2
mulhsu x8, x2, x1
mulw x9, x1, x2
mulw x10, x1, x3
mulh x11, x1, x1

.padding:
.4byte 0x00000000
.4byte 0x00000000



