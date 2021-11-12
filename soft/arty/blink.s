.equ    GPIO_BASE, 0x20000000000
.globl _start

_start:
	li s1, GPIO_BASE
	li s2, 1

loop:
	li s3, 4*1000*1000
	sb s2, 0(s1)
	xor s2, s2, 1

count_loop:
	add s3, s3, -1
    bnez s3, count_loop
	j loop

