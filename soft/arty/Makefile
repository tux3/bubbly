all: blink.bin

blink.bin: blink.elf
	llvm-objcopy -O binary blink.elf blink.bin

blink.elf: blink.o
	riscv64-unknown-elf-ld blink.o -o blink.elf

blink.o: blink.s
	clang --target=riscv64 -march=rv64ic blink.s -c -o blink.o

dump: blink.elf
	llvm-objdump -d blink.elf

clean:
	rm -f blink.bin blink.elf blink.o

