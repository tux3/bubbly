.PHONY: always-build

all: cfgmem.mcs


cfgmem.mcs: rust.bin gen_cfgmem.tcl ../../build/bubbly.runs/impl_1/top.bit
	vivado -notrace -nolog -nojournal -mode batch -source gen_cfgmem.tcl

rust.bin: target/riscv64imac-unknown-none-elf/release/rust
	llvm-objcopy -O binary $^ $@

target/riscv64imac-unknown-none-elf/release/rust: always-build
	cargo build --release

always-build:


