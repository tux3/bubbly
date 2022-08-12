.PHONY: always-build flash_cfgmem ethboot_rust

all: cfgmem.mcs


cfgmem.mcs: rust.bin gen_cfgmem.tcl ../../build/bubbly.runs/impl_1/top.bit
	vivado -notrace -nolog -nojournal -mode batch -source gen_cfgmem.tcl

rust.bin: target/riscv64imac-unknown-none-elf/release/rust
	llvm-objcopy -O binary $^ $@

target/riscv64imac-unknown-none-elf/release/rust: always-build
	cargo build --release

always-build:
	

flash_cfgmem: cfgmem.mcs cfgmem.prm
	../../tools/flash_cfgmem.tcl cfgmem.mcs cfgmem.prm
	../../tools/boot_hw.tcl

ethboot_rust: rust.bin
	cd ../../tools/ethboot && cargo run -- -t bubbly.local -p ${PWD}/rust.bin
