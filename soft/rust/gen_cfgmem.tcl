#vivado -notrace -nolog -nojournal -mode batch -source gen_cfgmem.tcl
write_cfgmem  -format mcs -size 16 -interface SPIx4 -loadbit {up 0x00000000 "../../build/bubbly.runs/impl_1/top.bit" } -loaddata {up 0x00400000 "rust.bin" } -force -file "cfgmem.mcs"
