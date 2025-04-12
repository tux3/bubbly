## Bubbly CPU

This is a 64-bit RISC-V CPU. It supports the RV64IMACZicsr_Zbb_Zbs ISA and extensions. And yes... the pipeline is full of bubbles.  
It passes the [RISC-V Architecture Tests](https://github.com/riscv-non-isa/riscv-arch-test), but most likely still contains bugs, it's just a hobby CPU!  

The core has small data and instruction caches, and 43 usable physical address bits.  
The ifetch follows simple branches, but the branch prediction is limited to considering all backwards conditional branches as taken.  
As there is only a single core, we get to support the A extension for atomic instructions for free.  

We don't yet have an MMU or a DDR DRAM controller yet. But, hey, how hard could it be? =)

## Blinkenligths

![board photo](img/board_ethernet_photo.jpg)

Pictured is the CPU running a simple server (in Rust) that receives an updated version of itself as a payload over the network and boots it.

## Third-party code

The project includes some third-party code for specific components:
- [verilog-ethernet](https://github.com/alexforencich/verilog-ethernet/)'s MAC/PHY modules and AXI interfaces to it
- [wb2axip](https://github.com/ZipCPU/wb2axip)'s AXI4-Lite crossbar 

Due to the state of verilog tooling and package management being what it is,
instead of declaring a dependency on these, we currently just embed a copy of the third party modules we use under the src folder.  
