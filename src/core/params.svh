// Global parameters for the core

`ifndef _CORE_PARAMS_INCLUDE
`define _CORE_PARAMS_INCLUDE

// Maximum usable address size. Constrained by the tag size in our cache entries
`define ALEN 43
// Register size
`define XLEN 64
// Maximum instruction size
`define ILEN 32
// Number of interrupt bits
`define PLATFORM_INTR_LEN 5
`define INTR_LEN 16 + `PLATFORM_INTR_LEN

`define RESET_PC '0

`define MVENDORID 32'h0
`define MARCHID 64'h0
`define MIMPID 64'h0

`define WITH_BITMANIP_ZBA 1
`define WITH_BITMANIP_ZBB 1
`define WITH_BITMANIP_ZBS 1

`endif // _CORE_PARAMS_INCLUDE
