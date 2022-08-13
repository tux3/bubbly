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
`define PLATFORM_INTR_LEN 4
`define INTR_LEN 16 + `PLATFORM_INTR_LEN

`define RESET_PC '0

`define MVENDORID 32'h0
`define MARCHID 64'h0
`define MIMPID 64'h0

`endif // _CORE_PARAMS_INCLUDE
