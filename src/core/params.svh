// Global parameters for the core

`ifndef _CORE_PARAMS_INCLUDE
`define _CORE_PARAMS_INCLUDE

`define ALEN 42 // Maximum usable address size. Constrained by the tag size in our cache entries
`define XLEN 64 // Register size
`define ILEN 32 // Maximum instruction size

`define RESET_PC '0

`endif // _CORE_PARAMS_INCLUDE
