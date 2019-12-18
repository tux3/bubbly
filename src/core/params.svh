// Global parameters for the core

`ifndef _CORE_PARAMS_INCLUDE
`define _CORE_PARAMS_INCLUDE

`define ALEN 26 // Maximum address size. Constrained by tag size we can fit in a cache entry with the iCE40's BRAM!
`define XLEN 64 // Register size
`define ILEN 32 // Maximum instruction size

`endif // _CORE_PARAMS_INCLUDE
