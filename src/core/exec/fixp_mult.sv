parameter FIXP_FRACT_BITS = 64;

// Fixed-point multiplication is used for our Newton-Ralphson divider
// We have 64 fractional bits, and between 2 and 64 integer bits
// Because the divider rescales inputs, only the 2nd argument needs a full 64+64 bits 
module fixp_mult(input [65:0] a, input [127:0] b, output [127:0] r);
    wire [128+FIXP_FRACT_BITS-1:0] tmp = a * b;
    assign r = {(b[127] ? {64{1'b1}} : tmp[FIXP_FRACT_BITS + 64 +: 64]), tmp[FIXP_FRACT_BITS +: 64]};
endmodule
