parameter FIXP_FRACT_BITS = 64;

// Fixed-point multiplication is used for our Newton-Ralphson divider
// We have 64 fractional bits, and between 2 and 64 integer bits
// Because the divider rescales inputs, only the 2nd argument needs a full 64+64 bits 
module fixp_mult(input clk, input [65:0] a, input [127:0] b, output [127:0] r);
    reg [128+FIXP_FRACT_BITS-1:0] a_bl;
    reg [64+FIXP_FRACT_BITS-1:0] a_bh;
    reg b_signed;
    wire [128+FIXP_FRACT_BITS-1:0] a_b = a_bl + {a_bh, 64'b0};
    always @(posedge clk) begin
        a_bl <= a * b[63:0];
        a_bh <= a * b[127:64];
        b_signed <= b[127];
    end

    assign r = {(b_signed ? {64{1'b1}} : a_b[FIXP_FRACT_BITS + 64 +: 64]), a_b[FIXP_FRACT_BITS +: 64]};
endmodule
