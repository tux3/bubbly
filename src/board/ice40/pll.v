// Maps 16MHZ -> 32MHZ, RESETB pin + LOCK signal -> Buffered RST signal
// Note that the PLL doesn't officially support generating anything less than 16MHz, sounds like it's just stable enough for testing.
// Empirically, setting DIVQ at 7 with a high DIVF seems to give horrible broken output, but using a DIVQ of 6 with a lower DIVF works okay well under 16MHz

module pll(input clk_in, input resetb_in, output clk_out, output reg reset_out);

wire locked;
logic [4:0] resetb_buf = '0;

// Fout = Fin*(DIVF+1)/(2^DIVQ)
SB_PLL40_CORE #(
    .FEEDBACK_PATH("SIMPLE"),
    .DIVR(4'b0000),
    .DIVF(7'b0111111),
    .DIVQ(3'b101),
    .FILTER_RANGE(3'b001)
) pll_inst (
	.BYPASS(1'b0),
	.EXTFEEDBACK(1'b0),
    .DYNAMICDELAY(8'b0),
    .LATCHINPUTVALUE(1'b0),
    .SDI(1'b0),
    .SCLK(1'b0),
    .REFERENCECLK(clk_in),
    .RESETB(resetb_in),
    .PLLOUTCORE(clk_out),
    .LOCK(locked)
);

always @(posedge clk_out) begin
    resetb_buf <= {resetb_buf, locked & resetb_in};
    reset_out <= ~&{resetb_buf, locked & resetb_in};
end    

endmodule