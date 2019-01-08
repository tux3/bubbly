// Maps 16MHZ -> 8MHZ, RESETB pin + LOCK signal -> Buffered RST signal
// Note that the PLL doesn't officially support generating anything less than 16MHz, but my QSPI Flash driver currently won't run above 10MHz!
// Empirically, setting DIVQ at 7 with a high DIVF seems to give horrible broken output, but using a DIVQ of 6 with a lower DIVF works okay well under 16MHz

module pll(input clk_in, input resetb_in, output clk_out, output reset_out);

wire locked;
reg [3:0] reset_buf = 0;
assign reset_out = |(reset_buf);

// Fout = Fin*(DIVF+1)/(2^DIVQ)
SB_PLL40_CORE #(
    .FEEDBACK_PATH("SIMPLE"),
    .DIVR(4'b0000),
    .DIVF(7'b0111111),
    .DIVQ(3'b110),
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

always @(posedge clk_out)
    reset_buf <= {reset_buf, !(locked & resetb_in)};

endmodule
