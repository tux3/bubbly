
module pll(
    input CLK100MHZ,
    input RSTN,
    output clk,
    output reg rst,
    output flash_capture_clk,
    output eth_ref_clk,
    output mtime_clk
);

wire mtime_clk_raw;

logic [7:0] rstn_buf = '0;
wire locked_fast, locked_slow;
wire clkfb_fast, clkfb_slow;

always_ff @(posedge clk) begin
    if (!locked_fast || !locked_slow || !RSTN)
        rstn_buf <= '0;
    else
        rstn_buf <= {rstn_buf, locked_fast & locked_slow & RSTN};
    rst <= ~&{rstn_buf, locked_fast & locked_slow & RSTN};
end

// Note: Set to DIVCLK_DIVIDE(4) CLKOUT{0,1}_DIVIDE(80) for slow logic analyzer (16.25MHz)
PLLE2_BASE #(
    .BANDWIDTH("OPTIMIZED"),   // Jitter programming (OPTIMIZED, HIGH, LOW)
    .CLKFBOUT_MULT(52),     // Multiply value for all CLKOUT (2.000-64.000).
    .CLKFBOUT_PHASE(0.0),      // Phase offset in degrees of CLKFB (-360.000-360.000).
    .CLKIN1_PERIOD(10.00),       // Input clock period in ns to ps resolution (i.e. 33.333 is 30 MHz).
    // CLKOUT0_DIVIDE - CLKOUT6_DIVIDE: Divide amount for each CLKOUT (1-128)
    .CLKOUT0_DIVIDE(20),
    .CLKOUT1_DIVIDE(20),
    // CLKOUT0_DUTY_CYCLE - CLKOUT6_DUTY_CYCLE: Duty cycle for each CLKOUT (0.01-0.99).
    .CLKOUT0_DUTY_CYCLE(0.5),
    .CLKOUT1_DUTY_CYCLE(0.3),
    // CLKOUT0_PHASE - CLKOUT6_PHASE: Phase offset for each CLKOUT (-360.000-360.000).
    .CLKOUT0_PHASE(0.0),
    .CLKOUT1_PHASE(148.5),
    .DIVCLK_DIVIDE(4),         // Master division value (1-106)
    .REF_JITTER1(0.0),         // Reference input jitter in UI (0.000-0.999).
    .STARTUP_WAIT("TRUE")     // Delays DONE until MMCM is locked (FALSE, TRUE)
) pll_fast (
    // Clock Outputs: 1-bit (each) output: User configurable clock outputs
    .CLKOUT0(clk),     // 1-bit output: CLKOUT0
    .CLKOUT1(flash_capture_clk),   // 1-bit output: CLKOUT1
    .CLKOUT2(),   // 1-bit output: CLKOUT2
    .CLKOUT3(),   // 1-bit output: CLKOUT3
    .CLKOUT4(),   // 1-bit output: CLKOUT4
    .CLKOUT5(),   // 1-bit output: CLKOUT5
    // Status Ports: 1-bit (each) output: MMCM status ports
    .LOCKED(locked_fast),       // 1-bit output: LOCK
    // Clock Inputs: 1-bit (each) input: Clock input
    .CLKIN1(CLK100MHZ),       // 1-bit input: Clock
    // Control Ports: 1-bit (each) input: MMCM control ports
    .RST('b0),             // 1-bit input: Reset
    .PWRDWN('b0),
    // Feedback Clocks
    .CLKFBOUT(clkfb_fast), // 1-bit output: Feedback clock
    .CLKFBIN(clkfb_fast)      // 1-bit input: Feedback clock
);

MMCME2_BASE #(
    .BANDWIDTH("OPTIMIZED"),   // Jitter programming (OPTIMIZED, HIGH, LOW)
    .CLKFBOUT_MULT_F(10),     // Multiply value for all CLKOUT (2.000-64.000).
    .CLKFBOUT_PHASE(0.0),      // Phase offset in degrees of CLKFB (-360.000-360.000).
    .CLKIN1_PERIOD(10.00),       // Input clock period in ns to ps resolution (i.e. 33.333 is 30 MHz).
    // CLKOUT0_DIVIDE - CLKOUT6_DIVIDE: Divide amount for each CLKOUT (1-128)
    .CLKOUT0_DIVIDE_F(40),
    .CLKOUT1_DIVIDE(125),
    // CLKOUT0_DUTY_CYCLE - CLKOUT6_DUTY_CYCLE: Duty cycle for each CLKOUT (0.01-0.99).
    .CLKOUT0_DUTY_CYCLE(0.5),
    .CLKOUT1_DUTY_CYCLE(0.5),
    // CLKOUT0_PHASE - CLKOUT6_PHASE: Phase offset for each CLKOUT (-360.000-360.000).
    .CLKOUT0_PHASE(0.0),
    .CLKOUT1_PHASE(0.0),
    .DIVCLK_DIVIDE(1),         // Master division value (1-106)
    .REF_JITTER1(0.0),         // Reference input jitter in UI (0.000-0.999).
    .STARTUP_WAIT("TRUE")     // Delays DONE until MMCM is locked (FALSE, TRUE)
) mmcm_slow (
    // Clock Outputs: 1-bit (each) output: User configurable clock outputs
    .CLKOUT0(eth_ref_clk),     // 1-bit output: CLKOUT0
    .CLKOUT0B(),
    .CLKOUT1(mtime_clk_raw),   // 1-bit output: CLKOUT1
    .CLKOUT1B(),
    .CLKOUT2(),   // 1-bit output: CLKOUT2
    .CLKOUT2B(),
    .CLKOUT3(),   // 1-bit output: CLKOUT3
    .CLKOUT3B(),
    .CLKOUT4(),   // 1-bit output: CLKOUT4
    .CLKOUT5(),   // 1-bit output: CLKOUT5
    .CLKOUT6(),   // 1-bit output: CLKOUT5
    // Status Ports: 1-bit (each) output: MMCM status ports
    .LOCKED(locked_slow),       // 1-bit output: LOCK
    // Clock Inputs: 1-bit (each) input: Clock input
    .CLKIN1(CLK100MHZ),       // 1-bit input: Clock
    // Control Ports: 1-bit (each) input: MMCM control ports
    .RST('b0),             // 1-bit input: Reset
    .PWRDWN('b0),
    // Feedback Clocks
    .CLKFBOUT(clkfb_slow), // 1-bit output: Feedback clock
    .CLKFBOUTB(),
    .CLKFBIN(clkfb_slow)      // 1-bit input: Feedback clock
);

BUFR #(
    .BUFR_DIVIDE(8)
) mtime_bufr (
    .I(mtime_clk_raw),
    .O(mtime_clk),
    .CE(1'b1),
    .CLR(1'b0)
);

endmodule
