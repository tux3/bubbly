
module pll(
    input CLK100MHZ,
    input RSTN,
    output clk,
    output reg rst
);
    
logic [4:0] rstn_buf = '0;
wire locked;
wire clkfb;

always_ff @(posedge clk) begin
    rstn_buf <= {rstn_buf, locked & RSTN};
    rst <= ~&{rstn_buf, locked & RSTN};
end

// Note: Set to DIVCLK_DIVIDE(5) CLKOUT0_DIVIDE(125) if trying to probe w/ slow logic analyzer...
PLLE2_BASE #(
    .BANDWIDTH("OPTIMIZED"),   // Jitter programming (OPTIMIZED, HIGH, LOW)
    .CLKFBOUT_MULT(40),     // Multiply value for all CLKOUT (2.000-64.000).
    .CLKFBOUT_PHASE(0.0),      // Phase offset in degrees of CLKFB (-360.000-360.000).
    .CLKIN1_PERIOD(10.00),       // Input clock period in ns to ps resolution (i.e. 33.333 is 30 MHz).
    // CLKOUT0_DIVIDE - CLKOUT6_DIVIDE: Divide amount for each CLKOUT (1-128)
    .CLKOUT0_DIVIDE(20),
    // CLKOUT0_DUTY_CYCLE - CLKOUT6_DUTY_CYCLE: Duty cycle for each CLKOUT (0.01-0.99).
    .CLKOUT0_DUTY_CYCLE(0.5),
    // CLKOUT0_PHASE - CLKOUT6_PHASE: Phase offset for each CLKOUT (-360.000-360.000).
    .CLKOUT0_PHASE(0.0),
    .DIVCLK_DIVIDE(4),         // Master division value (1-106)
    .REF_JITTER1(0.0),         // Reference input jitter in UI (0.000-0.999).
    .STARTUP_WAIT("TRUE")     // Delays DONE until MMCM is locked (FALSE, TRUE)
) MMCME2_BASE_inst (
    // Clock Outputs: 1-bit (each) output: User configurable clock outputs
    .CLKOUT0(clk),     // 1-bit output: CLKOUT0
    .CLKOUT1(),   // 1-bit output: CLKOUT1
    .CLKOUT2(),   // 1-bit output: CLKOUT2
    .CLKOUT3(),   // 1-bit output: CLKOUT3
    .CLKOUT4(),   // 1-bit output: CLKOUT4
    .CLKOUT5(),   // 1-bit output: CLKOUT5
    // Status Ports: 1-bit (each) output: MMCM status ports
    .LOCKED(locked),       // 1-bit output: LOCK
    // Clock Inputs: 1-bit (each) input: Clock input
    .CLKIN1(CLK100MHZ),       // 1-bit input: Clock
    // Control Ports: 1-bit (each) input: MMCM control ports
    .RST('b0),             // 1-bit input: Reset
    .PWRDWN('b0),
    // Feedback Clocks
    .CLKFBOUT(clkfb), // 1-bit output: Feedback clock
    .CLKFBIN(clkfb)      // 1-bit input: Feedback clock
); 

endmodule
