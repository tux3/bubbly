`include "core/params.svh"
`include "axi/axi4lite.svh"

module func_wfi_blocking_tb;
    timeunit 100ns;
    timeprecision 10ns;

    bit clk = 0;
    bit rst = 0;

    // We don't enable interrupts, so with our implementation, WFI should block forever
    const logic [8*32-1:0] code_buf = {<<32{
        'b001100000101_10000_101_00000_1110011, // CSRRWI r0, 'h10, mtvec
        'b0001000_00101_00000_000_00000_1110011, // WFI
        'b000000000001_00000_000_11110_0010011, // ADDI r30, r0, 1 (fail flag 1)
        'b0000000_00000_00000_000_00000_1100011, // Fail infinite loop
        'b000000000001_00000_000_11111_0010011, // ADDI r31, r0, 1 (fail flag on trap)

        'b0000000_00000_00000_000_00000_1100011, // Infinite loop
        'b00000000000000000000_00000_0000000,  // Padding (prevent out of bounds read asserts by the ifetch running ahead)
        'b00000000000000000000_00000_0000000
    }};

    wire cs, sclk, si, so, wp, hold, capture_clk;
    qspi_flash_buffer_mock #(.BUFFER_SIZE($bits(code_buf))) qspi_flash_mock(
        .*,
        .buffer(code_buf)
    );

    wire [`XLEN-1:0] reg_pc;
    wire [4:0] reg_read_sel;
    wire [`XLEN-1:0] reg_read_data;

    basic_soc soc(
        .clk,
        .rst,

        .cs,
        .sclk,
        .capture_clk,
        .si,
        .so,
        .wp,
        .hold,

        .reg_pc,
        .reg_read_sel,
        .reg_read_data,
        .fetch_instr(),
        .gpio_outputs()
    );

    initial begin
        #0 rst = 1;
        #2 rst = 0;
    end

    initial forever
        #0.5 clk = !clk;

    initial begin
        #2; @(posedge clk);

        #500;

        assert($signed(soc.core.regs.xreg[30]) == 0);
        assert($signed(soc.core.regs.xreg[31]) == 0);
        for (int i=1; i<30; i+=1)
            assert(soc.core.regs.xreg[i] == '0);
        $finish();
    end
endmodule
