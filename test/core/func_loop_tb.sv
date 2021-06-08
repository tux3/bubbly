`include "core/params.svh"
`include "axi/axi4lite.svh"

module func_loop_tb;
    timeunit 100ns;
    timeprecision 10ns;

    bit clk = 0;
    bit rst = 0;

    const logic [9*32-1:0] code_buf = {<<32{
        'b000000000000_00000_000_00001_0010011, // ADDI r1, r0, 0
        'b000000100000_00000_000_00010_0010011, // ADDI r2, r0, 0x20
        // Loop start
        'b000000000001_00001_000_00001_0010011, // ADDI r1, r1, 1
        'b111111111111_00010_000_00010_0010011, // ADDI r2, r2, -1
        'b1111111_00000_00010_001_11001_1100011, // BNE r2, r0, -8
        'b000000000001_00000_000_00011_0010011, // ADDI r3, r0, 1
        'b0000000_00000_00000_000_00000_1100011, // BEQ r0, r0, 0 (success infinite loop)
        'b00000000000000000000_00000_0000000,  // Padding (prevent out of bounds read asserts by the ifetch running ahead)
        'b00000000000000000000_00000_0000000
    }};

    wire cs, sclk, si, so, wp, hold;
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

        assert($signed(soc.core.regs.xreg[1]) == 'h20);
        assert($signed(soc.core.regs.xreg[2]) == 'h0);
        assert($signed(soc.core.regs.xreg[3]) == 'h1);
        for (int i=4; i<32; i+=1)
            assert(soc.core.regs.xreg[i] == '0);
        $finish();
    end
endmodule
