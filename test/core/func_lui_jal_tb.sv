`include "core/params.svh"
`include "axi/axi4lite.svh"

module func_lui_jal_tb;
    timeunit 100ns;
    timeprecision 10ns;

    bit clk = 0;
    bit rst = 0;

    const logic [5*32-1:0] code_buf = {<<32{
        'b10101011110011011110_00010_0110111, // LUI r2, 0xABCDE000
        'b11111111110111111111_00001_1101111, // JAL r1, -4
        'b11111111111111111111_00010_0110111, // LUI r2, 0xFFFFF000 (never reached)
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

        assert($signed(soc.core.regs.xreg[1]) == 32'sh00000008);
        assert($signed(soc.core.regs.xreg[2]) == 32'shABCDE000);
        for (int i=3; i<32; i+=1)
            assert(soc.core.regs.xreg[i] == '0);
        $finish();
    end
endmodule
