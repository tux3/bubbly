`include "../../core/params.svh"
`include "../../axi/axi4lite.svh"

module func_int_bypass_tb;
    timeunit 100ns;
    timeprecision 10ns;

    bit clk = 0;
    bit rst = 0;

    const logic [15*32-1:0] code_buf = {<<32{
        'b111111111111_00000_000_00001_0010011, // ADDI r1, r0, -1
        'b111111111111_00001_100_00010_0010011, // XORI r2, r1, -1
        'b010000000100_00001_101_00011_0010011, // SRAI r3, r1, 4
        'b000000000100_00001_101_00100_0010011, // SRLI r4, r1, 4
        'b000001010101_00100_111_00101_0010011, // ANDI r5, r4, 0x55
        'b000000001100_00101_001_00110_0010011, // SLLI r6, r5, 12
        'b000000100010_00101_110_00111_0010011, // ORI r7, r5, 0x22
        'b100000000000_00011_010_01000_0010011, // SLTI r8, r3, -(2**XLEN-1)
        'b100000000000_00011_011_01001_0010011, // SLTIU r9, r3, 2**(XLEN-1)
        'b100000000000_00100_010_01010_0010011, // SLTI r10, r4, -(2**XLEN-1)
        'b100000000000_00100_011_01011_0010011, // SLTIU r11, r4, 2**(XLEN-1)
        'b000000000000000_00000_01100_0010111, // AUIPC r12, 0
        'b000000000100_01100_000_00000_1100111, // JALR r12, 4
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

        assert($signed(soc.core.regs.xreg[01]) == 32'shFFFFFFFF);
        assert($signed(soc.core.regs.xreg[02]) == 32'sh00000000);
        assert($signed(soc.core.regs.xreg[03]) == 32'shFFFFFFFF);
        assert($signed(soc.core.regs.xreg[04]) == ({`XLEN{1'b1}} >> 4));
        assert($signed(soc.core.regs.xreg[05]) == 32'sh00000055);
        assert($signed(soc.core.regs.xreg[06]) == 32'sh00055000);
        assert($signed(soc.core.regs.xreg[07]) == 32'sh00000077);
        assert($signed(soc.core.regs.xreg[08]) == 32'sh00000000);
        assert($signed(soc.core.regs.xreg[09]) == 32'sh00000000);
        assert($signed(soc.core.regs.xreg[10]) == 32'sh00000000);
        assert($signed(soc.core.regs.xreg[11]) == 32'sh00000001);
        assert($signed(soc.core.regs.xreg[12]) == 32'sh0000002C);
        for (int i=13; i<32; i+=1)
            assert(soc.core.regs.xreg[i] == '0);
        $finish();
    end
endmodule
