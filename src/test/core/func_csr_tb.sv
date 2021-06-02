`include "../../core/params.svh"
`include "../../axi/axi4lite.svh"

module func_csr_tb;
    timeunit 100ns;
    timeprecision 10ns;

    bit clk = 0;
    bit rst = 0;

    const logic [26*32-1:0] code_buf = {<<32{
        'b000000010000_00000_011_00001_0000011, // LD r1, r0, h10
        'b000000011000_00000_011_00010_0000011, // LD r2, r0, h18
        'b000000100000_00000_000_00000_1100111, // JALR r0, h20
        'h00000000,
        'hAADDEEFF, 'h11223344,
        'hBBCC00EE, 'h22331144,

        'b001101000000_11111_110_00000_1110011, // CSRRSI r0, 11111, mscratch
        'b001101000000_00000_110_00011_1110011, // CSRRSI r3, 0, mscratch
        'b001101000000_00111_111_00100_1110011, // CSRRCI r4, 00111, mscratch
        'b001101000000_10001_110_00101_1110011, // CSRRSI r5, 10001, mscratch
        'b001101000000_00000_111_00110_1110011, // CSRRCI r6, 0, mscratch

        'b001101000000_00110_011_00110_1110011, // CSRRC r6, r6, mscratch
        'b001101000000_00001_010_00111_1110011, // CSRRS r7, r1, mscratch
        'b001101000000_00010_010_01000_1110011, // CSRRS r8, r2, mscratch
        'b001101000000_00001_011_01001_1110011, // CSRRC r9, r1, mscratch
        'b001101000000_00010_011_01010_1110011, // CSRRC r10, r2, mscratch

        'b001101000000_11111_101_01011_1110011, // CSRRWI r11, 11111, mscratch
        'b001101000000_00000_101_01100_1110011, // CSRRWI r12, 0, mscratch
        'b001101000000_00001_001_01101_1110011, // CSRRW r13, r1, mscratch
        'b001101000000_00000_001_01110_1110011, // CSRRW r14, r0, mscratch
        'b001101000000_00000_001_01111_1110011, // CSRRW r15, r0, mscratch

        'b11111111110111111111_00000_1101111,   // Inf. loop
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
        .reg_read_data
    );

    initial begin
        #0 rst = 1;
        #2 rst = 0;
    end

    initial forever
        #0.5 clk = !clk;

    initial begin
        integer xlen = `XLEN; // Avoid "comparison is constant" warning
        if (xlen == 32) begin
            $warning("Test skipped in 32-bit mode!");
            $finish();
        end

        #2; @(posedge clk);

        #750;

        assert($signed(soc.core.regs.xreg[01]) == 64'sh11223344AADDEEFF);
        assert($signed(soc.core.regs.xreg[02]) == 64'sh22331144BBCC00EE);

        assert($signed(soc.core.regs.xreg[03]) == 64'sb11111);
        assert($signed(soc.core.regs.xreg[04]) == 64'sb11111);
        assert($signed(soc.core.regs.xreg[05]) == 64'sb11000);
        assert($signed(soc.core.regs.xreg[06]) == 64'sb11001);
        assert($signed(soc.core.regs.xreg[07]) == 64'sh0);
        assert($signed(soc.core.regs.xreg[08]) == 64'sh11223344AADDEEFF);
        assert($signed(soc.core.regs.xreg[09]) == 64'sh33333344BBDDEEFF);
        assert($signed(soc.core.regs.xreg[10]) == 64'sh2211000011000000);
        assert($signed(soc.core.regs.xreg[11]) == 64'sh0);
        assert($signed(soc.core.regs.xreg[12]) == 64'sb11111);
        assert($signed(soc.core.regs.xreg[13]) == 64'sh0);
        assert($signed(soc.core.regs.xreg[14]) == 64'sh11223344AADDEEFF);
        assert($signed(soc.core.regs.xreg[15]) == 64'sh0);
        for (int i=16; i<32; i+=1)
            assert(soc.core.regs.xreg[i] == '0);
        $finish();
    end
endmodule
