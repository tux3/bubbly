`include "core/params.svh"
`include "axi/axi4lite.svh"

// This tests the 32bit (W) versions of RV64I instructions
module func_int_w_tb;
    timeunit 100ns;
    timeprecision 10ns;

    bit clk = 0;
    bit rst = 0;

    const logic [20*32-1:0] code_buf = {<<32{
        'b000000010000_00000_011_00001_0000011, // LD r1, r0, h10
        'b000000011000_00000_011_00010_0000011, // LD r2, r0, h18
        'b000000100000_00000_000_00000_1100111, // JALR r0, h20 (why not JAL? screw the JAL U-type immediate encoding)
        'h00000000, // We load some 64bit data intentionally to check the 32bit instructions don't accidentally use the upper data
        'hAADDEEFF, 'h11223344,
        'hBBCC00EE, 'h22331144,

        'b0000000_00010_00001_000_00011_0111011, // ADDW r3, r1, r2
        'b0100000_00010_00001_000_00100_0111011, // SUBW r4, r1, r2

        'b000000001000_00000_000_00111_0011011, // ADDIW r7, r0, 8
        'b0000000_00111_00100_001_00101_0111011, // SLLW r5, r4, r7
        'b0100000_00111_00100_101_00110_0111011, // SRAW r6, r4, r7
        'b0000000_00111_00100_101_00111_0111011, // SRLW r7, r4, r7

        'b0000000_01000_00001_001_01000_0011011, // SLLIW r8, r1, 8
        'b0000000_01000_00001_101_01001_0011011, // SRLIW r9, r1, 8
        'b0100000_01000_00001_101_01010_0011011, // SRAIW r10, r1, 8

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
        integer xlen = `XLEN; // Avoid "comparison is constant" warning
        if (xlen == 32) begin
            $warning("Test skipped in 32-bit mode!");
            $finish();
        end

        #2; @(posedge clk);

        #500;

        assert($signed(soc.core.regs.xreg[01]) == 64'sh11223344AADDEEFF);
        assert($signed(soc.core.regs.xreg[02]) == 64'sh22331144BBCC00EE);

        assert($signed(soc.core.regs.xreg[03]) == 32'sh66A9EFED);
        assert($signed(soc.core.regs.xreg[04]) == 32'shEF11EE11);
        assert($signed(soc.core.regs.xreg[05]) == 32'sh11EE1100);
        assert($signed(soc.core.regs.xreg[06]) == 32'shFFEF11EE);
        assert($signed(soc.core.regs.xreg[07]) == 32'sh00EF11EE);
        assert($signed(soc.core.regs.xreg[08]) == 32'shDDEEFF00);
        assert($signed(soc.core.regs.xreg[09]) == 32'sh00AADDEE);
        assert($signed(soc.core.regs.xreg[10]) == 32'shFFAADDEE);
        for (int i=11; i<32; i+=1)
            assert(soc.core.regs.xreg[i] == '0);
        $finish();
    end
endmodule
