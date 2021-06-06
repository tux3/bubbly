`include "../../core/params.svh"
`include "../../axi/axi4lite.svh"

module func_int_rtype_tb;
    timeunit 100ns;
    timeprecision 10ns;

    bit clk = 0;
    bit rst = 0;

    const logic [24*32-1:0] code_buf = {<<32{
        'b000000010000_00000_011_00001_0000011, // LD r1, r0, h10
        'b000000011000_00000_011_00010_0000011, // LD r2, r0, h18
        'b000000100000_00000_000_00000_1100111, // JALR r0, h20 (why not JAL? screw the JAL U-type immediate encoding)
        'h00000000,
        'hAADDEEFF, 'h11223344,
        'hBBCC00EE, 'h22331144,

        'b0000000_00010_00001_000_00011_0110011, // ADD r3, r1, r2
        'b0100000_00010_00001_000_00100_0110011, // SUB r4, r1, r2
        'b0000000_00010_00001_100_00101_0110011, // XOR r5, r1, r2
        'b0000000_00010_00001_110_00110_0110011, // OR r6, r1, r2
        'b0000000_00010_00001_111_00111_0110011, // AND r7, r1, r2

        'b000000000100_00000_000_01010_0010011, // ADDI r10, r0, 4
        'b0000000_01010_00100_001_01000_0110011, // SLL r8, r4, r10
        'b0100000_01010_00100_101_01001_0110011, // SRA r9, r4, r10
        'b0000000_01010_00100_101_01010_0110011, // SRL r10, r4, r10

        'b0000000_01000_00001_010_01011_0110011, // SLT r11, r1, r8
        'b0000000_00010_01001_010_01100_0110011, // SLT r12, r9, r2
        'b0000000_01000_00001_011_01101_0110011, // SLTU r13, r1, r8
        'b0000000_00010_01001_011_01110_0110011, // SLTU r14, r9, r2

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

        #750;

        assert($signed(soc.core.regs.xreg[01]) == 64'sh11223344AADDEEFF);
        assert($signed(soc.core.regs.xreg[02]) == 64'sh22331144BBCC00EE);

        assert($signed(soc.core.regs.xreg[03]) == 64'sh3355448966A9EFED);
        assert($signed(soc.core.regs.xreg[04]) == 64'shEEEF21FFEF11EE11);
        assert($signed(soc.core.regs.xreg[05]) == 64'sh331122001111EE11);
        assert($signed(soc.core.regs.xreg[06]) == 64'sh33333344BBDDEEFF);
        assert($signed(soc.core.regs.xreg[07]) == 64'sh00221144AACC00EE);
        assert($signed(soc.core.regs.xreg[08]) == 64'shEEF21FFEF11EE110);
        assert($signed(soc.core.regs.xreg[09]) == 64'shFEEEF21FFEF11EE1);
        assert($signed(soc.core.regs.xreg[10]) == 64'sh0EEEF21FFEF11EE1);
        assert($signed(soc.core.regs.xreg[11]) == 64'sh0);
        assert($signed(soc.core.regs.xreg[12]) == 64'sh1);
        assert($signed(soc.core.regs.xreg[13]) == 64'sh1);
        assert($signed(soc.core.regs.xreg[14]) == 64'sh0);
        for (int i=15; i<32; i+=1)
            assert(soc.core.regs.xreg[i] == '0);
        $finish();
    end
endmodule
