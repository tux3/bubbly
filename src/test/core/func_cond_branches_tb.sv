`include "../../core/params.svh"
`include "../../axi/axi4lite.svh"

module func_cond_branches_tb;
    timeunit 100ns;
    timeprecision 10ns;

    bit clk = 0;
    bit rst = 0;

    // This checks that we reach the end by taking all the branches correctly. Incorrect branches go to a bad infinite loop
    const logic [34*32-1:0] code_buf = {<<32{
        'b000000010000_00000_011_00001_0000011, // LD r1, r0, h10
        'b000000011000_00000_011_00010_0000011, // LD r2, r0, h18
        'b000000100000_00000_000_00000_1100111, // JALR r0, h20
        'b000000001100_00000_000_00000_1100111, // JALR r0, hC (failure infinite loop)
        'hAADDEEFF, 'h11223344,
        'hBBCC00EE, 'h99331144,

        'b0000000_00010_00001_000_01000_1100011, // BEQ r1, r2, FAIL
        'b0000000_00001_00001_000_01000_1100011, // BEQ r1, r1, OK
        'b000000001100_00000_000_00000_1100111, // JALR r0, hC (goto fail loop)

        'b0000000_00010_00010_001_01000_1100011, // BNE r2, r2, FAIL
        'b0000000_00001_00010_001_01000_1100011, // BNE r2, r1, OK
        'b000000001100_00000_000_00000_1100111, // JALR r0, hC (goto fail loop)

        'b0000000_00010_00001_100_01000_1100011, // BLT r1, r2, FAIL
        'b0000000_00001_00010_100_01000_1100011, // BLT r2, r1, OK
        'b000000001100_00000_000_00000_1100111, // JALR r0, hC (goto fail loop)

        'b0000000_00001_00010_110_01000_1100011, // BLTU r2, r1, FAIL
        'b0000000_00010_00001_110_01000_1100011, // BLTU r1, r2, OK
        'b000000001100_00000_000_00000_1100111, // JALR r0, hC (goto fail loop)

        'b0000000_00001_00010_101_01000_1100011, // BGE r2, r1, FAIL
        'b0000000_00001_00001_101_01000_1100011, // BGE r1, r1, OK
        'b000000001100_00000_000_00000_1100111, // JALR r0, hC (goto fail loop)
        'b0000000_00010_00001_101_01000_1100011, // BGE r1, r2, OK
        'b000000001100_00000_000_00000_1100111, // JALR r0, hC (goto fail loop)

        'b0000000_00010_00001_111_01000_1100011, // BGEU r1, r2, FAIL
        'b0000000_00001_00001_111_01000_1100011, // BGEU r1, r1, OK
        'b000000001100_00000_000_00000_1100111, // JALR r0, hC (goto fail loop)
        'b0000000_00001_00010_111_01000_1100011, // BGEU r2, r1, OK
        'b000000001100_00000_000_00000_1100111, // JALR r0, hC (goto fail loop)

        'b000000000001_00000_000_11111_0010011, // ADDI r31, r0, 1 (success flag)
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
        integer xlen = `XLEN; // Avoid "comparison is constant" warning
        if (xlen == 32) begin
            $warning("Test skipped in 32-bit mode!");
            $finish();
        end

        #2; @(posedge clk);

        #1000;

        assert(soc.core.regs.xreg[31] == 1);
        assert($signed(soc.core.regs.xreg[01]) == 64'sh11223344AADDEEFF);
        assert($signed(soc.core.regs.xreg[02]) == 64'sh99331144BBCC00EE);
        for (int i=3; i<31; i+=1)
            assert(soc.core.regs.xreg[i] == '0);
        $finish();
    end
endmodule
