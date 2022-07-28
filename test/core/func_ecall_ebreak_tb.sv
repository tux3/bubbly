`include "core/params.svh"
`include "axi/axi4lite.svh"

module func_ecall_ebreak_tb;
    timeunit 100ns;
    timeprecision 10ns;

    bit clk = 0;
    bit rst = 0;

    const logic [16*32-1:0] code_buf = {<<32{
        'b001100000101_01100_101_00000_1110011, // CSRRWI r0, 'hC, mtvec
        'b000000000000_00000_000_00000_1110011, // ECALL
        'b0000000_00000_00000_000_00000_1100011, // Fail infinite loop
        'b000000000001_00000_000_11111_0010011, // ADDI r31, r0, 1 (success flag 1)
        'b001101000010_00000_101_00001_1110011, // CSRRWI r1, 0, mcause

        'b000000100100_00000_000_00010_0010011, // ADDI r2, r0, 'h24
        'b001100000101_00010_001_00000_1110011, // CSRRW r0, r2, mtvec
        'b000000000001_00000_000_00000_1110011, // EBREAK
        'b0000000_00000_00000_000_00000_1100011, // Fail infinite loop
        'b000000000001_00000_000_11110_0010011, // ADDI r30, r0, 1 (success flag 2)
        'b001101000010_00000_101_00010_1110011, // CSRRWI r2, 0, mcause
        'b001101000011_00000_101_00011_1110011, // CSRRWI r3, 0, mtval
        'b001101000001_00000_101_00100_1110011, // CSRRWI r4, 0, mepc

        'b0000000_00000_00000_000_00000_1100011, // Success infinite loop
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

        assert($signed(soc.core.regs.xreg[1]) == trap_causes::EXC_ENV_CALL_MMODE);
        assert($signed(soc.core.regs.xreg[2]) == trap_causes::EXC_BREAKPOINT);
        assert($signed(soc.core.regs.xreg[3]) == '0);
        assert($signed(soc.core.regs.xreg[4]) == 'h1C);
        assert($signed(soc.core.regs.xreg[30]) == 1);
        assert($signed(soc.core.regs.xreg[31]) == 1);
        for (int i=5; i<30; i+=1)
            assert(soc.core.regs.xreg[i] == '0);
        $finish();
    end
endmodule
