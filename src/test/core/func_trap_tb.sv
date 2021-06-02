`include "../../core/params.svh"
`include "../../axi/axi4lite.svh"

module func_trap_tb;
    timeunit 100ns;
    timeprecision 10ns;

    bit clk = 0;
    bit rst = 0;

    const logic [19*32-1:0] code_buf = {<<32{
        'b001100000101_01110_101_00000_1110011, // CSRRWI r0, ('hC << 2 | 'b10), mtvec
        'b111111111111_00001_100_00010_1111111, // Invalid instruction at ifetch (overlong)
        'b0000000_00000_00000_000_00000_1100011, // Fail infinite loop
        'b000000000001_00000_000_11111_0010011, // ADDI r31, r0, 1 (success flag 1)

        'b001100000101_11111_101_00000_1110011, // CSRRWI r0, ('h1C << 2 | 'b11), mtvec
        'b111100010001_11111_101_00000_1110011, // Invalid instruction at exec (write ro CSR)
        'b0000000_00000_00000_000_00000_1100011, // Fail infinite loop
        'b000000000001_00000_000_11110_0010011, // ADDI r30, r0, 1 (success flag 2)

        'b001101000011_00000_101_11011_1110011, // CSRRWI r27, 0, mtval
        'b001101000001_00000_101_11100_1110011, // CSRRWI r28, 0, mepc
        'b001101000010_00000_101_11101_1110011, // CSRRWI r29, 0, mcause

        'b000000111100_00000_000_11010_0010011, // ADDI r26, r0, 'h3C
        'b001101000001_11010_001_00000_1110011, // CSRRW r0, r26, mepc
        'b0011000_00010_00000_000_00000_1110011, // MRET
        'b0000000_00000_00000_000_00000_1100011, // Fail infinite loop
        'b000000000001_00000_000_11010_0010011, // ADDI r26, r0, 1 (success flag 3)

        'b0000000_00000_00000_000_00000_1100011, // Success infinite loop
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

        assert($signed(soc.core.regs.xreg[26]) == 1);
        assert($signed(soc.core.regs.xreg[27]) == 'b111100010001_11111_101_00000_1110011);
        assert($signed(soc.core.regs.xreg[28]) == 'h14);
        assert($signed(soc.core.regs.xreg[29]) == trap_causes::EXC_ILLEGAL_INSTR);
        assert($signed(soc.core.regs.xreg[30]) == 1);
        assert($signed(soc.core.regs.xreg[31]) == 1);
        for (int i=1; i<26; i+=1)
            assert(soc.core.regs.xreg[i] == '0);
        $finish();
    end
endmodule
