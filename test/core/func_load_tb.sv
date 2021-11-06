`include "core/params.svh"
`include "axi/axi4lite.svh"

module func_load_tb;
    timeunit 100ns;
    timeprecision 10ns;

    bit clk = 0;
    bit rst = 0;

    const logic [14*32-1:0] code_buf = {<<32{
        'b000000101100_00000_000_00001_0010011, // ADDI r1, r0, data_addr
        'b000000000000_00001_000_00010_0000011, // LB r2, r1, 0
        'b000000000011_00001_000_00011_0000011, // LB r3, r1, 3
        'b000000000011_00001_100_00100_0000011, // LBU r4, r1, 3
        'b000000000110_00001_000_00101_0000011, // LB r5, r1, 6
        'b111111111100_00001_001_00110_0000011, // LH r6, r1, -4
        'b000000000000_00001_101_00111_0000011, // LHU r7, r1, 0
        'b000000000000_00001_010_01000_0000011, // LW r8, r1, 0
        'b000000000000_00001_110_01001_0000011, // LWU r9, r1, 0
        'b000000000100_00001_011_01010_0000011, // LD r10, r1, 4
        'b00000000000000000000_00001_1101111, // Inf. loop before data
        'h8A8FC3C7,
        'h017F423C,
        'h66778899
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

        #1000;

        assert($signed(soc.core.regs.xreg[2]) == 8'shC7);
        assert($signed(soc.core.regs.xreg[3]) == 8'sh8A);
        assert($signed(soc.core.regs.xreg[4]) == 8'h8A);
        assert($signed(soc.core.regs.xreg[5]) == 8'sh7F);
        assert($signed(soc.core.regs.xreg[6]) == 16'sb0000_00001_1101111);
        assert($signed(soc.core.regs.xreg[7]) == 16'hC3C7);
        assert($signed(soc.core.regs.xreg[8]) == 32'sh8A8FC3C7);
        assert($signed(soc.core.regs.xreg[9]) == 32'h8A8FC3C7);
        assert($signed(soc.core.regs.xreg[10]) == 64'h66778899_017F423C);
        for (int i=11; i<32; i+=1)
            assert(soc.core.regs.xreg[i] == '0);
        $finish();
    end
endmodule