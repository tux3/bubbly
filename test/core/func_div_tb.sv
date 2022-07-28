`include "core/params.svh"
`include "axi/axi4lite.svh"

module func_div_tb;
    timeunit 100ns;
    timeprecision 10ns;

    bit clk = 0;
    bit rst = 0;

    const logic [40*32-1:0] code_buf = {<<{
        {<<{32'hc88cd0b7 }}, //               lui     x1,0xc88cd
        {<<{16'h008a }}, //                   slli    x1,x1,0x2
        {<<{32'h45508093 }}, //               addi    x1,x1,1109
        {<<{16'h00b2 }}, //                   slli    x1,x1,0xc
        {<<{32'h66708093 }}, //               addi    x1,x1,1639
        {<<{16'h00b2 }}, //                   slli    x1,x1,0xc
        {<<{32'h78808093 }}, //               addi    x1,x1,1928
        {<<{32'h0aabb137 }}, //               lui     x2,0xaabb
        {<<{16'h0112 }}, //                   slli    x2,x2,0x4
        {<<{32'h07710113 }}, //               addi    x2,x2,119
        {<<{16'h6185 }}, //                   lui     x3,0x1
        {<<{32'h2341819b }}, //               addiw   x3,x3,564

        {<<{32'h0220c233 }}, //               div     x4,x1,x2
        {<<{32'h0220d2b3 }}, //               divu    x5,x1,x2
        {<<{32'h0220e333 }}, //               rem     x6,x1,x2
        {<<{32'h0220f3b3 }}, //               remu    x7,x1,x2
        {<<{32'h0220c43b }}, //               divw    x8,x1,x2
        {<<{32'h023144bb }}, //               divw    x9,x2,x3
        {<<{32'h0220d53b }}, //               divuw   x10,x1,x2
        {<<{32'h023155bb }}, //               divuw   x11,x2,x3
        {<<{32'h0220e63b }}, //               remw    x12,x1,x2
        {<<{32'h023166bb }}, //               remw    x13,x2,x3
        {<<{32'h0220f73b }}, //               remuw   x14,x1,x2
        {<<{32'h023177bb }}, //               remuw   x15,x2,x3

        // Div by zero
        {<<{32'h0200c833 }}, //               div     x16,x1,x0
        {<<{32'h0200c8bb }}, //               divw    x17,x1,x0
        {<<{32'h0200d933 }}, //               divu    x18,x1,x0
        {<<{32'h0200d9bb }}, //               divuw   x19,x1,x0
        {<<{32'h0200ea33 }}, //               rem     x20,x1,x0
        {<<{32'h0200eabb }}, //               remw    x21,x1,x0
        {<<{32'h0200fb33 }}, //               remu    x22,x1,x0
        {<<{32'h0200fbbb }}, //               remuw   x23,x1,x0

        // Signed overflow case
        {<<{16'h50fd }}, //                   li      x1,-1
        {<<{16'h10fe }}, //                   slli    x1,x1,0x3f (INT64_MIN)
        {<<{16'h4105 }}, //                   li      x2,1
        {<<{16'h017e }}, //                   slli    x2,x2,0x1f (INT32_MIN)
        {<<{16'h51fd }}, //                   li      x3,-1

        {<<{32'h0230cc33 }}, //               div     x24,x1,x3
        {<<{32'h0230ecb3 }}, //               rem     x25,x1,x3
        {<<{32'h02314d3b }}, //               divw    x26,x2,x3
        {<<{32'h02316dbb }}, //               remw    x27,x2,x3

        {<<{32'b11111111110111111111_00000_1101111}},               // Inf. loop
        {<<{32'h00000000}}, {<<{32'h00000000}}, {<<{32'h00000000}}  // padding
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
        #1500;

        assert(soc.core.regs.xreg[1] == 'h8000000000000000);
        assert(soc.core.regs.xreg[2] == 'h0000000080000000);
        assert(soc.core.regs.xreg[3] == 'hFFFFFFFFFFFFFFFF);

        assert(soc.core.regs.xreg[4] == 'hfffffffffeb36cbc);
        assert(soc.core.regs.xreg[5] == 'h17e8eaf33);
        assert(soc.core.regs.xreg[6] == 'hffffffffaaaaec24);
        assert(soc.core.regs.xreg[7] == 'ha8d206d3);
        assert(soc.core.regs.xreg[8] == 'hffffffffffffffff);
        assert(soc.core.regs.xreg[9] == 'hfffffffffffb50d0);
        assert(soc.core.regs.xreg[10] == 'h0000000000000000);
        assert(soc.core.regs.xreg[11] == 'h0000000000096112);
        assert(soc.core.regs.xreg[12] == 'h00000000002177ff);
        assert(soc.core.regs.xreg[13] == 'hfffffffffffff637);
        assert(soc.core.regs.xreg[14] == 'h55667788);
        assert(soc.core.regs.xreg[15] == 'h000004cf);

        assert(soc.core.regs.xreg[16] == 'hFFFFFFFFFFFFFFFF);
        assert(soc.core.regs.xreg[17] == 'hFFFFFFFFFFFFFFFF);
        assert(soc.core.regs.xreg[18] == 'hFFFFFFFFFFFFFFFF);
        assert(soc.core.regs.xreg[19] == 'hFFFFFFFFFFFFFFFF);
        assert(soc.core.regs.xreg[20] == 'hFF22334455667788);
        assert(soc.core.regs.xreg[21] == 'h0000000055667788);
        assert(soc.core.regs.xreg[22] == 'hFF22334455667788);
        assert(soc.core.regs.xreg[23] == 'h0000000055667788);

        assert(soc.core.regs.xreg[24] == 'h8000000000000000);
        assert(soc.core.regs.xreg[25] == '0);
        assert(soc.core.regs.xreg[26] == 'hFFFFFFFF80000000);
        assert(soc.core.regs.xreg[27] == '0);
        for (int i=28; i<32; i+=1)
            assert(soc.core.regs.xreg[i] == '0);

        $finish();
    end
endmodule