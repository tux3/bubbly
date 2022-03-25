`include "core/params.svh"
`include "axi/axi4lite.svh"

module func_mul_tb;
    timeunit 100ns;
    timeprecision 10ns;

    bit clk = 0;
    bit rst = 0;

    const logic [22*32-1:0] code_buf = {<<{
        {<<{32'hc88cd0b7}}, //  lui     x1,0xc88cd
        {<<{16'h008a}}, //      slli    x1,x1,0x2
        {<<{32'h45508093}}, //  addi    x1,x1,1109 # ffffffffc88cd455 <.padding+0xffffffffc88cd40f>
        {<<{16'h00b2}}, //      slli    x1,x1,0xc
        {<<{32'h66708093}}, //  addi    x1,x1,1639
        {<<{16'h00b2}}, //      slli    x1,x1,0xc
        {<<{32'h78808093}}, //  addi    x1,x1,1928
        {<<{32'h0aabb137}}, //  lui     x2,0xaabb
        {<<{16'h0112}}, //      slli    x2,x2,0x4
        {<<{32'h07710113}}, //  addi    x2,x2,119 # aabb077 <.padding+0xaabb031>
        {<<{32'h21d951b7}}, //  lui     x3,0x21d95
        {<<{16'h018a}}, //      slli    x3,x3,0x2
        {<<{32'h32118193}}, //  addi    x3,x3,801 # 21d95321 <.padding+0x21d952db>
        
        {<<{32'h02208233}}, //  mul     x4,x1,x2
        {<<{32'h022092b3}}, //  mulh    x5,x1,x2
        {<<{32'h0220b333}}, //  mulhu   x6,x1,x2
        {<<{32'h0220a3b3}}, //  mulhsu  x7,x1,x2
        {<<{32'h02112433}}, //  mulhsu  x8,x2,x1
        {<<{32'h022084bb}}, //  mulw    x9,x1,x2
        {<<{32'h0230853b}}, //  mulw    x10,x1,x3
        {<<{32'h021095b3}}, //  mulh    x11,x1,x1

        {<<{32'b11111111110111111111_00000_1101111}},   // Inf. loop
        {<<{16'h1212}},                                 // 8B align
        {<<{32'h00000000}}, {<<{32'h00000000}}          // padding
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

        assert(soc.core.regs.xreg[1] == 'hFF22334455667788);
        assert(soc.core.regs.xreg[2] == 'h00000000AABB0077);
        assert(soc.core.regs.xreg[3] == 'h0000000087654321);
        
        assert(soc.core.regs.xreg[4] == 'h6c8641fd52f99038);
        assert(soc.core.regs.xreg[5] == 'hffffffffff6c1406);
        assert(soc.core.regs.xreg[6] == 'haa27147d);
        assert(soc.core.regs.xreg[7] == 'hffffffffff6c1406);
        assert(soc.core.regs.xreg[8] == 'haa27147d);
        assert(soc.core.regs.xreg[9] == 'h0000000052f99038);
        assert(soc.core.regs.xreg[10] == 'hffffffffb4260088);
        assert(soc.core.regs.xreg[11] == 'h0000c02b1fc02e8c);

        $finish();
    end
endmodule
