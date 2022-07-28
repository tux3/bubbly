`include "core/params.svh"
`include "axi/axi4lite.svh"

module func_amo_lrsc_tb;
    timeunit 100ns;
    timeprecision 10ns;

    bit clk = 0;
    bit rst = 0;

    bit [64-1:0] sram_addr = {{64-`ALEN{1'b0}}, 4'b0001, {`ALEN-4{1'b0}}};
    const logic [22*32-1:0] code_buf_raw = {<<{
        {<<{32'h04800093}}, //    li      x1,72
        {<<{32'h1000b12f}}, //    lr.d    x2,(x1)
        {<<{16'h00a1}},     //    addi    x1,x1,8
        {<<{32'h1000b1af}}, //    lr.d    x3,(x1)
        {<<{16'h10e1}},     //    addi    x1,x1,-8
        {<<{32'h1001302f}}, //    lr.d    zero,(x2)
        {<<{32'h1821322f}}, //    sc.d    x4,x2,(x2)
        {<<{32'h183132af}}, //    sc.d    x5,x3,(x2)
        {<<{32'h00c08513}}, //    addi    x10,x1,12
        {<<{16'h002c}},     //    addi    x11,x2,8
        {<<{32'h1005232f}}, //    lr.w    x6,(x10)
        {<<{32'h1005a02f}}, //    lr.w    zero,(x11)
        {<<{32'h1865a3af}}, //    sc.w    x7,x6,(x11)
        {<<{32'h1805a3af}}, //    sc.w    x7,zero,(x11)
        {<<{16'h0810}},     //    addi    x12,x2,16
        {<<{32'h1006342f}}, //    lr.d    x8,(x12)
        {<<{32'h00363023}}, //    sd      x3,0(x12)
        {<<{32'h188634af}}, //    sc.d    x9,x8,(x12)

        {<<{32'b11111111110111111111_00000_1101111}},   // Inf. loop
        {<<{32'h12121212}}, // 8B align
        {<<{sram_addr[31:0]}}, {<<{sram_addr[63:32]}},     // sram ptr
        {<<{32'hAABBCCDD}}, {<<{32'hAAEEBBFF}}                // misc data
    }};
    const logic [22*32-1:0] code_buf = code_buf_raw;

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

    task axi4_read_expect_data(input [`ALEN-1:0] addr, input [64-1:0] data);
        @(posedge clk);
        @(posedge clk) begin
            assert(soc.data_axi.arvalid == '0) else $error("[%t] Expected !arvalid for read at %h", $time, addr); // Otherwise, this is going to get messy!
            force soc.data_axi.araddr = addr;
            force soc.data_axi.arvalid = '1;
        end

        forever @(posedge clk) begin
            if (soc.data_axi.arready) begin
                force soc.data_axi.rready = '1;
                force soc.data_axi.arvalid = '0;
                release soc.data_axi.araddr;
                break;
            end
        end

        while (!(soc.data_axi.rvalid && soc.data_axi.rready))
            @(posedge clk);
        release soc.data_axi.arvalid;
        assert(soc.data_axi.rresp == AXI4LITE_RESP_OKAY) else $error("[%t] Expected rresp OKAY for read at %h, but got %h", $time, addr, soc.data_axi.rresp);
        assert(soc.data_axi.rdata == data) else $error("[%t] Expected to read %h at %h, but got %h", $time, data, addr, soc.data_axi.rdata);
        @(posedge clk);
        release soc.data_axi.rready;
    endtask

    initial begin
        #2; @(posedge clk);

        #1500;

        assert(soc.core.regs.xreg[1] == 'h48);
        assert(soc.core.regs.xreg[2] == sram_addr);
        assert(soc.core.regs.xreg[3] == 'hAAEEBBFFAABBCCDD);
        assert(soc.core.regs.xreg[4] == 'h0);
        assert(soc.core.regs.xreg[5] != 'h0);
        assert(soc.core.regs.xreg[6] == 'hFFFFFFFFAAEEBBFF);
        assert(soc.core.regs.xreg[7] != 'h0);
        assert(soc.core.regs.xreg[8] == 'h0);
        assert(soc.core.regs.xreg[9] != 'h0);
        assert(soc.core.regs.xreg[10] == 'h54);

        axi4_read_expect_data(.addr(sram_addr), .data(sram_addr));
        axi4_read_expect_data(.addr(sram_addr+'h8), .data('hAAEEBBFF));
        axi4_read_expect_data(.addr(sram_addr+'h10), .data('hAAEEBBFFAABBCCDD));
        $finish();
    end
endmodule
