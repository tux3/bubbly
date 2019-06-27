module flash_reader_tb;

    bit clk = 0;
    bit rst = 1;

    logic [23:0] addr = 0;
    logic read_from_addr = 0;
    logic read_next = 0;
    logic [7:0] data;
    logic data_ready;

    wire cs, sclk, si, so, wp, hold;

    qspi_flash_mock flash(
        .*
    );

    flash_reader flash_reader(
        .*
    );

    initial begin
        #0 rst = 0;
        #100 rst = 1;
        forever
            #50 clk = !clk;
    end

    initial begin
        @(posedge rst);
        @(posedge clk);
        read_from_addr <= 1;

        @(posedge clk);
        read_from_addr <= 0;
        read_next <= 1;
    end
endmodule
