`include "core/params.svh"
`include "axi/axi4lite.svh"

module exec_div_tb;
    timeunit 100ns;
    timeprecision 10ns;
    
    bit clk = 0;
    bit rst = 0;
    
    initial begin
        #0 rst = 1;
        #2 rst = 0;
    end

    initial forever
        #0.5 clk = !clk;
    
    logic input_valid;
    logic [`XLEN-1:0] div_a;
    logic [`XLEN-1:0] div_b;
    wire [`XLEN-1:0] div_q;
    wire output_valid;
    exec_div div(.clk, .rst, .a_in(div_a), .b_in(div_b), .q_out(div_q), .do_rem(0), .input_valid, .output_valid);
    
    task expect_div(input [`XLEN-1:0] a, input [`XLEN-1:0] b, input [`XLEN-1:0] expected);
        @(posedge clk) begin
            assert(!output_valid);
            input_valid <= '1;
            div_a <= a;
            div_b <= b;
        end
        @(posedge clk)
            input_valid <= '0;
        while (!output_valid)
            @(posedge clk);
        assert(expected == div_q) else $error("[%t] Expected %h/%h to give %h, but got %h", $time, a, b, expected, div_q);
    endtask
    
    initial begin
        @(posedge clk)
            input_valid <= 0;
        #2;
        
        expect_div(6, 3, 2);
        expect_div(1, 2, 0);
        expect_div(3, 3, 1);
        expect_div(15000, 300, 50);
        expect_div(64'd18446744073709551599, 64'd18446744073709551600, 0);
        expect_div(64'd18446744073709550615, 1, 64'd18446744073709550615);

        $finish();
    end
endmodule
