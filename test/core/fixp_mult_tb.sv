`include "core/params.svh"
`include "axi/axi4lite.svh"

module fixp_mult_tb;
    timeunit 100ns;
    timeprecision 10ns;
        
    wire [127:0] mult_r;
    logic [65:0] mult_a;
    logic [127:0] mult_b;
    fixp_mult mult(.a(mult_a), .b(mult_b), .r(mult_r));
    
    task automatic expect_fixp_mult(input [63:0] a, input [63:0] b, input [63:0] expected);
        #1;
        mult_a <= {a, {64{1'b0}}};
        mult_b <= {b, {64{1'b0}}};
        #1;
        assert(expected == mult_r[64 +: 64]) else $error("[%t] Expected %h * %h to give %h, but got %h", $time, a, b, expected, mult_r[64 +: 64]);
        #1;
    endtask
    
    initial begin
        expect_fixp_mult(2, 5, 10);
        expect_fixp_mult(8, 0, 0);
        expect_fixp_mult(1, 'h1234_5678, 'h1234_5678);
        // If b is negative, we always return -1 for the integer part (this makes sense as a trick for division)
        expect_fixp_mult(2, 'hF000_0000_1234_0000, 'hFFFF_FFFF_FFFF_FFFF);
        expect_fixp_mult(3, 'hFFFF_FFFF_FFFF_FFFF, 'hFFFF_FFFF_FFFF_FFFF);
        $finish();
    end

endmodule
