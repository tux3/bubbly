// Holds one of the data buffers for skid_buf_ctl
module skid_buf_data #(
    parameter WIDTH = 1
) (
    input clk,
    input rst,
    input buf_full,
    input next_stalled,
    input [WIDTH-1:0] in,
    output [WIDTH-1:0] out
);

logic [WIDTH-1:0] out_buf;
assign out = buf_full ? out_buf : in;

always_ff @(posedge clk) begin
    if (rst) begin
        out_buf <= 'x;
    end else if (buf_full) begin
        if (!next_stalled)
            out_buf <= 'x;
    end else begin
        if (next_stalled)
            out_buf <= in;
        else
            out_buf <= 'x;
    end
end

`ifndef SYNTHESIS
always @(posedge clk) begin
    assert property (buf_full == !$isunknown(out_buf));
end
`endif

endmodule
