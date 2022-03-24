// Holds one of the data buffers for skid_buf_ctl
module skid_buf_data #(
    parameter WIDTH = 1,
    parameter MAYBE_UNKNOWN = 0
) (
    input clk,
    input rst,
    input buf_full,
    input prev_stalled,
    input next_stalled,
    input stall_next,
    input [WIDTH-1:0] in,
    output logic [WIDTH-1:0] out
);

logic [WIDTH-1:0] skid_buf;
logic [WIDTH-1:0] out_buf;

always_comb begin
    if (buf_full) begin
        out = next_stalled ? out_buf : skid_buf;
    end else begin
        if (!prev_stalled && (!next_stalled || stall_next))
            out = in;
        else
            out = out_buf;
    end
end

always_ff @(posedge clk) begin
    if (rst) begin
        out_buf <= 'x;
        skid_buf <= 'x;
    end else if (buf_full) begin
        if (!next_stalled) begin
            out_buf <= skid_buf;
            skid_buf <= 'x;
        end
    end else begin
        if (!prev_stalled && next_stalled && !stall_next) begin
            skid_buf <= in;
        end
        // Preserve out_buf if: next_stalled
        if (!next_stalled && !stall_next) begin
            out_buf <= prev_stalled ? 'x : in;
        end else if (!prev_stalled && (!next_stalled || stall_next)) begin
            out_buf <= in;
        end
    end
end

`ifndef SYNTHESIS
always @(negedge clk) begin
    assert property (!buf_full && prev_stalled |=> !buf_full);
    assert property (!buf_full && prev_stalled && stall_next  |=> !buf_full && stall_next);
    assert property (!buf_full && !prev_stalled && stall_next && !rst |=> !buf_full && !stall_next);
    assert property (!buf_full && !prev_stalled && !stall_next && next_stalled && !rst |=> buf_full && !stall_next);
    assert property (!buf_full && !prev_stalled && !stall_next && !next_stalled && !rst |=> !buf_full && !stall_next);
    if (!MAYBE_UNKNOWN) begin
        assert property (buf_full |-> !$isunknown(out_buf) && !$isunknown(skid_buf));
        assert property (!buf_full |-> $isunknown(skid_buf));
    end
end
`endif

endmodule
