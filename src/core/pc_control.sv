`include "params.svh"

module pc_control(
    input clk, rst,
    input next_stalled,
    output reg stall,
    output reg [`XLEN-1:0] pc
);

always_ff @(posedge clk, negedge rst) begin
    if (!rst) begin
        pc <= '0;
        stall <= '0;
    end else begin
        stall <= '0; // NOTE: For now we have no reason to initiate a stall, we just wait for the fetch's handshake to tick ahead
        if (!stall && !next_stalled)
            pc <= pc + 'h4;
    end
end

endmodule