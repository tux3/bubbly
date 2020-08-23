`include "../params.svh"

module decode_decompress(
    input clk,
    input rst,
    input flush,

    input prev_stalled,
    input next_stalled,
    output logic stall_prev,
    output logic stall_next,

    input ifetch_exception,
    input [3:0] ifetch_trap_cause,
    input [`ILEN-1:0] instruction,
    input [`ALEN-1:0] instruction_addr,
    input [`ALEN-1:0] instruction_next_addr,

    output logic decomp_exception,
    output logic [3:0] decomp_trap_cause,
    output logic [`ILEN-1:0] decomp_original_instruction,
    output logic [`ILEN-1:0] decomp_expanded_instruction,
    output logic [`ALEN-1:0] decomp_instruction_addr,
    output logic [`ALEN-1:0] decomp_instruction_next_addr
);

wire buf_full;
skid_buf_ctl sb_ctl(
    .clk,
    .rst(rst || flush),
    .prev_stalled,
    .next_stalled,
    .buf_full,
    .stall_prev,
    .stall_next
);

wire [$bits(ifetch_exception)-1:0] sb_ifetch_exception_out;
skid_buf_data #(.WIDTH($bits(ifetch_exception))) sb_ifetch_exception(
    .*,
    .in(ifetch_exception),
    .out(sb_ifetch_exception_out)
);
wire [$bits(ifetch_trap_cause)-1:0] sb_ifetch_trap_cause_out;
skid_buf_data #(.WIDTH($bits(ifetch_trap_cause)), .MAYBE_UNKNOWN(1)) sb_ifetch_trap_cause(
    .*,
    .in(ifetch_trap_cause),
    .out(sb_ifetch_trap_cause_out)
);
wire [$bits(instruction)-1:0] sb_instruction_out;
skid_buf_data #(.WIDTH($bits(instruction)), .MAYBE_UNKNOWN(1)) sb_instruction( // May be unknown on last 2 bytes of a cache line, upper two bytes will be 'x
    .*,
    .in(instruction),
    .out(sb_instruction_out)
);
wire [$bits(instruction_addr)-1:0] sb_instruction_addr_out;
skid_buf_data #(.WIDTH($bits(instruction_addr))) sb_instruction_addr(
    .*,
    .in(instruction_addr),
    .out(sb_instruction_addr_out)
);
wire [$bits(instruction_next_addr)-1:0] sb_instruction_next_addr_out;
skid_buf_data #(.WIDTH($bits(instruction_next_addr))) sb_instruction_next_addr(
    .*,
    .in(instruction_next_addr),
    .out(sb_instruction_next_addr_out)
);

decode_decompress_impl decode_decompress_impl(
    .clk,
    .rst,
    .flush,
    .ifetch_exception(sb_ifetch_exception_out),
    .ifetch_trap_cause(sb_ifetch_trap_cause_out),
    .instruction(sb_instruction_out),
    .instruction_addr(sb_instruction_addr_out),
    .instruction_next_addr(sb_instruction_next_addr_out),
    .*
);

endmodule

// Pipeline oblivious, protected from stalls by the parent's skid buffer
module decode_decompress_impl(
    input clk,
    input rst,
    input flush,
    input ifetch_exception,
    input [3:0] ifetch_trap_cause,
    input [`ILEN-1:0] instruction,
    input [`ALEN-1:0] instruction_addr,
    input [`ALEN-1:0] instruction_next_addr,

    output reg decomp_exception,
    output reg [3:0] decomp_trap_cause,
    output reg [`ILEN-1:0] decomp_original_instruction,
    output reg [`ILEN-1:0] decomp_expanded_instruction,
    output reg [`ALEN-1:0] decomp_instruction_addr,
    output reg [`ALEN-1:0] decomp_instruction_next_addr
);

wire [15:0] c_instr = instruction;
wire is_compressed = instruction[1:0] != 2'b11;

always @(posedge clk) begin
    decomp_original_instruction <= instruction;
    decomp_expanded_instruction <= instruction;
end

always @(posedge clk) begin
    if (rst || flush) begin
        decomp_exception <= 'x;
        decomp_trap_cause <= 'x;
        decomp_instruction_addr <= 'x;
        decomp_instruction_next_addr <= 'x;
    end else begin
        decomp_instruction_addr <= instruction_addr;
        decomp_instruction_next_addr <= instruction_next_addr;

        if (ifetch_exception) begin
            decomp_exception <= '1;
            decomp_trap_cause <= ifetch_trap_cause;
        end else if (is_compressed) begin // TODO: Implement C instructions and remove this
            decomp_exception <= '1;
            decomp_trap_cause <= trap_causes::EXC_ILLEGAL_INSTR;
        end else if (is_compressed && c_instr == '0) begin
            decomp_exception <= '1;
            decomp_trap_cause <= trap_causes::EXC_ILLEGAL_INSTR;
        end else begin
            decomp_exception <= '0;
            decomp_trap_cause <= 'x;
        end
    end
end

endmodule
