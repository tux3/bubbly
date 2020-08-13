`include "../params.svh"

module exec(
    input clk,
    input rst,
    input prev_stalled,
    output wire stall_prev,
    output reg stall_next,

    input decode_exception,
    input decode_is_compressed_instr,
    input decode_is_jump,
    input decode_is_reg_write,
    input [`ALEN-1:0] decode_instruction_addr,
    input [`ALEN-1:0] decode_instruction_next_addr,
    input [4:0] opcode,
    input [4:0] rd,
    input [2:0] funct3,
    input [4:0] rs1,
    input [4:0] rs2,
    input [`XLEN-1:0] decode_rs1_data,
    input [`XLEN-1:0] decode_rs2_data,
    input [6:0] funct7,
    input [31:20] i_imm,
    input [11:0] s_imm,
    input [31:12] u_imm,
    input [20:1] j_imm,

    output logic exec_exception,
    output logic exec_is_branch,
    output logic exec_is_reg_write,
    output logic [4:0] exec_reg_write_sel,
    output logic [`XLEN-1:0] exec_result,
    output logic [`ALEN-1:0] exec_branch_target,
    output reg [`ALEN-1:0] exec_instruction_next_addr, // This is NOT the next PC, it's still just the addr following the current instr

    // We require every previous stage to reset/stall their output on flush
    output wire exec_pipeline_flush,

    axi4lite.master data_bus
);

// The decoder's bypass inputs are registered, so they can't bypass directly from an exec cycle to the next
wire [`XLEN-1:0] rs1_data = (exec_is_reg_write && exec_reg_write_sel == rs1) ? exec_result : decode_rs1_data;
wire [`XLEN-1:0] rs2_data = (exec_is_reg_write && exec_reg_write_sel == rs2) ? exec_result : decode_rs2_data;

reg busy;
reg stopped_after_exception;
wire input_valid_unless_mispredict = !prev_stalled && !stall_prev;
wire input_valid = input_valid_unless_mispredict && !decode_exception && !exec_pipeline_flush;
assign exec_is_branch = exec_branch_output_valid;

wire input_is_branch = decode_is_jump;
wire exec_branch_next_output_valid_comb;
wire exec_branch_output_valid;
wire exec_branch_exception;
wire [`XLEN-1:0] exec_branch_result;
exec_branch exec_branch(
    .exec_mispredict_detected(exec_pipeline_flush),
    .*
);

wire input_is_int = opcode[4] == 0 && opcode[2] == 1;
wire exec_int_output_valid;
wire exec_int_exception;
wire [`XLEN-1:0] exec_int_result;
exec_int exec_int(
    .*
);

wire input_is_mem = opcode[4] == 0 && opcode[2] == 0;
wire exec_mem_output_valid;
wire exec_mem_exception;
wire [`XLEN-1:0] exec_mem_result;
exec_mem exec_mem(
    .*
);

wire lsu_prev_stalled;
wire lsu_stall_next;
wire [basic_cache_params::aligned_addr_size-1:0] lsu_addr;
wire lsu_access_fault;
wire lsu_do_load;
wire [`XLEN-1:0] lsu_load_data;
wire lsu_do_store;
wire [`XLEN-1:0] lsu_store_data;
wire [(`XLEN/8)-1:0] lsu_store_mask;
load_store lsu(
    .clk,
    .rst,
    .prev_stalled(lsu_prev_stalled),
    .stall_next(lsu_stall_next),
    .addr(lsu_addr),
    .access_fault(lsu_access_fault),
    .do_load(lsu_do_load),
    .load_data(lsu_load_data),
    .do_store(lsu_do_store),
    .store_data(lsu_store_data),
    .store_mask(lsu_store_mask),
    .data_bus(data_bus)
);

assign stall_prev = busy && stall_next;

always_ff @(posedge clk) begin
    if (rst) begin
        stopped_after_exception <= '0;
        busy <= '0;
        exec_is_reg_write <= 'x;
        exec_reg_write_sel <= '0;
        exec_instruction_next_addr <= 'x;
    end else begin
        if (!prev_stalled && !stall_prev) begin
            exec_instruction_next_addr <= exec_pipeline_flush ? 'x : decode_instruction_next_addr;
            if (decode_exception && !exec_pipeline_flush)
                stopped_after_exception <= '1;
        end

        if (input_valid) begin
            busy <= '1;
            exec_is_reg_write <= decode_is_reg_write;
            exec_reg_write_sel <= decode_is_reg_write ? rd : 'x;
        end else if (!stall_next) begin
            busy <= '0;
            exec_reg_write_sel <= '0;
        end
    end
end

// This is really a simple unique case(1'b1), except it's not *actually* unique during fucking delta cycle....
// So we have to do this syntactic horror
enum {
	NO_OUTPUT_VALID =       'b000,
    BRANCH_OUTPUT_VALID =   'b100,
    INT_OUTPUT_VALID =      'b010,
    MEM_OUTPUT_VALID =      'b001
} valid_output_types;
always_comb unique case ({exec_branch_output_valid, exec_int_output_valid, exec_mem_output_valid})
    NO_OUTPUT_VALID: begin
        exec_exception = stopped_after_exception;
        stall_next = !exec_exception;
        exec_result = '0;
    end
    BRANCH_OUTPUT_VALID: begin
        stall_next = '0;
        exec_exception = exec_branch_exception;
        exec_result = exec_branch_result;
    end
    INT_OUTPUT_VALID: begin
        stall_next = '0;
        exec_exception = exec_int_exception;
        exec_result = exec_int_result;
    end
    MEM_OUTPUT_VALID: begin
        stall_next = '0;
        exec_exception = exec_mem_exception;
        exec_result = exec_mem_result;
    end
    default: begin
        // This can happen during delta cycles... and hopefully only delta cycles.
        stall_next = 'x;
        exec_exception = 'x;
        exec_result = 'x;
    end
endcase

endmodule