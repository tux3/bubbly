`include "../params.svh"

module exec #(
    parameter UNCACHEABLE_ADDR_MASK = '0
) (
    input clk,
    input rst,
    input prev_stalled,
    output wire stall_prev,
    output reg stall_next,

    // Interrupt lines
    input mtime_int,
    input [`PLATFORM_INTR_LEN-1:0] platform_ints,

    input decode_exception,
    input [3:0] decode_trap_cause,
    input decode_is_jump,
    input decode_is_reg_write,
    input [`ILEN-1:0] decode_original_instruction,
    input [`ALEN-1:0] decode_instruction_addr,
    input [`ALEN-1:0] decode_instruction_next_addr,
    input [4:0] opcode,
    input [4:0] rd,
    input [2:0] funct3,
    input [4:0] rs1,
    input [4:0] rs2,
    input [`XLEN-1:0] decode_rs1_data,
    input [`XLEN-1:0] decode_rs2_data,
    input rs1_mul_sign,
    input rs2_mul_sign,
    input [6:0] funct7,
    input [31:20] i_imm,
    input [11:0] s_imm,
    input [12:1] b_imm,
    input [31:12] u_imm,
    input [20:1] j_imm,
    
    output logic [`ALEN-1:0] exec_mepc_approximate, // Note guaranteed to be up to date, used to predict xRET

    output logic exec_exception,
    output logic exec_interrupt,
    output logic [`ALEN-1:0] exec_trap_target,
    output logic exec_is_taken_branch,
    output logic exec_is_reg_write,
    output logic exec_is_xret,
    output logic [4:0] exec_reg_write_sel,
    output logic [`XLEN-1:0] exec_result,
    output logic [`ALEN-1:0] exec_branch_target,
    output reg [`ALEN-1:0] exec_instruction_next_addr, // This is NOT the next PC, it's still just the addr following the current instr

    // We require every previous stage to reset/stall their output on flush
    output wire exec_pipeline_flush,
    output wire exec_mispredict_detected,
    output wire [`ALEN-1:0] exec_mispredict_next_pc,

    axi4lite.master data_bus
);

logic [3:0] last_output_type;
logic [3:0] valid_outputs;
wire no_output_valid = valid_outputs == '0;

// The decoder's bypass inputs are registered, so they can't bypass directly from an exec cycle to the next
wire [`XLEN-1:0] rs1_data = (exec_is_reg_write && exec_reg_write_sel == rs1) ? exec_result : decode_rs1_data;
wire [`XLEN-1:0] rs2_data = (exec_is_reg_write && exec_reg_write_sel == rs2) ? exec_result : decode_rs2_data;

reg busy;
wire input_valid_unless_mispredict = !prev_stalled && !stall_prev;
wire input_valid = input_valid_unless_mispredict && !decode_exception && !exec_pipeline_flush;

// Note that xRET is under exec_system, but exec_branch still knows about xRET,
// so it can consider it a taken branch and share the mispredict/flush detection
wire input_is_branch = decode_is_jump;
wire exec_branch_next_output_valid_comb;
wire exec_branch_output_valid;
wire exec_branch_exception;
wire [3:0] exec_branch_trap_cause;
wire exec_branch_taken;
wire [`XLEN-1:0] exec_branch_result;
exec_branch exec_branch(
    .*
);

wire input_is_int = opcode[4] == 0 && opcode[2] == 1;
wire exec_int_output_valid;
wire exec_int_exception;
wire [3:0] exec_int_trap_cause;
wire [`XLEN-1:0] exec_int_result;
exec_int exec_int(
    .*
);

wire input_is_system = opcode == opcodes::SYSTEM;
wire exec_system_output_valid;
wire exec_system_exception;
wire [3:0] exec_system_trap_cause;
wire exec_system_is_xret;
wire [`XLEN-1:0] exec_system_result;
wire exec_system_would_do_wfi;
wire exec_system_blocked_on_wfi;
wire exec_system_will_do_xret;
wire [`XLEN-1:0] exec_system_new_mstatus_comb;
wire [1:0] exec_system_new_privilege_mode_comb;
exec_system exec_system(
    .*
);

wire input_is_mem = opcode[4] == 0 && opcode[2] == 0;
wire exec_mem_output_valid;
wire exec_mem_exception;
wire [3:0] exec_mem_trap_cause;
wire [`ALEN-1:0] exec_mem_fault_addr;
wire [`XLEN-1:0] exec_mem_result;
wire [`ALEN-1:0] last_branch_target_or_next;
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
load_store #(
    .UNCACHEABLE_ADDR_MASK(UNCACHEABLE_ADDR_MASK)
) lsu (
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

logic exec_trap;
logic [3:0] exec_trap_cause;
logic [`ALEN-1:0] decode_trap_mepc_buf;
logic [`ILEN-1:0] decode_original_instr_buf;

wire exec_csr_instr_valid;
wire [11:0] exec_csr_addr;
wire [2:0] exec_csr_funct3;
wire [4:0] exec_csr_rd;
wire [4:0] exec_csr_rs1_uimm;
wire [`XLEN-1:0] exec_csr_rs1_data;
wire exec_csr_exception;
wire [3:0] exec_csr_trap_cause;
wire [`XLEN-1:0] exec_csr_result;
wire [1:0] privilege_mode;
wire [`XLEN-1:0] mstatus;
wire [`INTR_LEN-1:0] mie;
wire [`INTR_LEN-1:0] mip;
wire [`ALEN-1:0] mepc;
wire [`XLEN-1:0] mtvec;

wire trap_take_m_int;
wire [`INTR_LEN-1:0] trap_int_cause;
wire [`ALEN-1:0] trap_mepc;
wire [`XLEN-1:0] trap_mtval;

csrs csrs(
    .inst_retired(!stall_next && !exec_trap),
    .trap_do_update(exec_trap),
    .trap_mcause(trap_take_m_int ? (64'h8000_0000_0000_0000 | trap_int_cause) : exec_trap_cause),
    .trap_mepc,
    .trap_mtval,
    .xret_do_update(exec_system_will_do_xret),
    .xret_completing(exec_is_xret && !exec_exception),
    .xret_new_mstatus(exec_system_new_mstatus_comb),
    .xret_new_privilege_mode(exec_system_new_privilege_mode_comb),
    .*
);

trap trap(
    .exec_trap_cause(exec_trap_cause),
    .exec_trap_instr_addr(decode_trap_mepc_buf),
    .exec_trap_instr(decode_original_instr_buf),
    .exec_branch_target,
    .exec_trap_target,
    .int_cause(trap_int_cause),
    .take_m_int(trap_take_m_int),

    .trap_mepc,
    .trap_mtval,
    .*
);

assign exec_mepc_approximate = mepc;

assign stall_prev = busy && no_output_valid;

always_ff @(posedge clk) begin
    if (rst) begin
        busy <= '0;
        exec_is_reg_write <= '0;
        exec_reg_write_sel <= '0;
        exec_instruction_next_addr <= 'x;
    end else begin
        if (!prev_stalled && !stall_prev) begin
            exec_instruction_next_addr <= exec_pipeline_flush ? 'x : decode_instruction_next_addr;
        end

        if (input_valid) begin
            busy <= '1;
            exec_is_reg_write <= decode_is_reg_write && rd != '0;
            exec_reg_write_sel <= decode_is_reg_write ? rd : '0;
        end else if (!stall_next) begin
            busy <= '0;
            exec_is_reg_write <= '0;
            exec_reg_write_sel <= '0;
        end
    end
end

logic decode_valid_exception_buf;
logic [3:0] decode_trap_cause_buf;
always @(posedge clk) begin
    if (rst) begin
        decode_valid_exception_buf <= '0;
        decode_trap_cause_buf <= 'x;
        decode_trap_mepc_buf <= 'x;
        decode_original_instr_buf <= 'x;
    end else if (input_valid_unless_mispredict) begin
        decode_valid_exception_buf <= decode_exception && !exec_pipeline_flush;
        decode_trap_cause_buf <= decode_trap_cause;
        decode_trap_mepc_buf <= exec_system_would_do_wfi ? decode_instruction_next_addr : decode_instruction_addr;
        decode_original_instr_buf <= decode_original_instruction;
    end else begin
        decode_valid_exception_buf <= '0;
        decode_trap_cause_buf <= 'x;
        decode_trap_mepc_buf <= 'x;
        decode_original_instr_buf <= 'x;
    end
end

// This is really a simple unique case(1'b1), except it's not *actually* unique during fucking delta cycle....
// So we have to do this syntactic horror
enum {
    NO_OUTPUT_VALID =       'b0000,
    BRANCH_OUTPUT_VALID =   'b1000,
    INT_OUTPUT_VALID =      'b0100,
    SYSTEM_OUTPUT_VALID =   'b0010,
    MEM_OUTPUT_VALID =      'b0001
} valid_output_types;

always_ff @(posedge clk) begin
    if (rst) begin
        last_output_type <= NO_OUTPUT_VALID;
    end else if (input_valid) begin
        last_output_type <= ({input_is_branch, input_is_int, input_is_system, input_is_mem});
    end else if (!stall_next) begin
        last_output_type <= NO_OUTPUT_VALID;
    end
end

always_comb unique case (last_output_type)
    NO_OUTPUT_VALID: begin
        exec_exception = decode_valid_exception_buf;
        exec_trap_cause = decode_trap_cause_buf;
        exec_result = 'x;
    end
    BRANCH_OUTPUT_VALID: begin
        exec_exception = exec_branch_exception;
        exec_trap_cause = exec_branch_trap_cause;
        exec_result = exec_branch_result;
    end
    INT_OUTPUT_VALID: begin
        exec_exception = exec_int_exception;
        exec_trap_cause = exec_int_trap_cause;
        exec_result = exec_int_result;
    end
    SYSTEM_OUTPUT_VALID: begin
        exec_exception = exec_system_exception;
        exec_trap_cause = exec_system_trap_cause;
        exec_result = exec_system_result;
    end
    MEM_OUTPUT_VALID: begin
        exec_exception = exec_mem_exception;
        exec_trap_cause = exec_mem_trap_cause;
        exec_result = exec_mem_result;
    end
    default: begin
        exec_exception = 'x;
        exec_trap_cause = 'x;
        exec_result = 'x;
    end
endcase

assign valid_outputs = {exec_branch_output_valid, exec_int_output_valid, exec_system_output_valid, exec_mem_output_valid};
always_comb unique case (valid_outputs)
    NO_OUTPUT_VALID: begin
        stall_next = !exec_trap;
    end
    BRANCH_OUTPUT_VALID: begin
        stall_next = '0;
    end
    INT_OUTPUT_VALID: begin
        stall_next = '0;
    end
    SYSTEM_OUTPUT_VALID: begin
        stall_next = '0;
    end
    MEM_OUTPUT_VALID: begin
        stall_next = '0;
    end
    default: begin
        // This can happen during delta cycles... and hopefully only delta cycles.
        stall_next = 'x;
    end
endcase

// These two don't account for when the instr raised an exception and shouldn't actually be followed
assign exec_is_taken_branch = exec_branch_output_valid && exec_branch_taken;
assign exec_is_xret = exec_system_output_valid && exec_system_is_xret;

assign exec_interrupt = trap_take_m_int;
assign exec_trap = exec_exception || trap_take_m_int;
assign exec_pipeline_flush = exec_mispredict_detected || exec_trap;

endmodule