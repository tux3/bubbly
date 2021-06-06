`include "../params.svh"

module exec_branch(
    input clk,
    input rst,
    input [`ALEN-1:0] decode_instruction_addr,
    input [`ALEN-1:0] decode_instruction_next_addr,
    input [4:0] opcode,
    input [4:0] rd,
    input [2:0] funct3,
    input [4:0] rs1,
    input [4:0] rs2,
    input [`XLEN-1:0] rs1_data,
    input [`XLEN-1:0] rs2_data,
    input [31:20] i_imm,
    input [12:1] b_imm,
    input [20:1] j_imm,

    input input_valid_unless_mispredict, // *We* detect those mispredicts!
    input input_valid,
    input input_is_branch,

    output reg exec_branch_output_valid,
    output reg exec_branch_exception,
    output reg [3:0] exec_branch_trap_cause,
    output reg exec_branch_taken,
    output reg [`XLEN-1:0] exec_branch_result,
    output reg [`ALEN-1:0] exec_branch_target,

    output wire exec_mispredict_detected,
    output wire [`ALEN-1:0] exec_mispredict_next_pc
);

always_ff @(posedge clk) begin
    if (rst)
        exec_branch_output_valid <= '0;
    else
        exec_branch_output_valid <= input_valid && input_is_branch;
end

logic illegal_instruction_exception;
logic [`ALEN-1:0] exec_branch_target_comb;
logic [`ALEN-1:0] branch_adder_op_1;
logic [`ALEN-1:0] branch_adder_op_2;
wire [`ALEN-1:0] branch_adder_result = branch_adder_op_1 + branch_adder_op_2;

always_comb begin
    illegal_instruction_exception = '0;

    if (opcode == decode_types::OP_JAL) begin
        branch_adder_op_1 = {{`ALEN-20{j_imm[20]}}, j_imm[19:1], 1'b0};
        branch_adder_op_2 = decode_instruction_addr;
        exec_branch_target_comb = branch_adder_result;
    end else if (opcode == decode_types::OP_JALR) begin
        branch_adder_op_1 = {{`ALEN-11{i_imm[31]}}, i_imm[30:20]};
        branch_adder_op_2 = rs1_data;
        exec_branch_target_comb = {branch_adder_result[`ALEN-1:1], 1'b0};
        illegal_instruction_exception = funct3 != '0;
    end else if (opcode == decode_types::OP_BRANCH) begin
        branch_adder_op_1 = {{`ALEN-12{b_imm[12]}}, b_imm[11:1], 1'b0};
        branch_adder_op_2 = decode_instruction_addr;
        exec_branch_target_comb = branch_adder_result;
        illegal_instruction_exception = funct3 == 3'b010 || funct3 == 3'b011;
    end else begin
        branch_adder_op_1 = 'x;
        branch_adder_op_2 = 'x;
        exec_branch_target_comb = 'x;
    end
end

logic branch_taken;
wire branch_equal_result = rs1_data == rs2_data;
wire branch_compare_result = rs1_data < rs2_data;
wire branch_compare_signed_result = $signed(rs1_data) < $signed(rs2_data);
always_comb begin
    if (opcode == decode_types::OP_BRANCH) begin
        unique case (funct3)
            3'b000: begin // BEQ
                branch_taken = branch_equal_result;
            end
            3'b001: begin // BNE
                branch_taken = !branch_equal_result;
            end
            3'b100: begin // BLT
                branch_taken = branch_compare_signed_result;
            end
            3'b110: begin // BLTU
                branch_taken = branch_compare_result;
            end
            3'b101: begin // BGE
                branch_taken = !branch_compare_signed_result;
            end
            3'b111: begin // BGEU
                branch_taken = !branch_compare_result;
            end
            default: branch_taken = 'x;
        endcase
    end else begin
        branch_taken = '1;
    end
end

always_ff @(posedge clk) begin
    if (input_valid && input_is_branch) begin
        if (illegal_instruction_exception) begin
            exec_branch_exception <= '1;
            exec_branch_trap_cause <= trap_causes::EXC_ILLEGAL_INSTR;
        end else if (exec_branch_target_comb[0]) begin
            exec_branch_exception <= '1;
            exec_branch_trap_cause <= trap_causes::EXC_INSTR_ADDR_MISALIGNED;
        end else begin
            exec_branch_exception <= '0;
            exec_branch_trap_cause <= 'x;
        end

        exec_branch_target <= exec_branch_target_comb;
        // Note that this is not the branch target, it's the value JAL/JALR write in rd
        exec_branch_result <= decode_instruction_next_addr;
    end
end

// Detect mispredicts by comparing the last taken branch to the next instr's address
wire last_branch_just_taken = exec_branch_taken;
reg [`ALEN-1:0] last_branch_target;

assign exec_mispredict_detected = input_valid_unless_mispredict && last_branch_just_taken && last_branch_target != decode_instruction_addr;
assign exec_mispredict_next_pc = last_branch_target;

always_ff @(posedge clk) begin
    if (rst) begin
        exec_branch_taken <= '0;
        last_branch_target <= 'x;
    end else begin
        if (input_valid_unless_mispredict)
            exec_branch_taken <= input_valid && input_is_branch && branch_taken;
        if (input_valid && input_is_branch && branch_taken)
            last_branch_target <= exec_branch_target_comb;
    end
end

endmodule