`include "core/params.svh"

module follow_branch(
    input clk,
    input rst,
    
    input instr_valid,
    input [`ILEN-1:0] instruction,
    input [`ALEN-1:0] instruction_addr,
    
    input [`ALEN-1:0] mepc,
    
    output should_follow_branch,
    output logic [`ALEN-1:0] branch_target
);

wire is_compressed = instruction[1:0] != 2'b11;
wire [4:0] c_op = {instruction[15:13], instruction[1:0]};
wire [4:0] op = instruction[6:2];
wire [11:0] funct12 = instruction[31:20];
wire is_xret = op == opcodes::SYSTEM && instruction[19:7] == '0
                && funct12 ==? 12'b00x1000_00010;

logic is_predictable_branch;
logic is_unconditional_branch;
logic jumps_backward; // Our 'branch predictor' just merrily assumes the taken branches are all the backwards branches
assign should_follow_branch = instr_valid && is_predictable_branch && (jumps_backward || is_unconditional_branch);
always_comb begin
    if (is_compressed) begin
        is_predictable_branch = c_op == opcodes::C_J
                             || c_op == opcodes::C_BEQZ
                             || c_op == opcodes::C_BNEZ;
        is_unconditional_branch = c_op == opcodes::C_J;
        jumps_backward = instruction[12];
    end else begin
        is_predictable_branch = op == opcodes::BRANCH
                             || op == opcodes::JAL
                             || is_xret;
        is_unconditional_branch = op == opcodes::JAL || is_xret;
        jumps_backward = instruction[31];
    end
end

// NOTE: This probably adds a LOT of delay to ifetch, because our inputs come very late
// Later, we should split ifetch in two to regain some slack and add a FIFO at the end to hide bubbles

// Mini decompress stage
logic [12:1] b_imm;
logic [20:1] j_imm;
wire [11:1] cj_off = {instruction[12], instruction[8], instruction[10:9], instruction[6],
                        instruction[7], instruction[2], instruction[11], instruction[5:3]};
wire [7:0] cb_imm = {instruction[12:10], instruction[6:2]};
wire [8:1] cb_off = {cb_imm[7], cb_imm[4:3], cb_imm[0], cb_imm[6:5], cb_imm[2:1]};

always_comb begin
    if (is_compressed) begin
        b_imm = {{4{cb_off[8]}}, cb_off[8:1]};
        j_imm = {{9{cj_off[11]}}, cj_off[11:1]};
    end else begin
        b_imm = {instruction[31], instruction[7], instruction[30:25], instruction[11:8]};
        j_imm = {instruction[31], instruction[19:12], instruction[20], instruction[30:25], instruction[24:21]};
    end
end

logic [`ALEN-1:0] branch_adder_op;
always_comb begin
    if (is_xret)
        branch_target = mepc;
    else
        branch_target = branch_adder_op + instruction_addr;
end

always_comb begin
    if (is_compressed) begin
        unique case(c_op)
            opcodes::C_J: branch_adder_op = {{`ALEN-20{j_imm[20]}}, j_imm[19:1], 1'b0};
            opcodes::C_BEQZ: branch_adder_op = {{`ALEN-12{b_imm[12]}}, b_imm[11:1], 1'b0};
            opcodes::C_BNEZ: branch_adder_op = {{`ALEN-12{b_imm[12]}}, b_imm[11:1], 1'b0};
            default: branch_adder_op = 'x;
        endcase
    end else begin
        unique case(op)
            opcodes::BRANCH: branch_adder_op = {{`ALEN-12{b_imm[12]}}, b_imm[11:1], 1'b0};
            opcodes::JAL: branch_adder_op = {{`ALEN-20{j_imm[20]}}, j_imm[19:1], 1'b0};
            default: branch_adder_op = 'x;
        endcase
    end
end

endmodule
