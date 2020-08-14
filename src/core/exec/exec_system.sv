`include "../params.svh"

module exec_system(
    input clk,
    input rst,
    input [`ALEN-1:0] decode_instruction_addr,
    input [4:0] opcode,
    input [4:0] rd,
    input [2:0] funct3,
    input [4:0] rs1,
    input [4:0] rs2,
    input [`XLEN-1:0] rs1_data,
    input [31:20] i_imm,
    input [6:0] funct7,

    input input_valid,
    input input_is_system,

    output exec_csr_instr_valid,
    output [11:0] exec_csr_addr,
    output [2:0] exec_csr_funct3,
    output [4:0] exec_csr_rd,
    output [4:0] exec_csr_rs1_uimm,
    output [`XLEN-1:0] exec_csr_rs1_data,
    input exec_csr_exception,
    input [`XLEN-1:0] exec_csr_result,

    output reg exec_system_output_valid,
    output reg exec_system_exception,
    output reg [`XLEN-1:0] exec_system_result
);

always_ff @(posedge clk) begin
    if (rst)
        exec_system_output_valid <= '0;
    else
        exec_system_output_valid <= input_valid && input_is_system;
end

enum {
    PRIV_LEVEL_USER = 'b00,
    PRIV_LEVEL_RESERVED1 = 'b01,
    PRIV_LEVEL_SUPERVISOR = 'b10,
    PRIV_LEVEL_MACHINE = 'b11
} priv_level_e;

assign exec_csr_instr_valid = input_valid && input_is_system && funct3 != 3'b100 && funct3 != '0;
assign exec_csr_addr = i_imm;
assign exec_csr_funct3 = funct3;
assign exec_csr_rd = rd;
assign exec_csr_rs1_uimm = rs1;
assign exec_csr_rs1_data = rs1_data;

wire [1:0] xret_level = funct7[4:3];
always_ff @(posedge clk) begin
    exec_system_exception <= '0;
    exec_system_result <= 'x;

    if (funct3 == 3'b100) begin // Hypervisor Load/Store instructions
        exec_system_exception <= '1;
    end else if (funct3 != '0) begin // Zicsr
        exec_system_exception <= exec_csr_exception;
        exec_system_result <= exec_csr_result;
    end else if (rd == '0) begin
        if (funct7 == 'b0001001) begin // SFENCE.VMA
            // Until we have paging, this is a no-op
        end else if (rs1 != '0) begin
            exec_system_exception <= '1; // Unsupported instructions
        end else unique casez ({funct7, rs2})
            0: begin // TODO: ECALL
                exec_system_exception <= '1;
            end
            1: begin // TODO: EBREAK
                exec_system_exception <= '1;
            end
            {7'b00??000, 5'b00010}: begin // {U,S,M}RET
                if (xret_level == PRIV_LEVEL_MACHINE) begin
                    exec_system_exception <= '1; // TODO: Implement MRET
                end else begin
                    exec_system_exception <= '1;
                end
            end
            {7'b0001000, 5'b00101}: begin // WFI
                // As permitted by the spec, this is just a no-op
            end
            default: begin
                exec_system_exception <= '1;
            end
        endcase
    end else begin
        exec_system_exception <= '1;
    end
end

endmodule