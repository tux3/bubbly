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

    input [1:0] privilege_mode,
    input [`XLEN-1:0] mstatus,
    input [`XLEN-1:0] mepc,

    output exec_csr_instr_valid,
    output [11:0] exec_csr_addr,
    output [2:0] exec_csr_funct3,
    output [4:0] exec_csr_rd,
    output [4:0] exec_csr_rs1_uimm,
    output [`XLEN-1:0] exec_csr_rs1_data,
    input exec_csr_exception,
    input [3:0] exec_csr_trap_cause,
    input [`XLEN-1:0] exec_csr_result,

    output logic exec_system_update_mstatus_comb,
    output logic [`XLEN-1:0] exec_system_new_mstatus_comb,
    output logic [1:0] exec_system_new_privilege_mode_comb,

    output reg exec_system_output_valid,
    output reg exec_system_exception,
    output reg [3:0] exec_system_trap_cause,
    output reg exec_system_is_xret,
    output reg [`XLEN-1:0] exec_system_result
);

always_ff @(posedge clk) begin
    if (rst)
        exec_system_output_valid <= '0;
    else
        exec_system_output_valid <= input_valid && input_is_system;
end

assign exec_csr_instr_valid = input_valid && input_is_system && funct3 != 3'b100 && funct3 != '0;
assign exec_csr_addr = i_imm;
assign exec_csr_funct3 = funct3;
assign exec_csr_rd = rd;
assign exec_csr_rs1_uimm = rs1;
assign exec_csr_rs1_data = rs1_data;

wire [1:0] xret_level = funct7[4:3];
always_ff @(posedge clk) begin
    if (rst) begin
        exec_system_exception <= '0;
        exec_system_trap_cause <= 'x;
        exec_system_is_xret <= '0;
        exec_system_result <= 'x;
    end else begin
        exec_system_exception <= '0;
        exec_system_trap_cause <= 'x;
        exec_system_is_xret <= '0;
        exec_system_result <= 'x;

        if (funct3 == 3'b100) begin // Hypervisor Load/Store instructions
            exec_system_exception <= '1;
            exec_system_trap_cause <= trap_causes::EXC_ILLEGAL_INSTR;
        end else if (funct3 != '0) begin // Zicsr
            exec_system_exception <= exec_csr_exception;
            exec_system_trap_cause <= exec_csr_trap_cause;
            exec_system_result <= exec_csr_result;
        end else if (rd == '0) begin
            if (funct7 == 'b0001001) begin // SFENCE.VMA
                // Until we have paging, this is a no-op
            end else if (rs1 != '0) begin
                exec_system_exception <= '1; // Unsupported instructions
                exec_system_trap_cause <= trap_causes::EXC_ILLEGAL_INSTR;
            end else unique casez ({funct7, rs2})
                0: begin // ECALL
                    exec_system_exception <= '1;
                    if (privilege_mode == priv_levels::MACHINE)
                        exec_system_trap_cause <= trap_causes::EXC_ENV_CALL_MMODE;
                    else if (privilege_mode == priv_levels::SUPERVISOR)
                        exec_system_trap_cause <= trap_causes::EXC_ENV_CALL_SMODE;
                    else if (privilege_mode == priv_levels::USER)
                        exec_system_trap_cause <= trap_causes::EXC_ENV_CALL_UMODE;
                    else begin
                        exec_system_trap_cause <= 'x;
                        `ifndef SYNTHESIS
                        $error("[%t] Trying to execute ECALL, but current privilege mode is unknown: %h", $time, privilege_mode);
                        `endif
                    end
                end
                1: begin // EBREAK
                    exec_system_exception <= '1;
                    exec_system_trap_cause <= trap_causes::EXC_BREAKPOINT;
                end
                {7'b00??000, 5'b00010}: begin // {U,S,M}RET
                    exec_system_is_xret <= '1;

                    if (xret_level == priv_levels::MACHINE) begin
                        exec_system_exception <= privilege_mode != priv_levels::MACHINE;
                        exec_system_result <= mepc; // NOTE: Safe because mepc's guarantted to be aligned
                    end else begin
                        exec_system_exception <= '1;
                        exec_system_trap_cause <= trap_causes::EXC_ILLEGAL_INSTR;
                    end
                end
                {7'b0001000, 5'b00101}: begin // WFI
                    // As permitted by the spec, this is just a no-op
                end
                default: begin
                    exec_system_exception <= '1;
                    exec_system_trap_cause <= trap_causes::EXC_ILLEGAL_INSTR;
                end
            endcase
        end else begin
            exec_system_exception <= '1;
            exec_system_trap_cause <= trap_causes::EXC_ILLEGAL_INSTR;
        end
    end
end

always_comb begin
    exec_system_update_mstatus_comb = '0;
    exec_system_new_mstatus_comb = 'x;
    exec_system_new_privilege_mode_comb = 'x;

    // Update CSRs on xRET instruction
    if (funct3 == '0 && rd == '0 && rs1 == '0 && rs2 == 5'b00010 && funct7[6:5] == '0 && funct7[2:0] == '0) begin
        if (xret_level == priv_levels::MACHINE) begin
            exec_system_update_mstatus_comb = input_valid && input_is_system && privilege_mode == priv_levels::MACHINE;
            exec_system_new_privilege_mode_comb = mstatus[12:11];
            exec_system_new_mstatus_comb = {
                mstatus[`XLEN-1:13],
                priv_levels::MACHINE,   // New MPP
                mstatus[10:8],
                1'b1,                   // New MPIE
                mstatus[6:4],
                mstatus[7],             // New MIE
                mstatus[2:0]
            };
        end
    end
end

endmodule
