`include "../params.svh"

module csrs(
    input clk,
    input rst,

    input inst_retired,

    input exec_csr_instr_valid,
    input [11:0] exec_csr_addr,
    input [2:0] exec_csr_funct3,
    input [4:0] exec_csr_rd,
    input [4:0] exec_csr_rs1_uimm,
    input [`XLEN-1:0] exec_csr_rs1_data,
    output logic exec_csr_exception,
    output logic [3:0] exec_csr_trap_cause,
    output logic [`XLEN-1:0] exec_csr_result,

    input trap_do_update,
    input [3:0] trap_mcause,
    input [`ALEN-1:0] trap_mepc,

    output [`XLEN-1:0] mtvec
);

enum {
    CSR_SIZE_XLEN = `XLEN,
    CSR_SIZE_32 = 'h32
} csr_size_e;

//    CSR name       addr   size            init        AND write mask
`define CSR_X_REG_LIST \
    `X(mtvec,       'h305,  CSR_SIZE_XLEN,  '0,         ~64'b10) \
    `X(mscratch,    'h340,  CSR_SIZE_XLEN,  '0,         '1) \
    `X(mepc,        'h341,  CSR_SIZE_XLEN,  '0,         ~64'b1) \
    `X(mcause,      'h342,  CSR_SIZE_XLEN,  '0,         '1) \
    `X(mcycle,      'hB00,  CSR_SIZE_XLEN,  '0,         '1) \
    `X(minstret,    'hB02,  CSR_SIZE_XLEN,  '0,         '1) \
    `X(mvendorid,   'hF11,  CSR_SIZE_32,    `MVENDORID, '1) \
    `X(marchid,     'hF12,  CSR_SIZE_XLEN,  `MARCHID,   '1) \
    `X(mimpid,      'hF13,  CSR_SIZE_XLEN,  `MIMPID,    '1) \
    `X(mhartid,     'hF14,  CSR_SIZE_XLEN,  '0,         '1) // Hardcoded because we're single-hart!

//    CSR name       addr   maps-to
`define CSR_X_VIRTUAL_LIST \
    `X(cycle,        'hC00, mcycle) \
    `X(time_,        'hC01, mcycle) \
    `X(instret,      'hC02, minstret)

enum {
    CSR_FUNCT3_CSRRW = 'b001,
    CSR_FUNCT3_CSRRS = 'b010,
    CSR_FUNCT3_CSRRC = 'b011,
    CSR_FUNCT3_CSRRWI = 'b101,
    CSR_FUNCT3_CSRRSI = 'b110,
    CSR_FUNCT3_CSRRCI = 'b111
} csr_funct3_e;

`define X(name, addr, size, init, andmask) \
    reg [size-1:0] csr_``name;
`CSR_X_REG_LIST
`undef X

assign mtvec = csr_mtvec;

wire is_readonly_csr = exec_csr_addr[11:10] == 'b11;
// CSRRS/C with a zero rs1/uimm are specified to not perform a write at all (so OK on a readonly CSR, for example)
wire is_write_instr = (exec_csr_funct3 == CSR_FUNCT3_CSRRW || exec_csr_funct3 == CSR_FUNCT3_CSRRWI) || exec_csr_rs1_uimm != '0;
// CSR_FUNCT3_CSRRW/I with rd==0 does not read at all
wire is_read_instr = (exec_csr_funct3 != CSR_FUNCT3_CSRRW || exec_csr_funct3 != CSR_FUNCT3_CSRRWI) || exec_csr_rd != '0;

logic csr_bad_addr;
wire write_exception = is_write_instr && is_readonly_csr;
assign exec_csr_exception = csr_bad_addr || write_exception;
assign exec_csr_trap_cause = trap_causes::EXC_ILLEGAL_INSTR;

// Reads
always_comb begin
    csr_bad_addr = 0;
    unique case (exec_csr_addr)
        `define X(name, addr, size, init, andmask) \
            addr: exec_csr_result = is_read_instr ? csr_``name : 'x;
        `CSR_X_REG_LIST
        `undef X

        `define X(name, addr, mapsto) \
            addr: exec_csr_result = is_read_instr ? csr_``mapsto : 'x;
        `CSR_X_VIRTUAL_LIST
        `undef X

        default: begin
            csr_bad_addr = 1;
            exec_csr_result = 'x;
        end
    endcase
end

// Writes
wire [`XLEN-1:0] write_input_data = exec_csr_funct3[2] ? exec_csr_rs1_uimm : exec_csr_rs1_data;
logic [`XLEN-1:0] write_data;
always_comb begin
    if (exec_csr_funct3 == CSR_FUNCT3_CSRRW || exec_csr_funct3 == CSR_FUNCT3_CSRRWI) begin
        write_data = write_input_data;
    end else if (exec_csr_funct3 == CSR_FUNCT3_CSRRS || exec_csr_funct3 == CSR_FUNCT3_CSRRSI) begin
        write_data = exec_csr_result | write_input_data;
    end else if (exec_csr_funct3 == CSR_FUNCT3_CSRRC || exec_csr_funct3 == CSR_FUNCT3_CSRRCI) begin
        write_data = exec_csr_result & ~write_input_data;
    end else begin
        write_data = 'x;
    end
end

always @(posedge clk) begin
    if (rst) begin
        `define X(name, addr, size, init, andmask) \
            csr_``name <= init;
        `CSR_X_REG_LIST
        `undef X
    end else begin
        csr_mcycle <= csr_mcycle + 1;
        if (inst_retired)
            csr_minstret <= csr_minstret + 1;

        if (exec_csr_instr_valid && is_write_instr && !is_readonly_csr) begin
            `define X(name, addr, size, init, andmask) \
                addr: csr_``name <= write_data & andmask;

            unique case (exec_csr_addr)
                `CSR_X_REG_LIST
                default: ;
            endcase

            `undef X
        end

        if (trap_do_update) begin
            csr_mcause <= trap_mcause;
            csr_mepc <= trap_mepc;
        end
    end
end

`undef CSR_X_REG_LIST
`undef CSR_X_VIRTUAL_LIST

endmodule
