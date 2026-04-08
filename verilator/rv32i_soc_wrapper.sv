// Wrapper for Generated RV32I SoC (debug: satp + S-mode trap)
// out[191:160]=pcReg, out[159:128]=uartValid, out[127:96]=prevStoreData
// out[95:64]=satpReg, out[63:32]=sepcReg, out[31:0]=stvalReg

module rv32i_soc (
    input  logic        clk,
    input  logic        rst,
    input  logic        imem_wr_en,
    input  logic [11:0] imem_wr_addr,
    input  logic [31:0] imem_wr_data,
    input  logic        dmem_wr_en,
    input  logic [22:0] dmem_wr_addr,
    input  logic [31:0] dmem_wr_data,
    input  logic        uart_rx_valid,
    input  logic [7:0]  uart_rx_data,
    output logic [31:0] pc_out,
    output logic        uart_tx_valid,
    output logic [31:0] uart_tx_data,
    output logic [31:0] mepc_debug,
    output logic [31:0] idex_pc_debug,
    output logic        trap_out,
    output logic [31:0] trap_cause_out,
    output logic [31:0] trap_pc_out,
    output logic        itlb_need_translate,
    output logic        itlb_hit,
    output logic        itlb_miss,
    output logic        itlb_stall,
    output logic        itlb_ptw_req,
    output logic [31:0] itlb_phys_addr,
    output logic [31:0] itlb_fetch_pc
);

    logic [191:0] packed_out;

    Sparkle_IP_RV32_SoCVerilog_rv32iSoCSynth gen_soc (
        .clk(clk),
        .rst(rst),
        ._gen_imem_wr_en(imem_wr_en),
        ._gen_imem_wr_addr(imem_wr_addr),
        ._gen_imem_wr_data(imem_wr_data),
        ._gen_dmem_wr_en(dmem_wr_en),
        ._gen_dmem_wr_addr(dmem_wr_addr),
        ._gen_dmem_wr_data(dmem_wr_data),
        .out(packed_out)
    );

    assign pc_out           = packed_out[191:160];
    assign uart_tx_valid    = |packed_out[159:128];
    assign uart_tx_data     = packed_out[127:96];

    // Debug: satp + PTW state
    assign mepc_debug           = packed_out[95:64];   // satpReg
    assign idex_pc_debug        = packed_out[63:32];   // ptwPteReg
    assign trap_cause_out       = packed_out[31:0];    // ptwVaddrReg
    assign trap_out             = 1'b0;
    assign trap_pc_out          = 32'd0;
    assign itlb_need_translate  = 1'b0;
    assign itlb_hit             = 1'b0;
    assign itlb_miss            = 1'b0;
    assign itlb_stall           = 1'b0;
    assign itlb_ptw_req         = 1'b0;
    assign itlb_phys_addr       = 32'd0;
    assign itlb_fetch_pc        = 32'd0;

endmodule
