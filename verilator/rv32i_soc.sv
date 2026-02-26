// ============================================================================
// RV32I SoC — SystemVerilog (Verilator simulation target)
//
// Direct translation of Examples/RV32/SoC.lean Signal DSL.
// 5-stage pipeline (IF/ID/EX/WB) with CLINT, CSR, UART MMIO,
// S-mode CSRs, trap delegation, privilege tracking, MMU (Sv32 TLB+PTW).
// 115 pipeline registers, 4 byte-wide data memories, register file.
//
// Generated to match Lean simulation semantics for cross-validation.
// ============================================================================

module rv32i_soc (
    input  logic        clk,
    input  logic        rst,
    // IMEM write port (for firmware loading during reset)
    input  logic        imem_wr_en,
    input  logic [11:0] imem_wr_addr,
    input  logic [31:0] imem_wr_data,
    // UART RX input (active-high valid pulse with data byte)
    input  logic        uart_rx_valid,
    input  logic [7:0]  uart_rx_data,
    // Outputs for testbench monitoring
    output logic [31:0] pc_out,
    output logic        uart_tx_valid,
    output logic [31:0] uart_tx_data
);

    // ========================================================================
    // NOP instruction
    // ========================================================================
    localparam logic [31:0] NOP_INST = 32'h00000013; // ADDI x0, x0, 0

    // ========================================================================
    // Pipeline registers (69 total)
    // ========================================================================
    // IF stage
    logic [31:0] pcReg, pcReg_next;
    logic [31:0] fetchPC, fetchPC_next;
    logic        flushDelay, flushDelay_next;

    // IF/ID
    logic [31:0] ifid_inst, ifid_inst_next;
    logic [31:0] ifid_pc, ifid_pc_next;
    logic [31:0] ifid_pc4, ifid_pc4_next;

    // ID/EX
    logic [3:0]  idex_aluOp, idex_aluOp_next;
    logic        idex_regWrite, idex_regWrite_next;
    logic        idex_memRead, idex_memRead_next;
    logic        idex_memWrite, idex_memWrite_next;
    logic        idex_memToReg, idex_memToReg_next;
    logic        idex_branch, idex_branch_next;
    logic        idex_jump, idex_jump_next;
    logic        idex_auipc, idex_auipc_next;
    logic        idex_aluSrcB, idex_aluSrcB_next;
    logic        idex_isJalr, idex_isJalr_next;
    logic        idex_isCsr, idex_isCsr_next;
    logic        idex_isEcall, idex_isEcall_next;
    logic        idex_isMret, idex_isMret_next;
    logic [31:0] idex_rs1Val, idex_rs1Val_next;
    logic [31:0] idex_rs2Val, idex_rs2Val_next;
    logic [31:0] idex_imm, idex_imm_next;
    logic [4:0]  idex_rd, idex_rd_next;
    logic [4:0]  idex_rs1Idx, idex_rs1Idx_next;
    logic [4:0]  idex_rs2Idx, idex_rs2Idx_next;
    logic [2:0]  idex_funct3, idex_funct3_next;
    logic [31:0] idex_pc, idex_pc_next;
    logic [31:0] idex_pc4, idex_pc4_next;
    logic [11:0] idex_csrAddr, idex_csrAddr_next;
    logic [2:0]  idex_csrFunct3, idex_csrFunct3_next;

    // EX/WB
    logic [31:0] exwb_alu, exwb_alu_next;
    logic [4:0]  exwb_rd, exwb_rd_next;
    logic        exwb_regW, exwb_regW_next;
    logic        exwb_m2r, exwb_m2r_next;
    logic [31:0] exwb_pc4, exwb_pc4_next;
    logic        exwb_jump, exwb_jump_next;
    logic        exwb_isCsr, exwb_isCsr_next;
    logic [31:0] exwb_csrRdata, exwb_csrRdata_next;

    // WB history (for forwarding)
    logic [4:0]  prev_wb_addr, prev_wb_addr_next;
    logic [31:0] prev_wb_data, prev_wb_data_next;
    logic        prev_wb_en, prev_wb_en_next;

    // Store history (for store-load forwarding)
    logic [31:0] prevStoreAddr, prevStoreAddr_next;
    logic [31:0] prevStoreData, prevStoreData_next;
    logic        prevStoreEn, prevStoreEn_next;

    // CLINT
    logic [31:0] msipReg, msipReg_next;
    logic [31:0] mtimeLoReg, mtimeLoReg_next;
    logic [31:0] mtimeHiReg, mtimeHiReg_next;
    logic [31:0] mtimecmpLoReg, mtimecmpLoReg_next;
    logic [31:0] mtimecmpHiReg, mtimecmpHiReg_next;

    // CSR
    logic [31:0] mstatusReg, mstatusReg_next;
    logic [31:0] mieReg, mieReg_next;
    logic [31:0] mtvecReg, mtvecReg_next;
    logic [31:0] mscratchReg, mscratchReg_next;
    logic [31:0] mepcReg, mepcReg_next;
    logic [31:0] mcauseReg, mcauseReg_next;
    logic [31:0] mtvalReg, mtvalReg_next;

    // AI MMIO
    logic [31:0] aiStatusReg, aiStatusReg_next;
    logic [31:0] aiInputReg, aiInputReg_next;

    // Sub-word
    logic [2:0]  exwb_funct3, exwb_funct3_next;

    // M-extension
    logic        idex_isMext, idex_isMext_next;

    // A-extension
    logic        reservationValid, reservationValid_next;
    logic [31:0] reservationAddr, reservationAddr_next;
    logic        idex_isAMO, idex_isAMO_next;
    logic [4:0]  idex_amoOp, idex_amoOp_next;
    logic        exwb_isAMO, exwb_isAMO_next;
    logic [4:0]  exwb_amoOp, exwb_amoOp_next;
    logic        pendingWriteEn, pendingWriteEn_next;
    logic [31:0] pendingWriteAddr, pendingWriteAddr_next;
    logic [31:0] pendingWriteData, pendingWriteData_next;

    // S-mode CSRs + privilege (69-78)
    logic [1:0]  privMode, privMode_next;
    logic [31:0] sieReg, sieReg_next;
    logic [31:0] stvecReg, stvecReg_next;
    logic [31:0] sscratchReg, sscratchReg_next;
    logic [31:0] sepcReg, sepcReg_next;
    logic [31:0] scauseReg, scauseReg_next;
    logic [31:0] stvalReg, stvalReg_next;
    logic [31:0] satpReg, satpReg_next;
    logic [31:0] medelegReg, medelegReg_next;
    logic [31:0] midelegReg, midelegReg_next;

    // MMU TLB + PTW (79-106)
    logic [2:0]  mmuState, mmuState_next;
    logic [2:0]  ptwState, ptwState_next;
    logic [31:0] ptwVaddr, ptwVaddr_next;
    logic [31:0] ptwPte, ptwPte_next;
    logic        ptwMega, ptwMega_next;
    logic [1:0]  replPtr, replPtr_next;
    // TLB entry 0
    logic        tlb0Valid, tlb0Valid_next;
    logic [19:0] tlb0VPN, tlb0VPN_next;
    logic [21:0] tlb0PPN, tlb0PPN_next;
    logic [7:0]  tlb0Flags, tlb0Flags_next;
    logic        tlb0Mega, tlb0Mega_next;
    // TLB entry 1
    logic        tlb1Valid, tlb1Valid_next;
    logic [19:0] tlb1VPN, tlb1VPN_next;
    logic [21:0] tlb1PPN, tlb1PPN_next;
    logic [7:0]  tlb1Flags, tlb1Flags_next;
    logic        tlb1Mega, tlb1Mega_next;
    // TLB entry 2
    logic        tlb2Valid, tlb2Valid_next;
    logic [19:0] tlb2VPN, tlb2VPN_next;
    logic [21:0] tlb2PPN, tlb2PPN_next;
    logic [7:0]  tlb2Flags, tlb2Flags_next;
    logic        tlb2Mega, tlb2Mega_next;
    // TLB entry 3
    logic        tlb3Valid, tlb3Valid_next;
    logic [19:0] tlb3VPN, tlb3VPN_next;
    logic [21:0] tlb3PPN, tlb3PPN_next;
    logic [7:0]  tlb3Flags, tlb3Flags_next;
    logic        tlb3Mega, tlb3Mega_next;
    // PTW ifetch tracking
    logic        ptwIsIfetch, ptwIsIfetch_next;
    logic        ifetchFaultPending, ifetchFaultPending_next;

    // Pipeline additions (107-108)
    logic        idex_isSret, idex_isSret_next;
    logic        idex_isSFenceVMA, idex_isSFenceVMA_next;

    // UART 8250 registers (109-114)
    logic [7:0]  uartLCR, uartLCR_next;
    logic [7:0]  uartIER, uartIER_next;
    logic [7:0]  uartMCR, uartMCR_next;
    logic [7:0]  uartSCR, uartSCR_next;
    logic [7:0]  uartDLL, uartDLL_next;
    logic [7:0]  uartDLM, uartDLM_next;
    // UART RX-only registers (Verilator only, not in Lean)
    logic [7:0]  uartRxBuf, uartRxBuf_next;
    logic        uartRxReady, uartRxReady_next;

    // ========================================================================
    // Memories
    // ========================================================================

    // IMEM: 4096 x 32-bit (combinational read, writable for init)
    logic [31:0] imem [0:4095];
    logic [31:0] imem_rdata;
    wire  [11:0] imem_addr = fetchPC[13:2];
    assign imem_rdata = imem[imem_addr];

    // DRAM instruction fetch: combinational read from same DMEM byte arrays
    wire [22:0] ifetch_word_addr = fetchPC[24:2];
    wire [7:0] dram_ifetch_b0 = dmem_b0[ifetch_word_addr];
    wire [7:0] dram_ifetch_b1 = dmem_b1[ifetch_word_addr];
    wire [7:0] dram_ifetch_b2 = dmem_b2[ifetch_word_addr];
    wire [7:0] dram_ifetch_b3 = dmem_b3[ifetch_word_addr];
    wire [31:0] dram_ifetch_word = {dram_ifetch_b3, dram_ifetch_b2, dram_ifetch_b1, dram_ifetch_b0};
    wire fetchInDRAM = fetchPC[31];
    wire [31:0] final_imem_rdata = fetchInDRAM ? dram_ifetch_word : imem_rdata;

    // DMEM: 4 byte-wide memories (each 8M x 8-bit = 32 MB total), synchronous read
    logic [7:0] dmem_b0 [0:8388607];
    logic [7:0] dmem_b1 [0:8388607];
    logic [7:0] dmem_b2 [0:8388607];
    logic [7:0] dmem_b3 [0:8388607];
    logic [7:0] dmem_b0_rdata, dmem_b1_rdata, dmem_b2_rdata, dmem_b3_rdata;

    // Register file: 32 x 32-bit (combinational read, synchronous write)
    logic [31:0] regfile [0:31];

    // ========================================================================
    // Combinational Logic
    // ========================================================================

    // Forwarding / WB data
    wire wbRdNz = (exwb_rd != 5'd0);
    wire [4:0]  wb_addr = exwb_rd;
    wire        wb_en   = exwb_regW & wbRdNz;
    wire [31:0] wb_data_non_mem = exwb_isCsr ? exwb_csrRdata :
                                  (exwb_jump ? exwb_pc4 : exwb_alu);

    wire fwd_rs1_match = wb_en & (wb_addr == idex_rs1Idx);
    wire fwd_rs2_match = wb_en & (wb_addr == idex_rs2Idx);

    // Approximate forwarding (for DMEM address calc, no load forwarding)
    wire [31:0] fwd_val_approx  = exwb_m2r ? idex_rs1Val : wb_data_non_mem;
    wire [31:0] ex_rs1_approx   = fwd_rs1_match ? fwd_val_approx : idex_rs1Val;
    wire [31:0] fwd_val2_approx = exwb_m2r ? idex_rs2Val : wb_data_non_mem;
    wire [31:0] ex_rs2_approx   = fwd_rs2_match ? fwd_val2_approx : idex_rs2Val;
    wire [31:0] alu_a_approx    = idex_auipc ? idex_pc : ex_rs1_approx;
    wire [31:0] alu_b_approx    = idex_aluSrcB ? idex_imm : ex_rs2_approx;

    // ALU (approximate, for address calculation)
    wire [31:0] alu_result_approx;
    alu_compute alu_approx_inst (
        .op(idex_aluOp), .a(alu_a_approx), .b(alu_b_approx),
        .result(alu_result_approx)
    );

    // Bus address decode (EX stage)
    wire [15:0] busAddrHi_ex = alu_result_approx[31:16];
    wire isCLINT_ex = (busAddrHi_ex == 16'h0200);
    wire is_mmio_ex = alu_result_approx[30];
    wire [7:0] busAddrByte24_ex = alu_result_approx[31:24];
    wire isUART_ex = (busAddrByte24_ex == 8'h10);
    wire isDMEM_ex  = !isCLINT_ex & !is_mmio_ex & !isUART_ex;

    // DMEM address and write enable (23-bit word address = 8M words = 32 MB)
    wire [22:0] dmem_addr_ex = alu_result_approx[24:2];
    wire dmem_we = (idex_memWrite & isDMEM_ex) | pendingWriteEn;

    // MMU/PTW bypass and state decode (early, for DMEM addr mux and stall)
    wire satpMode = satpReg[31];
    wire isMmode = (privMode == 2'd3);
    wire bypassMMU = isMmode | !satpMode;
    // MMU FSM: IDLE=0, TLB_LOOKUP=1, PTW_WALK=2, DONE=3, FAULT=4
    wire isMMUIdle   = (mmuState == 3'd0);
    wire isTLBLookup = (mmuState == 3'd1);
    wire isPTWWalk   = (mmuState == 3'd2);
    wire isMMUDone   = (mmuState == 3'd3);
    wire isMMUFault  = (mmuState == 3'd4);
    // PTW FSM: IDLE=0, L1_REQ=1, L1_WAIT=2, L0_REQ=3, L0_WAIT=4, DONE=5, FAULT=6
    wire ptwIsIdle   = (ptwState == 3'd0);
    wire ptwIsL1Req  = (ptwState == 3'd1);
    wire ptwIsL1Wait = (ptwState == 3'd2);
    wire ptwIsL0Req  = (ptwState == 3'd3);
    wire ptwIsL0Wait = (ptwState == 3'd4);
    wire ptwIsDone   = (ptwState == 3'd5);
    wire ptwIsFault  = (ptwState == 3'd6);
    // PTW memory address generation
    wire [21:0] satpPPN = satpReg[21:0];
    wire [31:0] l1Addr = {satpPPN, 10'd0} + {20'd0, ptwVaddr[31:22], 2'd0};
    wire [21:0] ptePPNFull_w = ptwPte[31:10];
    wire [31:0] l0Addr = {ptePPNFull_w, 10'd0} + {20'd0, ptwVaddr[21:12], 2'd0};
    wire ptwMemActive = ptwIsL1Req | ptwIsL0Req;
    wire [31:0] ptwMemAddr = ptwIsL1Req ? l1Addr : l0Addr;
    wire [22:0] ptwMemWordAddr = ptwMemAddr[24:2];
    // MMU stall: busy (not IDLE/DONE/FAULT) and not bypassed
    wire mmuBusy = !(isMMUIdle | isMMUDone | isMMUFault);
    wire mmuStall = mmuBusy & !bypassMMU;

    // DMEM read address: PTW overrides pipeline during page table walk
    wire [22:0] dmem_addr = ptwMemActive ? ptwMemWordAddr :
                             pendingWriteEn ? pendingWriteAddr[24:2] : dmem_addr_ex;

    // Sub-word store byte-enable logic
    wire [1:0] storeByteOff = alu_result_approx[1:0];
    wire [1:0] storeFunct3Low = idex_funct3[1:0];
    wire isSB = (storeFunct3Low == 2'd0);
    wire isSH = (storeFunct3Low == 2'd1);
    wire isSW = (storeFunct3Low == 2'd2);

    wire storeHalfLow  = !alu_result_approx[1];
    wire storeHalfHigh = alu_result_approx[1];

    wire b0we = isSW | (isSH & storeHalfLow)  | (isSB & (storeByteOff == 2'd0));
    wire b1we = isSW | (isSH & storeHalfLow)  | (isSB & (storeByteOff == 2'd1));
    wire b2we = isSW | (isSH & storeHalfHigh) | (isSB & (storeByteOff == 2'd2));
    wire b3we = isSW | (isSH & storeHalfHigh) | (isSB & (storeByteOff == 2'd3));

    // Pending write overrides: all bytes enabled for word-sized AMO write
    wire byte0_we = (dmem_we & b0we) | pendingWriteEn;
    wire byte1_we = (dmem_we & b1we) | pendingWriteEn;
    wire byte2_we = (dmem_we & b2we) | pendingWriteEn;
    wire byte3_we = (dmem_we & b3we) | pendingWriteEn;

    // Byte write data (mux pending write data for AMO writeback)
    wire [7:0] rs2_byte0 = ex_rs2_approx[7:0];
    wire [7:0] rs2_byte1 = ex_rs2_approx[15:8];
    wire [7:0] rs2_byte2 = ex_rs2_approx[23:16];
    wire [7:0] rs2_byte3 = ex_rs2_approx[31:24];

    wire [7:0] byte0_wdata_ex = rs2_byte0;
    wire [7:0] byte1_wdata_ex = isSB ? rs2_byte0 : rs2_byte1;
    wire [7:0] byte2_wdata_ex = isSW ? rs2_byte2 : rs2_byte0;
    wire [7:0] byte3_wdata_ex = isSW ? rs2_byte3 : (isSB ? rs2_byte0 : rs2_byte1);

    wire [7:0] byte0_wdata = pendingWriteEn ? pendingWriteData[7:0]   : byte0_wdata_ex;
    wire [7:0] byte1_wdata = pendingWriteEn ? pendingWriteData[15:8]  : byte1_wdata_ex;
    wire [7:0] byte2_wdata = pendingWriteEn ? pendingWriteData[23:16] : byte2_wdata_ex;
    wire [7:0] byte3_wdata = pendingWriteEn ? pendingWriteData[31:24] : byte3_wdata_ex;

    // DMEM read data reconstruction
    wire [31:0] dmem_rdata = {dmem_b3_rdata, dmem_b2_rdata,
                               dmem_b1_rdata, dmem_b0_rdata};

    // ========================================================================
    // MMU TLB lookup and PTW combinational signals
    // ========================================================================
    wire [19:0] dVPN = alu_result_approx[31:12];
    wire tlb0FullMatch = (tlb0VPN == dVPN);
    wire tlb0MegaMatch = (tlb0VPN[19:10] == dVPN[19:10]);
    wire tlb0VPNMatch = tlb0Mega ? tlb0MegaMatch : tlb0FullMatch;
    wire tlb0Hit = tlb0Valid & tlb0VPNMatch;
    wire tlb1FullMatch = (tlb1VPN == dVPN);
    wire tlb1MegaMatch = (tlb1VPN[19:10] == dVPN[19:10]);
    wire tlb1VPNMatch = tlb1Mega ? tlb1MegaMatch : tlb1FullMatch;
    wire tlb1Hit = tlb1Valid & tlb1VPNMatch;
    wire tlb2FullMatch = (tlb2VPN == dVPN);
    wire tlb2MegaMatch = (tlb2VPN[19:10] == dVPN[19:10]);
    wire tlb2VPNMatch = tlb2Mega ? tlb2MegaMatch : tlb2FullMatch;
    wire tlb2Hit = tlb2Valid & tlb2VPNMatch;
    wire tlb3FullMatch = (tlb3VPN == dVPN);
    wire tlb3MegaMatch = (tlb3VPN[19:10] == dVPN[19:10]);
    wire tlb3VPNMatch = tlb3Mega ? tlb3MegaMatch : tlb3FullMatch;
    wire tlb3Hit = tlb3Valid & tlb3VPNMatch;
    wire anyTLBHit = tlb0Hit | tlb1Hit | tlb2Hit | tlb3Hit;

    // D-side MMU request
    wire dMemAccess = idex_memRead | idex_memWrite;
    wire needTranslateD = dMemAccess & !bypassMMU;

    // PTW request: TLB miss during TLB_LOOKUP
    wire ptwReq = isTLBLookup & !anyTLBHit;

    // PTE fields from dmem_rdata (valid in L1_WAIT/L0_WAIT states)
    wire dmemPteValid  = dmem_rdata[0];
    wire dmemPteRBit   = dmem_rdata[1];
    wire dmemPteXBit   = dmem_rdata[3];
    wire dmemPteIsLeaf = dmemPteRBit | dmemPteXBit;
    wire dmemPteInvalid = !dmemPteValid;

    // PTE data ready in WAIT states
    wire isDataReady = ptwIsL1Wait | ptwIsL0Wait;

    // PTW state transition targets
    wire [2:0] nextFromL1Wait = dmemPteInvalid ? 3'd6 :
                                 dmemPteIsLeaf ? 3'd5 : 3'd3;
    wire [2:0] nextFromL0Wait = dmemPteInvalid ? 3'd6 :
                                 dmemPteIsLeaf ? 3'd5 : 3'd6;

    // TLB fill on PTW DONE
    wire tlbFill = ptwIsDone;
    wire [19:0] fillVPN = ptwVaddr[31:12];
    wire [21:0] fillPPN = ptwPte[31:10];
    wire [7:0]  fillFlags = ptwPte[7:0];
    wire doFill0 = tlbFill & (replPtr == 2'd0);
    wire doFill1 = tlbFill & (replPtr == 2'd1);
    wire doFill2 = tlbFill & (replPtr == 2'd2);
    wire doFill3 = tlbFill & (replPtr == 2'd3);

    // Store-load forwarding
    wire [29:0] storeAddrHi = prevStoreAddr[31:2];
    wire [29:0] loadAddrHi  = exwb_alu[31:2];
    wire addrMatch = (storeAddrHi == loadAddrHi);
    wire storeLoadMatch = prevStoreEn & addrMatch;
    wire [31:0] dmemRdataFwd = storeLoadMatch ? prevStoreData : dmem_rdata;

    // CLINT read
    wire [15:0] clintOffset_wb = exwb_alu[15:0];
    wire [31:0] clintRdata =
        (clintOffset_wb == 16'h0000) ? msipReg :
        (clintOffset_wb == 16'h4000) ? mtimecmpLoReg :
        (clintOffset_wb == 16'h4004) ? mtimecmpHiReg :
        (clintOffset_wb == 16'hBFF8) ? mtimeLoReg :
        (clintOffset_wb == 16'hBFFC) ? mtimeHiReg :
        32'd0;

    // Bus address decode (WB stage)
    wire isCLINT_wb = (exwb_alu[31:16] == 16'h0200);
    wire is_mmio_wb = exwb_alu[30];

    // MMIO read
    wire [3:0] mmioOffset_wb = exwb_alu[3:0];
    wire [31:0] mmioRdata =
        (mmioOffset_wb == 4'h0) ? aiStatusReg :
        (mmioOffset_wb == 4'h8) ? 32'hDEADBEEF :
        32'd0;

    // UART 8250 read logic (WB stage)
    wire isUART_wb = (exwb_alu[31:24] == 8'h10);
    wire [2:0] uartOffset_wb = exwb_alu[2:0];
    wire uartDLAB_wb = uartLCR[7];
    wire [31:0] uartRd0 = uartDLAB_wb ? {24'd0, uartDLL} : {24'd0, uartRxBuf};
    wire [31:0] uartRd1 = uartDLAB_wb ? {24'd0, uartDLM} : {24'd0, uartIER};
    wire [31:0] uartRd2 = 32'h00000001;  // IIR: no interrupt pending
    wire [31:0] uartRd3 = {24'd0, uartLCR};
    wire [31:0] uartRd4 = {24'd0, uartMCR};
    wire [31:0] uartRd5 = {24'd0, 8'h60 | {7'd0, uartRxReady}};  // LSR: THRE+TEMT + DR
    wire [31:0] uartRd7 = {24'd0, uartSCR};
    wire [31:0] uartRdata =
        (uartOffset_wb == 3'd0) ? uartRd0 :
        (uartOffset_wb == 3'd1) ? uartRd1 :
        (uartOffset_wb == 3'd2) ? uartRd2 :
        (uartOffset_wb == 3'd3) ? uartRd3 :
        (uartOffset_wb == 3'd4) ? uartRd4 :
        (uartOffset_wb == 3'd5) ? uartRd5 :
        (uartOffset_wb == 3'd7) ? uartRd7 :
        32'd0;

    // Raw bus read data
    wire [31:0] busRdataRaw = isCLINT_wb ? clintRdata :
                               (isUART_wb ? uartRdata :
                               (is_mmio_wb ? mmioRdata : dmemRdataFwd));

    // Sub-word load extraction
    wire [1:0] loadByteOff = exwb_alu[1:0];
    wire [7:0] loadByte0 = busRdataRaw[7:0];
    wire [7:0] loadByte1 = busRdataRaw[15:8];
    wire [7:0] loadByte2 = busRdataRaw[23:16];
    wire [7:0] loadByte3 = busRdataRaw[31:24];

    wire [7:0] selByte = (loadByteOff == 2'd0) ? loadByte0 :
                          (loadByteOff == 2'd1) ? loadByte1 :
                          (loadByteOff == 2'd2) ? loadByte2 :
                          loadByte3;

    wire [15:0] selHalf = exwb_alu[1] ? busRdataRaw[31:16] : busRdataRaw[15:0];

    // Sign/zero extend byte
    wire [31:0] byteSext = {{24{selByte[7]}}, selByte};
    wire [31:0] byteZext = {24'd0, selByte};

    // Sign/zero extend halfword
    wire [31:0] halfSext = {{16{selHalf[15]}}, selHalf};
    wire [31:0] halfZext = {16'd0, selHalf};

    // Load extraction mux (funct3: 000=LB, 001=LH, 010=LW, 100=LBU, 101=LHU)
    wire [31:0] loadExtracted =
        (exwb_funct3 == 3'd0) ? byteSext :
        (exwb_funct3 == 3'd1) ? halfSext :
        (exwb_funct3 == 3'd4) ? byteZext :
        (exwb_funct3 == 3'd5) ? halfZext :
        busRdataRaw;

    // Gate: only use extracted value for loads
    wire [31:0] busRdata = exwb_m2r ? loadExtracted : busRdataRaw;

    // AMO compute: read-modify-write for non-LR/SC atomics
    wire exwb_isLR  = exwb_isAMO & (exwb_amoOp == 5'b00010);
    wire exwb_isSC  = exwb_isAMO & (exwb_amoOp == 5'b00011);

    wire [31:0] amo_new_val;
    amo_compute amo_inst (
        .amoOp(exwb_amoOp), .memVal(busRdataRaw), .rs2Val(prevStoreData),
        .result(amo_new_val)
    );

    // WB result: SC.W writes 0 (always succeeds, single-hart)
    wire [31:0] wb_result = exwb_isSC ? 32'd0 :
                             exwb_isCsr ? exwb_csrRdata :
                             (exwb_jump ? exwb_pc4 :
                             (exwb_m2r ? busRdata : exwb_alu));
    wire [31:0] wb_data = wb_result;

    // Full forwarding (with memory data)
    wire [31:0] ex_rs1 = fwd_rs1_match ? wb_data : idex_rs1Val;
    wire [31:0] ex_rs2 = fwd_rs2_match ? wb_data : idex_rs2Val;
    wire [31:0] alu_a  = idex_auipc ? idex_pc : ex_rs1;
    wire [31:0] alu_b  = idex_aluSrcB ? idex_imm : ex_rs2;

    // ALU (full)
    wire [31:0] alu_result_raw;
    alu_compute alu_full_inst (
        .op(idex_aluOp), .a(alu_a), .b(alu_b), .result(alu_result_raw)
    );

    // M-extension computation
    wire [31:0] mext_result;
    mext_compute mext_inst (
        .funct3(idex_funct3), .rs1(ex_rs1), .rs2(ex_rs2), .result(mext_result)
    );
    wire [31:0] alu_result = idex_isMext ? mext_result : alu_result_raw;

    // Branch comparator
    wire branchCond;
    branch_comp branch_inst (
        .funct3(idex_funct3), .a(ex_rs1), .b(ex_rs2), .taken(branchCond)
    );

    wire branchTaken = idex_branch & branchCond;
    wire [31:0] brTarget = idex_pc + idex_imm;
    wire [31:0] jalrTarget = (ex_rs1 + idex_imm) & 32'hFFFFFFFE;
    wire [31:0] jumpTarget = idex_isJalr ? jalrTarget : brTarget;

    // ========================================================================
    // Timer / Interrupts
    // ========================================================================
    wire hiGt = (mtimecmpHiReg < mtimeHiReg);
    wire hiEq = (mtimeHiReg == mtimecmpHiReg);
    wire loGe = !(mtimeLoReg < mtimecmpLoReg);
    wire timerIrq = hiGt | (hiEq & loGe);
    wire swIrq = msipReg[0];

    wire [31:0] mipValue = (timerIrq ? 32'h00000080 : 32'd0) |
                            (swIrq    ? 32'h00000008 : 32'd0);

    // ========================================================================
    // CSR read
    // ========================================================================
    // SSTATUS: masked view of mstatus
    wire [31:0] sstatus_mask = 32'h000C0122;
    wire [31:0] sstatus_view = mstatusReg & sstatus_mask;

    wire [31:0] csr_rdata =
        (idex_csrAddr == 12'h300) ? mstatusReg :
        (idex_csrAddr == 12'h304) ? mieReg :
        (idex_csrAddr == 12'h305) ? mtvecReg :
        (idex_csrAddr == 12'h340) ? mscratchReg :
        (idex_csrAddr == 12'h341) ? mepcReg :
        (idex_csrAddr == 12'h342) ? mcauseReg :
        (idex_csrAddr == 12'h343) ? mtvalReg :
        (idex_csrAddr == 12'h344) ? mipValue :
        (idex_csrAddr == 12'h301) ? 32'h40001101 :  // misa: RV32IMA
        (idex_csrAddr == 12'hF14) ? 32'd0 :          // mhartid
        (idex_csrAddr == 12'h302) ? medelegReg :
        (idex_csrAddr == 12'h303) ? midelegReg :
        (idex_csrAddr == 12'h100) ? sstatus_view :    // sstatus
        (idex_csrAddr == 12'h104) ? sieReg :
        (idex_csrAddr == 12'h105) ? stvecReg :
        (idex_csrAddr == 12'h140) ? sscratchReg :
        (idex_csrAddr == 12'h141) ? sepcReg :
        (idex_csrAddr == 12'h142) ? scauseReg :
        (idex_csrAddr == 12'h143) ? stvalReg :
        (idex_csrAddr == 12'h144) ? 32'd0 :           // sip
        (idex_csrAddr == 12'h180) ? satpReg :
        32'd0;

    // ========================================================================
    // Trap logic
    // ========================================================================
    wire mstatusMIE  = mstatusReg[3];
    wire mstatusMPIE = mstatusReg[7];
    wire mieMTIE     = mieReg[7];
    wire mieMSIE     = mieReg[3];

    wire timerIntEnabled = mstatusMIE & mieMTIE & timerIrq;
    wire swIntEnabled    = mstatusMIE & mieMSIE & swIrq;
    // Page fault from MMU FAULT state (D-side: load=13, store=15)
    wire pageFault = isMMUFault & !bypassMMU;
    wire isStoreFault = pageFault & idex_memWrite;
    wire [31:0] pageFaultCause = isStoreFault ? 32'h0000000F : 32'h0000000D;

    wire trap_taken      = idex_isEcall | pageFault | timerIntEnabled | swIntEnabled;

    // ECALL cause depends on privilege level
    wire [31:0] ecallCause = (privMode == 2'd0) ? 32'h00000008 :
                              (privMode == 2'd1) ? 32'h00000009 :
                              32'h0000000B;

    wire [31:0] trapCause = idex_isEcall ? ecallCause :
                             pageFault       ? pageFaultCause :
                             timerIntEnabled ? 32'h80000007 :
                             swIntEnabled    ? 32'h80000003 :
                             32'd0;

    // Trap delegation
    wire isInterrupt = trapCause[31];
    wire [4:0] causeIdx = trapCause[4:0];
    wire medelegBit = medelegReg[causeIdx];
    wire midelegBit = midelegReg[causeIdx];
    wire delegated = isInterrupt ? midelegBit : medelegBit;
    wire privLeS = !(privMode > 2'd1);
    wire trapToS = trap_taken & delegated & privLeS;
    wire trapToM = trap_taken & !trapToS;

    wire [31:0] mtvec_base = mtvecReg & 32'hFFFFFFFC;
    wire [31:0] stvec_base = stvecReg & 32'hFFFFFFFC;
    wire [31:0] trap_target = trapToS ? stvec_base : mtvec_base;
    wire [31:0] mret_target = mepcReg;
    wire [31:0] sret_target = sepcReg;

    // MPP and SPP for privilege mode transitions
    wire [1:0] mpp = mstatusReg[12:11];
    wire [1:0] sretPriv = {1'b0, mstatusReg[8]};

    // ========================================================================
    // Control flow
    // ========================================================================
    wire flush = branchTaken | idex_jump | trap_taken | idex_isMret | idex_isSret | idex_isSFenceVMA;
    wire flushOrDelay = flush | flushDelay;

    // ========================================================================
    // Decode (ID stage)
    // ========================================================================
    wire [6:0] id_opcode = ifid_inst[6:0];
    wire [4:0] id_rd     = ifid_inst[11:7];
    wire [2:0] id_funct3 = ifid_inst[14:12];
    wire [4:0] id_rs1    = ifid_inst[19:15];
    wire [4:0] id_rs2    = ifid_inst[24:20];
    wire [6:0] id_funct7 = ifid_inst[31:25];

    // Immediate generation
    wire [31:0] id_imm_raw;
    imm_gen imm_inst (.inst(ifid_inst), .opcode(id_opcode), .imm(id_imm_raw));
    // AMO instructions use rs1 as address directly (imm = 0)
    wire [31:0] id_imm = id_isAMO ? 32'd0 : id_imm_raw;

    // ALU control
    wire [3:0] id_aluOp;
    alu_control alu_ctrl_inst (
        .opcode(id_opcode), .funct3(id_funct3), .funct7(id_funct7),
        .alu_op(id_aluOp)
    );

    // Control signals
    wire id_isALUrr  = (id_opcode == 7'b0110011);
    wire id_isALUimm = (id_opcode == 7'b0010011);
    wire id_isLoad   = (id_opcode == 7'b0000011);
    wire id_isStore  = (id_opcode == 7'b0100011);
    wire id_isBranch = (id_opcode == 7'b1100011);
    wire id_isLUI    = (id_opcode == 7'b0110111);
    wire id_isAUIPC  = (id_opcode == 7'b0010111);
    wire id_isJAL    = (id_opcode == 7'b1101111);
    wire id_isJALR   = (id_opcode == 7'b1100111);
    wire id_isSystem = (id_opcode == 7'b1110011);

    wire id_aluSrcB  = id_isALUimm | id_isLoad | id_isStore | id_isLUI |
                        id_isAUIPC | id_isJAL | id_isJALR | id_isAMO;
    wire id_regWrite = id_isALUrr | id_isALUimm | id_isLoad | id_isLUI |
                        id_isAUIPC | id_isJAL | id_isJALR | id_isAMO | id_isCsr;
    wire id_memRead  = id_isLoad | id_isLR | id_isAMOrw;
    wire id_memWrite = id_isStore | id_isSC;
    wire id_memToReg = id_isLoad | id_isLR | id_isAMOrw;
    wire id_jump     = id_isJAL | id_isJALR;
    wire id_auipc    = id_isAUIPC | id_isJAL;
    wire id_f3isZero = (id_funct3 == 3'd0);
    wire id_isCsr    = id_isSystem & !id_f3isZero;
    wire id_isEcall  = id_isSystem & id_f3isZero & (ifid_inst[31:20] == 12'h000);
    wire [11:0] id_csrAddr = ifid_inst[31:20];
    wire isMretField = (ifid_inst[31:20] == 12'h302);
    wire id_isMret   = id_isSystem & isMretField;
    // M-extension: R-type with funct7 = 0000001
    wire id_isMext   = id_isALUrr & (id_funct7 == 7'b0000001);
    // A-extension: opcode = 0101111
    wire id_isAMO    = (id_opcode == 7'b0101111);
    wire [4:0] id_amoOp = ifid_inst[31:27];  // funct7[6:2]
    wire id_isLR     = id_isAMO & (id_amoOp == 5'b00010);
    wire id_isSC     = id_isAMO & (id_amoOp == 5'b00011);
    wire id_isAMOrw  = id_isAMO & !id_isLR & !id_isSC;

    // SRET: funct12 = 0x102, SYSTEM opcode, funct3 = 0
    wire id_isSret = id_isSystem & id_f3isZero & (ifid_inst[31:20] == 12'h102);
    // SFENCE.VMA: funct7 = 0b0001001, funct3 = 0, SYSTEM opcode
    wire id_isSFenceVMA = id_isSystem & id_f3isZero & (id_funct7 == 7'b0001001);

    // AMO stall: classify EX stage AMO type
    wire idex_isLR   = idex_isAMO & (idex_amoOp == 5'b00010);
    wire idex_isSC   = idex_isAMO & (idex_amoOp == 5'b00011);
    wire idex_isAMOrw = idex_isAMO & !idex_isLR & !idex_isSC;

    // Hazard detection (+ AMO stall for delayed write)
    wire loadUseHazard = idex_memRead & (idex_rd != 5'd0) &
                         ((idex_rd == id_rs1) | (idex_rd == id_rs2));
    wire stall = loadUseHazard | idex_isAMOrw | pendingWriteEn | mmuStall;
    wire squash = stall | flushOrDelay;

    // ========================================================================
    // Register file read (combinational)
    // ========================================================================
    wire [4:0] rf_rs1_addr = stall ? id_rs1 : ifid_inst[19:15];
    wire [4:0] rf_rs2_addr = stall ? id_rs2 : ifid_inst[24:20];

    wire [31:0] rf_rs1_raw = regfile[rf_rs1_addr];
    wire [31:0] rf_rs2_raw = regfile[rf_rs2_addr];

    // WB forwarding to ID
    wire wb_fwd_rs1   = wb_en & (wb_addr == id_rs1);
    wire wb_fwd_rs2   = wb_en & (wb_addr == id_rs2);
    wire prev_fwd_rs1 = prev_wb_en & (prev_wb_addr == id_rs1);
    wire prev_fwd_rs2 = prev_wb_en & (prev_wb_addr == id_rs2);

    wire [31:0] rf_rs1_bypassed = wb_fwd_rs1 ? wb_data :
                                   (prev_fwd_rs1 ? prev_wb_data : rf_rs1_raw);
    wire [31:0] rf_rs2_bypassed = wb_fwd_rs2 ? wb_data :
                                   (prev_fwd_rs2 ? prev_wb_data : rf_rs2_raw);

    wire [31:0] id_rs1Val = (id_rs1 == 5'd0) ? 32'd0 : rf_rs1_bypassed;
    wire [31:0] id_rs2Val = (id_rs2 == 5'd0) ? 32'd0 : rf_rs2_bypassed;

    // ========================================================================
    // CLINT write
    // ========================================================================
    wire [15:0] clintOffset = alu_result_approx[15:0];
    wire clintWE = idex_memWrite & isCLINT_ex;

    wire [31:0] mtimeLoInc = mtimeLoReg + 32'd1;
    wire mtimeCarry = (mtimeLoInc == 32'd0);
    wire [31:0] mtimeHiInc = mtimeCarry ? (mtimeHiReg + 32'd1) : mtimeHiReg;

    // ========================================================================
    // MMIO write
    // ========================================================================
    wire mmioWE = idex_memWrite & is_mmio_ex;
    wire [3:0] mmioOffset_ex = alu_result_approx[3:0];

    // ========================================================================
    // CSR write logic
    // ========================================================================
    wire csrIsImm = idex_csrFunct3[2];
    wire [31:0] csrZimm = {27'd0, idex_rs1Idx};
    wire [31:0] csrWdata = csrIsImm ? csrZimm : ex_rs1;
    wire [1:0] csrF3Low = idex_csrFunct3[1:0];
    wire csrIsRW = (csrF3Low == 2'b01);
    wire csrIsRS = (csrF3Low == 2'b10);
    wire csrIsRC = (csrF3Low == 2'b11);

    function automatic [31:0] mkCsrNewVal(input [31:0] oldVal, input [31:0] wdata,
                                           input rw, rs, rc);
        if (rw)      mkCsrNewVal = wdata;
        else if (rs) mkCsrNewVal = oldVal | wdata;
        else if (rc) mkCsrNewVal = oldVal & ~wdata;
        else         mkCsrNewVal = oldVal;
    endfunction

    wire [31:0] mstatusNewCSR  = mkCsrNewVal(mstatusReg,  csrWdata, csrIsRW, csrIsRS, csrIsRC);
    wire [31:0] mieNewCSR      = mkCsrNewVal(mieReg,      csrWdata, csrIsRW, csrIsRS, csrIsRC);
    wire [31:0] mtvecNewCSR    = mkCsrNewVal(mtvecReg,    csrWdata, csrIsRW, csrIsRS, csrIsRC);
    wire [31:0] mscratchNewCSR = mkCsrNewVal(mscratchReg, csrWdata, csrIsRW, csrIsRS, csrIsRC);
    wire [31:0] mepcNewCSR     = mkCsrNewVal(mepcReg,     csrWdata, csrIsRW, csrIsRS, csrIsRC);
    wire [31:0] mcauseNewCSR   = mkCsrNewVal(mcauseReg,   csrWdata, csrIsRW, csrIsRS, csrIsRC);
    wire [31:0] mtvalNewCSR    = mkCsrNewVal(mtvalReg,    csrWdata, csrIsRW, csrIsRS, csrIsRC);
    // S-mode CSR new values
    wire [31:0] sieNewCSR      = mkCsrNewVal(sieReg,      csrWdata, csrIsRW, csrIsRS, csrIsRC);
    wire [31:0] stvecNewCSR    = mkCsrNewVal(stvecReg,    csrWdata, csrIsRW, csrIsRS, csrIsRC);
    wire [31:0] sscratchNewCSR = mkCsrNewVal(sscratchReg, csrWdata, csrIsRW, csrIsRS, csrIsRC);
    wire [31:0] sepcNewCSR     = mkCsrNewVal(sepcReg,     csrWdata, csrIsRW, csrIsRS, csrIsRC);
    wire [31:0] scauseNewCSR   = mkCsrNewVal(scauseReg,   csrWdata, csrIsRW, csrIsRS, csrIsRC);
    wire [31:0] stvalNewCSR    = mkCsrNewVal(stvalReg,    csrWdata, csrIsRW, csrIsRS, csrIsRC);
    wire [31:0] satpNewCSR     = mkCsrNewVal(satpReg,     csrWdata, csrIsRW, csrIsRS, csrIsRC);
    // Delegation CSR new values
    wire [31:0] medelegNewCSR  = mkCsrNewVal(medelegReg,  csrWdata, csrIsRW, csrIsRS, csrIsRC);
    wire [31:0] midelegNewCSR  = mkCsrNewVal(midelegReg,  csrWdata, csrIsRW, csrIsRS, csrIsRC);
    // SSTATUS write: merge S-mode bits back into mstatus
    wire [31:0] sstatusNewVal  = mkCsrNewVal(sstatus_view, csrWdata, csrIsRW, csrIsRS, csrIsRC);
    wire [31:0] sstatus_wdata_out = (mstatusReg & ~sstatus_mask) | (sstatusNewVal & sstatus_mask);
    wire sstatusWriteActive = idex_isCsr & (idex_csrAddr == 12'h100);

    // mstatus M-mode trap: MIE→MPIE, clear MIE, MPP←privMode
    wire [31:0] msClearMIE = mstatusReg & 32'hFFFFFFF7;
    wire [31:0] msSetMPIE  = mstatusMIE ?
                              (msClearMIE | 32'h00000080) :
                              (msClearMIE & 32'hFFFFFF7F);
    wire [31:0] msSetMPIE_clearMPP = msSetMPIE & 32'hFFFFE7FF;
    wire [31:0] mstatusTrapMVal = msSetMPIE_clearMPP | ({30'd0, privMode} << 11);

    // mstatus S-mode trap: SIE→SPIE, clear SIE, SPP←privMode[0]
    wire mstatusSIE  = mstatusReg[1];
    wire mstatusSPIE = mstatusReg[5];
    wire [31:0] msClearSIE = mstatusReg & 32'hFFFFFFFD;
    wire [31:0] msSetSPIE  = mstatusSIE ?
                              (msClearSIE | 32'h00000020) :
                              (msClearSIE & 32'hFFFFFFDF);
    wire [31:0] mstatusTrapSVal = privMode[0] ?
                                   (msSetSPIE | 32'h00000100) :
                                   (msSetSPIE & 32'hFFFFFEFF);

    wire [31:0] mstatusTrapVal = trapToS ? mstatusTrapSVal : mstatusTrapMVal;

    // MRET: MIE←MPIE, MPIE←1, MPP←0
    wire [31:0] msClearMPP = mstatusReg & 32'hFFFFE7FF;
    wire [31:0] msRestoreMIE = mstatusMPIE ?
                                (msClearMPP | 32'h00000008) :
                                (msClearMPP & 32'hFFFFFFF7);
    wire [31:0] mstatusMretVal = msRestoreMIE | 32'h00000080;

    // SRET: SIE←SPIE, SPIE←1, SPP←0
    wire [31:0] msClearSPP = mstatusReg & 32'hFFFFFEFF;
    wire [31:0] msRestoreSIE = mstatusSPIE ?
                                (msClearSPP | 32'h00000002) :
                                (msClearSPP & 32'hFFFFFFFD);
    wire [31:0] mstatusSretVal = msRestoreSIE | 32'h00000020;

    // ========================================================================
    // Next-state logic
    // ========================================================================
    wire [31:0] pcPlus4 = pcReg + 32'd4;
    wire [31:0] fetchPCPlus4 = fetchPC + 32'd4;

    always_comb begin
        // PC
        pcReg_next = trap_taken ? trap_target :
                     idex_isMret ? mret_target :
                     idex_isSret ? sret_target :
                     flush ? jumpTarget :
                     stall ? pcReg :
                     pcPlus4;

        fetchPC_next = stall ? fetchPC : pcReg;
        flushDelay_next = flush;

        // IF/ID
        ifid_inst_next = flushOrDelay ? NOP_INST : (stall ? ifid_inst : final_imem_rdata);
        ifid_pc_next   = stall ? ifid_pc : fetchPC;
        ifid_pc4_next  = stall ? ifid_pc4 : fetchPCPlus4;

        // ID/EX (squash on stall or flush)
        idex_aluOp_next    = squash ? 4'd0 : id_aluOp;
        idex_regWrite_next = squash ? 1'b0 : id_regWrite;
        idex_memRead_next  = squash ? 1'b0 : id_memRead;
        idex_memWrite_next = squash ? 1'b0 : id_memWrite;
        idex_memToReg_next = squash ? 1'b0 : id_memToReg;
        idex_branch_next   = squash ? 1'b0 : id_isBranch;
        idex_jump_next     = squash ? 1'b0 : id_jump;
        idex_auipc_next    = squash ? 1'b0 : id_auipc;
        idex_aluSrcB_next  = squash ? 1'b0 : id_aluSrcB;
        idex_isJalr_next   = squash ? 1'b0 : id_isJALR;
        idex_isCsr_next    = squash ? 1'b0 : id_isCsr;
        idex_isEcall_next  = squash ? 1'b0 : id_isEcall;
        idex_isMret_next   = squash ? 1'b0 : id_isMret;

        idex_rs1Val_next    = id_rs1Val;
        idex_rs2Val_next    = id_rs2Val;
        idex_imm_next       = id_imm;
        idex_rd_next        = squash ? 5'd0 : id_rd;
        idex_rs1Idx_next    = id_rs1;
        idex_rs2Idx_next    = id_rs2;
        idex_funct3_next    = id_funct3;
        idex_pc_next        = ifid_pc;
        idex_pc4_next       = ifid_pc4;
        idex_csrAddr_next   = id_csrAddr;
        idex_csrFunct3_next = id_funct3;

        // EX/WB
        exwb_alu_next      = alu_result;
        exwb_rd_next       = idex_rd;
        exwb_regW_next     = idex_regWrite;
        exwb_m2r_next      = idex_memToReg;
        exwb_pc4_next      = idex_pc4;
        exwb_jump_next     = idex_jump;
        exwb_isCsr_next    = idex_isCsr;
        exwb_csrRdata_next = csr_rdata;

        // WB history
        prev_wb_addr_next = wb_addr;
        prev_wb_data_next = wb_data;
        prev_wb_en_next   = wb_en;

        // Store history
        prevStoreAddr_next = alu_result;
        prevStoreData_next = ex_rs2;
        prevStoreEn_next   = idex_memWrite;

        // CLINT
        msipReg_next      = (clintWE & (clintOffset == 16'h0000)) ? ex_rs2_approx : msipReg;
        mtimeLoReg_next   = (clintWE & (clintOffset == 16'hBFF8)) ? ex_rs2_approx : mtimeLoInc;
        mtimeHiReg_next   = (clintWE & (clintOffset == 16'hBFFC)) ? ex_rs2_approx : mtimeHiInc;
        mtimecmpLoReg_next = (clintWE & (clintOffset == 16'h4000)) ? ex_rs2_approx : mtimecmpLoReg;
        mtimecmpHiReg_next = (clintWE & (clintOffset == 16'h4004)) ? ex_rs2_approx : mtimecmpHiReg;

        // CSR (M-mode)
        mstatusReg_next = trap_taken ? mstatusTrapVal :
                           idex_isMret ? mstatusMretVal :
                           idex_isSret ? mstatusSretVal :
                           sstatusWriteActive ? sstatus_wdata_out :
                           (idex_isCsr & (idex_csrAddr == 12'h300)) ? mstatusNewCSR :
                           mstatusReg;
        mieReg_next     = (idex_isCsr & (idex_csrAddr == 12'h304)) ? mieNewCSR : mieReg;
        mtvecReg_next   = (idex_isCsr & (idex_csrAddr == 12'h305)) ? mtvecNewCSR : mtvecReg;
        mscratchReg_next = (idex_isCsr & (idex_csrAddr == 12'h340)) ? mscratchNewCSR : mscratchReg;
        mepcReg_next    = trapToM ? idex_pc :
                           (idex_isCsr & (idex_csrAddr == 12'h341)) ? mepcNewCSR : mepcReg;
        mcauseReg_next  = trapToM ? trapCause :
                           (idex_isCsr & (idex_csrAddr == 12'h342)) ? mcauseNewCSR : mcauseReg;
        mtvalReg_next   = trapToM ? (pageFault ? alu_result_approx : 32'd0) :
                           (idex_isCsr & (idex_csrAddr == 12'h343)) ? mtvalNewCSR : mtvalReg;

        // CSR (S-mode)
        sieReg_next      = (idex_isCsr & (idex_csrAddr == 12'h104)) ? sieNewCSR : sieReg;
        stvecReg_next    = (idex_isCsr & (idex_csrAddr == 12'h105)) ? stvecNewCSR : stvecReg;
        sscratchReg_next = (idex_isCsr & (idex_csrAddr == 12'h140)) ? sscratchNewCSR : sscratchReg;
        sepcReg_next     = trapToS ? idex_pc :
                            (idex_isCsr & (idex_csrAddr == 12'h141)) ? sepcNewCSR : sepcReg;
        scauseReg_next   = trapToS ? trapCause :
                            (idex_isCsr & (idex_csrAddr == 12'h142)) ? scauseNewCSR : scauseReg;
        stvalReg_next    = trapToS ? (pageFault ? alu_result_approx : 32'd0) :
                            (idex_isCsr & (idex_csrAddr == 12'h143)) ? stvalNewCSR : stvalReg;
        satpReg_next     = (idex_isCsr & (idex_csrAddr == 12'h180)) ? satpNewCSR : satpReg;

        // Delegation
        medelegReg_next  = (idex_isCsr & (idex_csrAddr == 12'h302)) ? medelegNewCSR : medelegReg;
        midelegReg_next  = (idex_isCsr & (idex_csrAddr == 12'h303)) ? midelegNewCSR : midelegReg;

        // Privilege mode
        privMode_next = trapToM ? 2'd3 :
                         trapToS ? 2'd1 :
                         idex_isMret ? mpp :
                         idex_isSret ? sretPriv :
                         privMode;

        // AI MMIO
        aiStatusReg_next = (mmioWE & (mmioOffset_ex == 4'h0)) ? ex_rs2_approx : aiStatusReg;
        aiInputReg_next  = (mmioWE & (mmioOffset_ex == 4'h4)) ? ex_rs2_approx : aiInputReg;

        // UART 8250 write logic
        begin
            automatic logic uartWE = idex_memWrite & isUART_ex;
            automatic logic [2:0] uartOff = alu_result_approx[2:0];
            automatic logic uartDLAB = uartLCR[7];
            automatic logic [7:0] uartWdata8 = ex_rs2_approx[7:0];

            uartLCR_next = (uartWE & (uartOff == 3'd3)) ? uartWdata8 : uartLCR;
            uartIER_next = (uartWE & (uartOff == 3'd1) & !uartDLAB) ? uartWdata8 : uartIER;
            uartMCR_next = (uartWE & (uartOff == 3'd4)) ? uartWdata8 : uartMCR;
            uartSCR_next = (uartWE & (uartOff == 3'd7)) ? uartWdata8 : uartSCR;
            uartDLL_next = (uartWE & (uartOff == 3'd0) & uartDLAB) ? uartWdata8 : uartDLL;
            uartDLM_next = (uartWE & (uartOff == 3'd1) & uartDLAB) ? uartWdata8 : uartDLM;

            // RX logic: uart_rx_valid sets buffer, RBR read clears ready
            if (uart_rx_valid) begin
                uartRxBuf_next = uart_rx_data;
                uartRxReady_next = 1'b1;
            end else if (exwb_m2r & isUART_wb & (uartOffset_wb == 3'd0) & !uartDLAB_wb) begin
                // RBR read clears RX ready
                uartRxBuf_next = uartRxBuf;
                uartRxReady_next = 1'b0;
            end else begin
                uartRxBuf_next = uartRxBuf;
                uartRxReady_next = uartRxReady;
            end
        end

        // Sub-word
        exwb_funct3_next = idex_funct3;

        // M-extension
        idex_isMext_next = squash ? 1'b0 : id_isMext;

        // A-extension: ID/EX pipeline
        idex_isAMO_next = squash ? 1'b0 : id_isAMO;
        idex_amoOp_next = squash ? 5'd0 : id_amoOp;

        // A-extension: EX/WB pipeline
        exwb_isAMO_next = idex_isAMO;
        exwb_amoOp_next = idex_amoOp;

        // Reservation registers (LR sets, SC clears, store to same addr clears)
        if (exwb_isLR) begin
            reservationValid_next = 1'b1;
            reservationAddr_next  = exwb_alu;
        end else if (exwb_isSC) begin
            reservationValid_next = 1'b0;
            reservationAddr_next  = reservationAddr;
        end else if (prevStoreEn & (prevStoreAddr == reservationAddr)) begin
            reservationValid_next = 1'b0;
            reservationAddr_next  = reservationAddr;
        end else begin
            reservationValid_next = reservationValid;
            reservationAddr_next  = reservationAddr;
        end

        // Pending write: AMO read-modify-write delayed by 1 cycle
        // exwb_isAMO && !exwb_isLR && !exwb_isSC triggers pending write
        if (exwb_isAMO & !exwb_isLR & !exwb_isSC) begin
            pendingWriteEn_next   = 1'b1;
            pendingWriteAddr_next = exwb_alu;
            pendingWriteData_next = amo_new_val;
        end else begin
            pendingWriteEn_next   = 1'b0;
            pendingWriteAddr_next = pendingWriteAddr;
            pendingWriteData_next = pendingWriteData;
        end

        // SRET and SFENCE.VMA pipeline (107-108)
        idex_isSret_next = squash ? 1'b0 : id_isSret;
        idex_isSFenceVMA_next = squash ? 1'b0 : id_isSFenceVMA;

        // MMU TLB + PTW (D-side only)
        ptwVaddr_next = (ptwIsIdle & ptwReq) ? alu_result_approx : ptwVaddr;
        ptwPte_next = isDataReady ? dmem_rdata : ptwPte;

        // PTW state transitions (7-state FSM)
        ptwState_next = ptwIsIdle   ? (ptwReq ? 3'd1 : 3'd0) :
                        ptwIsL1Req  ? 3'd2 :
                        ptwIsL1Wait ? nextFromL1Wait :
                        ptwIsL0Req  ? 3'd4 :
                        ptwIsL0Wait ? nextFromL0Wait :
                        3'd0;  // DONE/FAULT → IDLE

        // Megapage tracking: leaf found at L1 level
        ptwMega_next = (ptwIsL1Wait & dmemPteIsLeaf & !dmemPteInvalid) ? 1'b1 :
                        ptwIsIdle ? 1'b0 : ptwMega;

        // Replacement pointer: increment on fill
        replPtr_next = tlbFill ? (replPtr + 2'd1) : replPtr;

        // TLB entry next-state (SFENCE.VMA clears, fill updates)
        tlb0Valid_next = idex_isSFenceVMA ? 1'b0 : (doFill0 ? 1'b1 : tlb0Valid);
        tlb0VPN_next   = doFill0 ? fillVPN   : tlb0VPN;
        tlb0PPN_next   = doFill0 ? fillPPN   : tlb0PPN;
        tlb0Flags_next = doFill0 ? fillFlags  : tlb0Flags;
        tlb0Mega_next  = doFill0 ? ptwMega    : tlb0Mega;
        tlb1Valid_next = idex_isSFenceVMA ? 1'b0 : (doFill1 ? 1'b1 : tlb1Valid);
        tlb1VPN_next   = doFill1 ? fillVPN   : tlb1VPN;
        tlb1PPN_next   = doFill1 ? fillPPN   : tlb1PPN;
        tlb1Flags_next = doFill1 ? fillFlags  : tlb1Flags;
        tlb1Mega_next  = doFill1 ? ptwMega    : tlb1Mega;
        tlb2Valid_next = idex_isSFenceVMA ? 1'b0 : (doFill2 ? 1'b1 : tlb2Valid);
        tlb2VPN_next   = doFill2 ? fillVPN   : tlb2VPN;
        tlb2PPN_next   = doFill2 ? fillPPN   : tlb2PPN;
        tlb2Flags_next = doFill2 ? fillFlags  : tlb2Flags;
        tlb2Mega_next  = doFill2 ? ptwMega    : tlb2Mega;
        tlb3Valid_next = idex_isSFenceVMA ? 1'b0 : (doFill3 ? 1'b1 : tlb3Valid);
        tlb3VPN_next   = doFill3 ? fillVPN   : tlb3VPN;
        tlb3PPN_next   = doFill3 ? fillPPN   : tlb3PPN;
        tlb3Flags_next = doFill3 ? fillFlags  : tlb3Flags;
        tlb3Mega_next  = doFill3 ? ptwMega    : tlb3Mega;

        // MMU state transitions
        mmuState_next = isMMUIdle   ? (needTranslateD ? 3'd1 : 3'd0) :
                        isTLBLookup ? (anyTLBHit ? 3'd3 : 3'd2) :
                        isPTWWalk   ? (ptwIsDone ? 3'd3 : (ptwIsFault ? 3'd4 : 3'd2)) :
                        3'd0;  // DONE/FAULT → IDLE

        ptwIsIfetch_next = ptwIsIfetch;
        ifetchFaultPending_next = ifetchFaultPending;
    end

    // ========================================================================
    // UART output detection (store to 0x10000000)
    // ========================================================================
    // Detect store in WB stage (prevStoreEn is the registered memWrite)
    // UART address: 0x10xxxxxx (bit 28 = 1)
    assign uart_tx_valid = prevStoreEn & (prevStoreAddr[31:24] == 8'h10);
    assign uart_tx_data  = prevStoreData;

    // ========================================================================
    // Sequential logic
    // ========================================================================
    always_ff @(posedge clk) begin
        if (rst) begin
            pcReg          <= 32'd0;
            fetchPC        <= 32'd0;
            flushDelay     <= 1'b0;
            ifid_inst      <= NOP_INST;
            ifid_pc        <= 32'd0;
            ifid_pc4       <= 32'd0;
            idex_aluOp     <= 4'd0;
            idex_regWrite  <= 1'b0;
            idex_memRead   <= 1'b0;
            idex_memWrite  <= 1'b0;
            idex_memToReg  <= 1'b0;
            idex_branch    <= 1'b0;
            idex_jump      <= 1'b0;
            idex_auipc     <= 1'b0;
            idex_aluSrcB   <= 1'b0;
            idex_isJalr    <= 1'b0;
            idex_isCsr     <= 1'b0;
            idex_isEcall   <= 1'b0;
            idex_isMret    <= 1'b0;
            idex_rs1Val    <= 32'd0;
            idex_rs2Val    <= 32'd0;
            idex_imm       <= 32'd0;
            idex_rd        <= 5'd0;
            idex_rs1Idx    <= 5'd0;
            idex_rs2Idx    <= 5'd0;
            idex_funct3    <= 3'd0;
            idex_pc        <= 32'd0;
            idex_pc4       <= 32'd0;
            idex_csrAddr   <= 12'd0;
            idex_csrFunct3 <= 3'd0;
            exwb_alu       <= 32'd0;
            exwb_rd        <= 5'd0;
            exwb_regW      <= 1'b0;
            exwb_m2r       <= 1'b0;
            exwb_pc4       <= 32'd0;
            exwb_jump      <= 1'b0;
            exwb_isCsr     <= 1'b0;
            exwb_csrRdata  <= 32'd0;
            prev_wb_addr   <= 5'd0;
            prev_wb_data   <= 32'd0;
            prev_wb_en     <= 1'b0;
            prevStoreAddr  <= 32'd0;
            prevStoreData  <= 32'd0;
            prevStoreEn    <= 1'b0;
            msipReg        <= 32'd0;
            mtimeLoReg     <= 32'd0;
            mtimeHiReg     <= 32'd0;
            mtimecmpLoReg  <= 32'hFFFFFFFF;
            mtimecmpHiReg  <= 32'hFFFFFFFF;
            mstatusReg     <= 32'd0;
            mieReg         <= 32'd0;
            mtvecReg       <= 32'd0;
            mscratchReg    <= 32'd0;
            mepcReg        <= 32'd0;
            mcauseReg      <= 32'd0;
            mtvalReg       <= 32'd0;
            aiStatusReg    <= 32'd0;
            aiInputReg     <= 32'd0;
            exwb_funct3    <= 3'd0;
            idex_isMext    <= 1'b0;
            // A-extension
            reservationValid <= 1'b0;
            reservationAddr  <= 32'd0;
            idex_isAMO       <= 1'b0;
            idex_amoOp       <= 5'd0;
            exwb_isAMO       <= 1'b0;
            exwb_amoOp       <= 5'd0;
            pendingWriteEn   <= 1'b0;
            pendingWriteAddr <= 32'd0;
            pendingWriteData <= 32'd0;
            // S-mode CSRs + privilege
            privMode         <= 2'd3;  // M-mode
            sieReg           <= 32'd0;
            stvecReg         <= 32'd0;
            sscratchReg      <= 32'd0;
            sepcReg          <= 32'd0;
            scauseReg        <= 32'd0;
            stvalReg         <= 32'd0;
            satpReg          <= 32'd0;
            medelegReg       <= 32'd0;
            midelegReg       <= 32'd0;
            // MMU TLB + PTW
            mmuState         <= 3'd0;
            ptwState         <= 3'd0;
            ptwVaddr         <= 32'd0;
            ptwPte           <= 32'd0;
            ptwMega          <= 1'b0;
            replPtr          <= 2'd0;
            tlb0Valid <= 1'b0; tlb0VPN <= 20'd0; tlb0PPN <= 22'd0; tlb0Flags <= 8'd0; tlb0Mega <= 1'b0;
            tlb1Valid <= 1'b0; tlb1VPN <= 20'd0; tlb1PPN <= 22'd0; tlb1Flags <= 8'd0; tlb1Mega <= 1'b0;
            tlb2Valid <= 1'b0; tlb2VPN <= 20'd0; tlb2PPN <= 22'd0; tlb2Flags <= 8'd0; tlb2Mega <= 1'b0;
            tlb3Valid <= 1'b0; tlb3VPN <= 20'd0; tlb3PPN <= 22'd0; tlb3Flags <= 8'd0; tlb3Mega <= 1'b0;
            ptwIsIfetch      <= 1'b0;
            ifetchFaultPending <= 1'b0;
            // Pipeline additions
            idex_isSret      <= 1'b0;
            idex_isSFenceVMA <= 1'b0;
            // UART 8250
            uartLCR          <= 8'd0;
            uartIER          <= 8'd0;
            uartMCR          <= 8'd0;
            uartSCR          <= 8'd0;
            uartDLL          <= 8'd0;
            uartDLM          <= 8'd0;
            uartRxBuf        <= 8'd0;
            uartRxReady      <= 1'b0;
        end else begin
            pcReg          <= pcReg_next;
            fetchPC        <= fetchPC_next;
            flushDelay     <= flushDelay_next;
            ifid_inst      <= ifid_inst_next;
            ifid_pc        <= ifid_pc_next;
            ifid_pc4       <= ifid_pc4_next;
            idex_aluOp     <= idex_aluOp_next;
            idex_regWrite  <= idex_regWrite_next;
            idex_memRead   <= idex_memRead_next;
            idex_memWrite  <= idex_memWrite_next;
            idex_memToReg  <= idex_memToReg_next;
            idex_branch    <= idex_branch_next;
            idex_jump      <= idex_jump_next;
            idex_auipc     <= idex_auipc_next;
            idex_aluSrcB   <= idex_aluSrcB_next;
            idex_isJalr    <= idex_isJalr_next;
            idex_isCsr     <= idex_isCsr_next;
            idex_isEcall   <= idex_isEcall_next;
            idex_isMret    <= idex_isMret_next;
            idex_rs1Val    <= idex_rs1Val_next;
            idex_rs2Val    <= idex_rs2Val_next;
            idex_imm       <= idex_imm_next;
            idex_rd        <= idex_rd_next;
            idex_rs1Idx    <= idex_rs1Idx_next;
            idex_rs2Idx    <= idex_rs2Idx_next;
            idex_funct3    <= idex_funct3_next;
            idex_pc        <= idex_pc_next;
            idex_pc4       <= idex_pc4_next;
            idex_csrAddr   <= idex_csrAddr_next;
            idex_csrFunct3 <= idex_csrFunct3_next;
            exwb_alu       <= exwb_alu_next;
            exwb_rd        <= exwb_rd_next;
            exwb_regW      <= exwb_regW_next;
            exwb_m2r       <= exwb_m2r_next;
            exwb_pc4       <= exwb_pc4_next;
            exwb_jump      <= exwb_jump_next;
            exwb_isCsr     <= exwb_isCsr_next;
            exwb_csrRdata  <= exwb_csrRdata_next;
            prev_wb_addr   <= prev_wb_addr_next;
            prev_wb_data   <= prev_wb_data_next;
            prev_wb_en     <= prev_wb_en_next;
            prevStoreAddr  <= prevStoreAddr_next;
            prevStoreData  <= prevStoreData_next;
            prevStoreEn    <= prevStoreEn_next;
            msipReg        <= msipReg_next;
            mtimeLoReg     <= mtimeLoReg_next;
            mtimeHiReg     <= mtimeHiReg_next;
            mtimecmpLoReg  <= mtimecmpLoReg_next;
            mtimecmpHiReg  <= mtimecmpHiReg_next;
            mstatusReg     <= mstatusReg_next;
            mieReg         <= mieReg_next;
            mtvecReg       <= mtvecReg_next;
            mscratchReg    <= mscratchReg_next;
            mepcReg        <= mepcReg_next;
            mcauseReg      <= mcauseReg_next;
            mtvalReg       <= mtvalReg_next;
            aiStatusReg    <= aiStatusReg_next;
            aiInputReg     <= aiInputReg_next;
            exwb_funct3    <= exwb_funct3_next;
            idex_isMext    <= idex_isMext_next;
            // A-extension
            reservationValid <= reservationValid_next;
            reservationAddr  <= reservationAddr_next;
            idex_isAMO       <= idex_isAMO_next;
            idex_amoOp       <= idex_amoOp_next;
            exwb_isAMO       <= exwb_isAMO_next;
            exwb_amoOp       <= exwb_amoOp_next;
            pendingWriteEn   <= pendingWriteEn_next;
            pendingWriteAddr <= pendingWriteAddr_next;
            pendingWriteData <= pendingWriteData_next;
            // S-mode CSRs + privilege
            privMode         <= privMode_next;
            sieReg           <= sieReg_next;
            stvecReg         <= stvecReg_next;
            sscratchReg      <= sscratchReg_next;
            sepcReg          <= sepcReg_next;
            scauseReg        <= scauseReg_next;
            stvalReg         <= stvalReg_next;
            satpReg          <= satpReg_next;
            medelegReg       <= medelegReg_next;
            midelegReg       <= midelegReg_next;
            // MMU TLB + PTW
            mmuState         <= mmuState_next;
            ptwState         <= ptwState_next;
            ptwVaddr         <= ptwVaddr_next;
            ptwPte           <= ptwPte_next;
            ptwMega          <= ptwMega_next;
            replPtr          <= replPtr_next;
            tlb0Valid <= tlb0Valid_next; tlb0VPN <= tlb0VPN_next; tlb0PPN <= tlb0PPN_next;
            tlb0Flags <= tlb0Flags_next; tlb0Mega <= tlb0Mega_next;
            tlb1Valid <= tlb1Valid_next; tlb1VPN <= tlb1VPN_next; tlb1PPN <= tlb1PPN_next;
            tlb1Flags <= tlb1Flags_next; tlb1Mega <= tlb1Mega_next;
            tlb2Valid <= tlb2Valid_next; tlb2VPN <= tlb2VPN_next; tlb2PPN <= tlb2PPN_next;
            tlb2Flags <= tlb2Flags_next; tlb2Mega <= tlb2Mega_next;
            tlb3Valid <= tlb3Valid_next; tlb3VPN <= tlb3VPN_next; tlb3PPN <= tlb3PPN_next;
            tlb3Flags <= tlb3Flags_next; tlb3Mega <= tlb3Mega_next;
            ptwIsIfetch      <= ptwIsIfetch_next;
            ifetchFaultPending <= ifetchFaultPending_next;
            // Pipeline additions
            idex_isSret      <= idex_isSret_next;
            idex_isSFenceVMA <= idex_isSFenceVMA_next;
            // UART 8250
            uartLCR          <= uartLCR_next;
            uartIER          <= uartIER_next;
            uartMCR          <= uartMCR_next;
            uartSCR          <= uartSCR_next;
            uartDLL          <= uartDLL_next;
            uartDLM          <= uartDLM_next;
            uartRxBuf        <= uartRxBuf_next;
            uartRxReady      <= uartRxReady_next;
        end
    end

    // ========================================================================
    // IMEM write (for firmware loading)
    // ========================================================================
    always_ff @(posedge clk) begin
        if (imem_wr_en) begin
            imem[imem_wr_addr] <= imem_wr_data;
        end
    end

    // ========================================================================
    // DMEM: 4 byte-wide synchronous memories
    // ========================================================================
    always_ff @(posedge clk) begin
        if (byte0_we) dmem_b0[dmem_addr] <= byte0_wdata;
        dmem_b0_rdata <= dmem_b0[dmem_addr];

        if (byte1_we) dmem_b1[dmem_addr] <= byte1_wdata;
        dmem_b1_rdata <= dmem_b1[dmem_addr];

        if (byte2_we) dmem_b2[dmem_addr] <= byte2_wdata;
        dmem_b2_rdata <= dmem_b2[dmem_addr];

        if (byte3_we) dmem_b3[dmem_addr] <= byte3_wdata;
        dmem_b3_rdata <= dmem_b3[dmem_addr];
    end

    // ========================================================================
    // Register file write
    // ========================================================================
    always_ff @(posedge clk) begin
        if (wb_en) begin
            regfile[wb_addr] <= wb_data;
        end
    end

    // Output PC
    assign pc_out = pcReg;

endmodule

// ============================================================================
// ALU module
// ============================================================================
module alu_compute (
    input  logic [3:0]  op,
    input  logic [31:0] a, b,
    output logic [31:0] result
);
    always_comb begin
        case (op)
            4'd0:  result = a + b;                                    // ADD
            4'd1:  result = a - b;                                    // SUB
            4'd2:  result = a & b;                                    // AND
            4'd3:  result = a | b;                                    // OR
            4'd4:  result = a ^ b;                                    // XOR
            4'd5:  result = a << b[4:0];                              // SLL
            4'd6:  result = a >> b[4:0];                              // SRL
            4'd7:  result = $signed(a) >>> b[4:0];                    // SRA
            4'd8:  result = ($signed(a) < $signed(b)) ? 32'd1 : 32'd0; // SLT
            4'd9:  result = (a < b) ? 32'd1 : 32'd0;                 // SLTU
            default: result = b;                                       // PASS (LUI)
        endcase
    end
endmodule

// ============================================================================
// Branch comparator
// ============================================================================
module branch_comp (
    input  logic [2:0]  funct3,
    input  logic [31:0] a, b,
    output logic        taken
);
    always_comb begin
        case (funct3)
            3'd0: taken = (a == b);                                    // BEQ
            3'd1: taken = (a != b);                                    // BNE
            3'd4: taken = ($signed(a) < $signed(b));                   // BLT
            3'd5: taken = ($signed(a) >= $signed(b));                  // BGE
            3'd6: taken = (a < b);                                     // BLTU
            3'd7: taken = (a >= b);                                    // BGEU
            default: taken = 1'b0;
        endcase
    end
endmodule

// ============================================================================
// Immediate generator
// ============================================================================
module imm_gen (
    input  logic [31:0] inst,
    input  logic [6:0]  opcode,
    output logic [31:0] imm
);
    // I-type
    wire [31:0] immI = {{20{inst[31]}}, inst[31:20]};
    // S-type
    wire [31:0] immS = {{20{inst[31]}}, inst[31:25], inst[11:7]};
    // B-type
    wire [31:0] immB = {{19{inst[31]}}, inst[31], inst[7], inst[30:25], inst[11:8], 1'b0};
    // U-type
    wire [31:0] immU = {inst[31:12], 12'd0};
    // J-type
    wire [31:0] immJ = {{11{inst[31]}}, inst[31], inst[19:12], inst[20], inst[30:21], 1'b0};

    always_comb begin
        case (opcode)
            7'b1101111: imm = immJ;  // JAL
            7'b0110111: imm = immU;  // LUI
            7'b0010111: imm = immU;  // AUIPC
            7'b1100011: imm = immB;  // Branch
            7'b0100011: imm = immS;  // Store
            default:    imm = immI;  // I-type (LOAD, ALUI, JALR, SYSTEM)
        endcase
    end
endmodule

// ============================================================================
// ALU control decoder
// ============================================================================
module alu_control (
    input  logic [6:0] opcode,
    input  logic [2:0] funct3,
    input  logic [6:0] funct7,
    output logic [3:0] alu_op
);
    wire isALUrr  = (opcode == 7'b0110011);
    wire isALUimm = (opcode == 7'b0010011);
    wire isALUany = isALUrr | isALUimm;
    wire isLUI    = (opcode == 7'b0110111);
    wire isBranch = (opcode == 7'b1100011);
    wire f7bit5   = funct7[5];

    always_comb begin
        if (isALUany) begin
            case (funct3)
                3'd0: alu_op = (isALUrr & f7bit5) ? 4'd1 : 4'd0; // ADD/SUB
                3'd1: alu_op = 4'd5;   // SLL
                3'd2: alu_op = 4'd8;   // SLT
                3'd3: alu_op = 4'd9;   // SLTU
                3'd4: alu_op = 4'd4;   // XOR
                3'd5: alu_op = (isALUany & f7bit5) ? 4'd7 : 4'd6; // SRL/SRA
                3'd6: alu_op = 4'd3;   // OR
                3'd7: alu_op = 4'd2;   // AND
            endcase
        end else if (isLUI) begin
            alu_op = 4'hA;  // PASS
        end else if (isBranch) begin
            alu_op = 4'd1;  // SUB
        end else begin
            alu_op = 4'd0;  // ADD (LOAD, STORE, AUIPC, JAL, JALR)
        end
    end
endmodule

// ============================================================================
// M-extension compute (MUL/DIV/REM)
// ============================================================================
module mext_compute (
    input  logic [2:0]  funct3,
    input  logic [31:0] rs1, rs2,
    output logic [31:0] result
);
    // Signed interpretations
    wire signed [31:0] srs1 = $signed(rs1);
    wire signed [31:0] srs2 = $signed(rs2);

    // 64-bit products
    wire signed [63:0] prod_ss = $signed({{32{rs1[31]}}, rs1}) * $signed({{32{rs2[31]}}, rs2});
    wire signed [63:0] prod_su = $signed({{32{rs1[31]}}, rs1}) * $signed({1'b0, rs2});
    wire        [63:0] prod_uu = {32'd0, rs1} * {32'd0, rs2};

    always_comb begin
        case (funct3)
            3'd0: result = prod_ss[31:0];                     // MUL
            3'd1: result = prod_ss[63:32];                    // MULH
            3'd2: result = prod_su[63:32];                    // MULHSU
            3'd3: result = prod_uu[63:32];                    // MULHU
            3'd4: begin                                        // DIV
                if (rs2 == 32'd0)
                    result = 32'hFFFFFFFF;
                else if (rs1 == 32'h80000000 && rs2 == 32'hFFFFFFFF)
                    result = 32'h80000000;
                else
                    result = $unsigned(srs1 / srs2);
            end
            3'd5: begin                                        // DIVU
                if (rs2 == 32'd0)
                    result = 32'hFFFFFFFF;
                else
                    result = rs1 / rs2;
            end
            3'd6: begin                                        // REM
                if (rs2 == 32'd0)
                    result = rs1;
                else if (rs1 == 32'h80000000 && rs2 == 32'hFFFFFFFF)
                    result = 32'd0;
                else
                    result = $unsigned(srs1 % srs2);
            end
            3'd7: begin                                        // REMU
                if (rs2 == 32'd0)
                    result = rs1;
                else
                    result = rs1 % rs2;
            end
        endcase
    end
endmodule

// ============================================================================
// A-extension AMO compute
// ============================================================================
module amo_compute (
    input  logic [4:0]  amoOp,
    input  logic [31:0] memVal, rs2Val,
    output logic [31:0] result
);
    wire signed [31:0] smemVal = $signed(memVal);
    wire signed [31:0] srs2Val = $signed(rs2Val);

    always_comb begin
        case (amoOp)
            5'b00001: result = rs2Val;                                      // AMOSWAP
            5'b00000: result = memVal + rs2Val;                             // AMOADD
            5'b00100: result = memVal ^ rs2Val;                             // AMOXOR
            5'b01100: result = memVal & rs2Val;                             // AMOAND
            5'b01000: result = memVal | rs2Val;                             // AMOOR
            5'b10000: result = (smemVal <= srs2Val) ? memVal : rs2Val;      // AMOMIN
            5'b10100: result = (smemVal >= srs2Val) ? memVal : rs2Val;      // AMOMAX
            5'b11000: result = (memVal <= rs2Val)   ? memVal : rs2Val;      // AMOMINU
            5'b11100: result = (memVal >= rs2Val)   ? memVal : rs2Val;      // AMOMAXU
            default:  result = memVal;
        endcase
    end
endmodule
