/-
  RV32I Combinational Components — Signal DSL

  Signal DSL versions of the RV32I combinational components:
  - ALU (32-bit, 11 operations)
  - Branch comparator (6 branch types)
  - Hazard detection unit (load-use stall)
  - Decoder (field extraction, immediate generation, ALU control, control signals)

  These are standalone Signal functions that will be composed into
  the full pipeline in Step 3.
-/

import Sparkle
import Sparkle.Compiler.Elab
import Examples.RV32.Types

set_option maxRecDepth 4096

namespace Sparkle.Examples.RV32.Signal

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Examples.RV32

-- ============================================================================
-- ALU (Combinational)
-- ============================================================================

/-- 32-bit ALU using Signal DSL.
    Inputs:  op[3:0], a[31:0], b[31:0]
    Output:  result[31:0]

    op encoding (from ALUOp.toBitVec4):
      0=ADD, 1=SUB, 2=AND, 3=OR, 4=XOR,
      5=SLL, 6=SRL, 7=SRA, 8=SLT, 9=SLTU, A=PASS -/
def aluSignal {dom : DomainConfig}
    (op : Signal dom (BitVec 4))
    (a b : Signal dom (BitVec 32))
    : Signal dom (BitVec 32) :=
  -- Compute all possible ALU results
  let addR := (· + ·) <$> a <*> b
  let subR := (· - ·) <$> a <*> b
  let andR := (· &&& ·) <$> a <*> b
  let orR  := (· ||| ·) <$> a <*> b
  let xorR := (· ^^^ ·) <$> a <*> b
  let sllR := (· <<< ·) <$> a <*> b
  let srlR := (· >>> ·) <$> a <*> b
  let sraR := (ashr · ·) <$> a <*> b
  -- SLT/SLTU: compare and produce 0 or 1
  let sltCond  := (BitVec.slt · ·) <$> a <*> b
  let sltR     := Signal.mux sltCond (Signal.pure 1#32) (Signal.pure 0#32)
  let sltuCond := (BitVec.ult · ·) <$> a <*> b
  let sltuR    := Signal.mux sltuCond (Signal.pure 1#32) (Signal.pure 0#32)
  -- Mux tree: select result based on op code
  let isOp0 := (· == ·) <$> op <*> Signal.pure 0#4   -- ADD
  let isOp1 := (· == ·) <$> op <*> Signal.pure 1#4   -- SUB
  let isOp2 := (· == ·) <$> op <*> Signal.pure 2#4   -- AND
  let isOp3 := (· == ·) <$> op <*> Signal.pure 3#4   -- OR
  let isOp4 := (· == ·) <$> op <*> Signal.pure 4#4   -- XOR
  let isOp5 := (· == ·) <$> op <*> Signal.pure 5#4   -- SLL
  let isOp6 := (· == ·) <$> op <*> Signal.pure 6#4   -- SRL
  let isOp7 := (· == ·) <$> op <*> Signal.pure 7#4   -- SRA
  let isOp8 := (· == ·) <$> op <*> Signal.pure 8#4   -- SLT
  let isOp9 := (· == ·) <$> op <*> Signal.pure 9#4   -- SLTU
  -- Default: PASS (op=0xA) — pass through B operand
  Signal.mux isOp9 sltuR
    (Signal.mux isOp8 sltR
    (Signal.mux isOp7 sraR
    (Signal.mux isOp6 srlR
    (Signal.mux isOp5 sllR
    (Signal.mux isOp4 xorR
    (Signal.mux isOp3 orR
    (Signal.mux isOp2 andR
    (Signal.mux isOp1 subR
    (Signal.mux isOp0 addR
      b)))))))))

#synthesizeVerilog aluSignal

-- ============================================================================
-- Branch Comparator (Combinational)
-- ============================================================================

/-- Branch comparator: evaluates branch condition based on funct3.
    Inputs:  funct3[2:0], a[31:0], b[31:0]
    Output:  taken (1-bit Bool)

    funct3 encoding:
      0=BEQ, 1=BNE, 4=BLT, 5=BGE, 6=BLTU, 7=BGEU -/
def branchCompSignal {dom : DomainConfig}
    (funct3 : Signal dom (BitVec 3))
    (a b : Signal dom (BitVec 32))
    : Signal dom Bool :=
  -- Compute all comparison results
  let beq  := (· == ·) <$> a <*> b
  let bne  := (fun eq => !eq) <$> beq
  let blt  := (BitVec.slt · ·) <$> a <*> b
  let bge  := (fun lt => !lt) <$> blt
  let bltu := (BitVec.ult · ·) <$> a <*> b
  let bgeu := (fun lt => !lt) <$> bltu
  -- Mux tree: select condition based on funct3
  let f3is0 := (· == ·) <$> funct3 <*> Signal.pure 0#3  -- BEQ
  let f3is1 := (· == ·) <$> funct3 <*> Signal.pure 1#3  -- BNE
  let f3is4 := (· == ·) <$> funct3 <*> Signal.pure 4#3  -- BLT
  let f3is5 := (· == ·) <$> funct3 <*> Signal.pure 5#3  -- BGE
  let f3is6 := (· == ·) <$> funct3 <*> Signal.pure 6#3  -- BLTU
  let f3is7 := (· == ·) <$> funct3 <*> Signal.pure 7#3  -- BGEU
  Signal.mux f3is7 bgeu
    (Signal.mux f3is6 bltu
    (Signal.mux f3is5 bge
    (Signal.mux f3is4 blt
    (Signal.mux f3is1 bne
    (Signal.mux f3is0 beq
      (Signal.pure false))))))

#synthesizeVerilog branchCompSignal

-- ============================================================================
-- Hazard Detection Unit (Combinational)
-- ============================================================================

/-- Load-use hazard detection.
    Inputs:  ex_mem_read (1-bit), ex_rd[4:0], id_rs1[4:0], id_rs2[4:0]
    Output:  stall (1-bit Bool)

    Stall when EX stage has a load and its rd matches ID stage rs1 or rs2. -/
def hazardSignal {dom : DomainConfig}
    (exMemRead : Signal dom Bool)
    (exRd : Signal dom (BitVec 5))
    (idRs1 idRs2 : Signal dom (BitVec 5))
    : Signal dom Bool :=
  let rdIsZero  := (· == ·) <$> exRd <*> Signal.pure 0#5
  let rdNonZero := (fun x => !x) <$> rdIsZero
  let rs1Match  := (· == ·) <$> exRd <*> idRs1
  let rs2Match  := (· == ·) <$> exRd <*> idRs2
  let anyMatch  := (· || ·) <$> rs1Match <*> rs2Match
  let hazard    := (· && ·) <$> rdNonZero <*> anyMatch
  (· && ·) <$> exMemRead <*> hazard

#synthesizeVerilog hazardSignal

-- ============================================================================
-- Decoder: Field Extraction (Combinational)
-- ============================================================================

/-- Extract instruction fields: opcode, rd, funct3, rs1, rs2, funct7.
    Input:   inst[31:0]
    Output:  (opcode[6:0] × rd[4:0] × funct3[2:0] × rs1[4:0] × rs2[4:0] × funct7[6:0])
    Returned as nested pairs: ((opcode × rd) × (funct3 × rs1) × (rs2 × funct7)) -/
def decoderFieldsSignal {dom : DomainConfig}
    (inst : Signal dom (BitVec 32))
    : Signal dom ((BitVec 7 × BitVec 5) × ((BitVec 3 × BitVec 5) × (BitVec 5 × BitVec 7))) :=
  let opcode := inst.map (BitVec.extractLsb' 0 7 ·)    -- inst[6:0]
  let rd     := inst.map (BitVec.extractLsb' 7 5 ·)    -- inst[11:7]
  let funct3 := inst.map (BitVec.extractLsb' 12 3 ·)   -- inst[14:12]
  let rs1    := inst.map (BitVec.extractLsb' 15 5 ·)   -- inst[19:15]
  let rs2    := inst.map (BitVec.extractLsb' 20 5 ·)   -- inst[24:20]
  let funct7 := inst.map (BitVec.extractLsb' 25 7 ·)   -- inst[31:25]
  let pair1  := bundle2 opcode rd
  let pair2  := bundle2 funct3 rs1
  let pair3  := bundle2 rs2 funct7
  let inner  := bundle2 pair2 pair3
  bundle2 pair1 inner

#synthesizeVerilog decoderFieldsSignal

-- ============================================================================
-- Decoder: Immediate Generation (Combinational)
-- ============================================================================

/-- Generate sign-extended immediate value based on opcode.
    Inputs:  inst[31:0], opcode[6:0]
    Output:  imm[31:0]

    Mux cascade: JAL > U-type > Branch > Store > I-type (default) -/
def immGenSignal {dom : DomainConfig}
    (inst : Signal dom (BitVec 32))
    (opcode : Signal dom (BitVec 7))
    : Signal dom (BitVec 32) :=
  -- Sign bit for sign extension
  let inst31 := inst.map (BitVec.extractLsb' 31 1 ·)

  -- I-type: {sign_ext[31:20], inst[31:20]}
  let immI_hi := Signal.mux
    ((· == ·) <$> inst31 <*> Signal.pure 1#1)
    (Signal.pure 0xFFFFF#20) (Signal.pure 0#20)
  let immI_lo := inst.map (BitVec.extractLsb' 20 12 ·)
  let immI := (· ++ ·) <$> immI_hi <*> immI_lo

  -- S-type: {sign_ext, inst[31:25], inst[11:7]}
  let immS_hi := Signal.mux
    ((· == ·) <$> inst31 <*> Signal.pure 1#1)
    (Signal.pure 0xFFFFF#20) (Signal.pure 0#20)
  let immS_mid := inst.map (BitVec.extractLsb' 25 7 ·)
  let immS_lo  := inst.map (BitVec.extractLsb' 7 5 ·)
  let immS_a := (· ++ ·) <$> immS_hi <*> immS_mid
  let immS := (· ++ ·) <$> immS_a <*> immS_lo

  -- B-type: {sign_ext[31:13], inst[31], inst[7], inst[30:25], inst[11:8], 0}
  let immB_hi := Signal.mux
    ((· == ·) <$> inst31 <*> Signal.pure 1#1)
    (Signal.pure 0x7FFFF#19) (Signal.pure 0#19)
  let immB_b31 := inst.map (BitVec.extractLsb' 31 1 ·)
  let immB_b7  := inst.map (BitVec.extractLsb' 7 1 ·)
  let immB_mid := inst.map (BitVec.extractLsb' 25 6 ·)
  let immB_lo  := inst.map (BitVec.extractLsb' 8 4 ·)
  let immB_a := (· ++ ·) <$> immB_hi <*> immB_b31
  let immB_b := (· ++ ·) <$> immB_b7 <*> immB_mid
  let immB_c := (· ++ ·) <$> immB_lo <*> Signal.pure 0#1
  let immB_ab := (· ++ ·) <$> immB_a <*> immB_b
  let immB := (· ++ ·) <$> immB_ab <*> immB_c

  -- U-type: {inst[31:12], 12'b0}
  let immU_hi := inst.map (BitVec.extractLsb' 12 20 ·)
  let immU := (· ++ ·) <$> immU_hi <*> Signal.pure 0#12

  -- J-type: {sign_ext[31:21], inst[31], inst[19:12], inst[20], inst[30:21], 0}
  let immJ_hi  := Signal.mux
    ((· == ·) <$> inst31 <*> Signal.pure 1#1)
    (Signal.pure 0x7FF#11) (Signal.pure 0#11)
  let immJ_b31   := inst.map (BitVec.extractLsb' 31 1 ·)
  let immJ_19_12 := inst.map (BitVec.extractLsb' 12 8 ·)
  let immJ_b20   := inst.map (BitVec.extractLsb' 20 1 ·)
  let immJ_30_21 := inst.map (BitVec.extractLsb' 21 10 ·)
  let immJ_a := (· ++ ·) <$> immJ_hi <*> immJ_b31
  let immJ_b := (· ++ ·) <$> immJ_19_12 <*> immJ_b20
  let immJ_c := (· ++ ·) <$> immJ_30_21 <*> Signal.pure 0#1
  let immJ_ab := (· ++ ·) <$> immJ_a <*> immJ_b
  let immJ := (· ++ ·) <$> immJ_ab <*> immJ_c

  -- Opcode comparisons (inline literals to avoid let-binding issues in synthesis)
  let isStore  := (· == ·) <$> opcode <*> Signal.pure 0b0100011#7   -- STORE
  let isBranch := (· == ·) <$> opcode <*> Signal.pure 0b1100011#7   -- BRANCH
  let isLUI    := (· == ·) <$> opcode <*> Signal.pure 0b0110111#7   -- LUI
  let isAUIPC  := (· == ·) <$> opcode <*> Signal.pure 0b0010111#7   -- AUIPC
  let isUType  := (· || ·) <$> isLUI <*> isAUIPC
  let isJAL    := (· == ·) <$> opcode <*> Signal.pure 0b1101111#7   -- JAL

  -- Mux cascade: JAL > U-type > Branch > Store > I-type
  Signal.mux isJAL immJ
    (Signal.mux isUType immU
    (Signal.mux isBranch immB
    (Signal.mux isStore immS
      immI)))

#synthesizeVerilog immGenSignal

-- ============================================================================
-- Decoder: ALU Control (Combinational)
-- ============================================================================

/-- Decode ALU operation from opcode, funct3, funct7.
    Inputs:  opcode[6:0], funct3[2:0], funct7[6:0]
    Output:  alu_op[3:0] -/
def aluControlSignal {dom : DomainConfig}
    (opcode : Signal dom (BitVec 7))
    (funct3 : Signal dom (BitVec 3))
    (funct7 : Signal dom (BitVec 7))
    : Signal dom (BitVec 4) :=
  -- Opcode comparisons (inline literals)
  let isALUrr  := (· == ·) <$> opcode <*> Signal.pure 0b0110011#7   -- ALU
  let isALUimm := (· == ·) <$> opcode <*> Signal.pure 0b0010011#7   -- ALUI
  let isALUany := (· || ·) <$> isALUrr <*> isALUimm

  -- funct7 bit 5 (distinguishes ADD/SUB, SRL/SRA)
  let f7bit5 := funct7.map (fun f7 => BitVec.extractLsb' 5 1 f7 == 1#1)

  -- funct3 comparisons
  let f3is0 := (· == ·) <$> funct3 <*> Signal.pure 0#3
  let f3is1 := (· == ·) <$> funct3 <*> Signal.pure 1#3
  let f3is2 := (· == ·) <$> funct3 <*> Signal.pure 2#3
  let f3is3 := (· == ·) <$> funct3 <*> Signal.pure 3#3
  let f3is4 := (· == ·) <$> funct3 <*> Signal.pure 4#3
  let f3is5 := (· == ·) <$> funct3 <*> Signal.pure 5#3
  let f3is6 := (· == ·) <$> funct3 <*> Signal.pure 6#3
  let f3is7 := (· == ·) <$> funct3 <*> Signal.pure 7#3

  -- ALU op mux tree (inline BitVec 4 literals)
  let baseOp :=
    Signal.mux f3is7 (Signal.pure 0x2#4)     -- AND
    (Signal.mux f3is6 (Signal.pure 0x3#4)     -- OR
    (Signal.mux f3is5 (Signal.pure 0x6#4)     -- SRL
    (Signal.mux f3is4 (Signal.pure 0x4#4)     -- XOR
    (Signal.mux f3is3 (Signal.pure 0x9#4)     -- SLTU
    (Signal.mux f3is2 (Signal.pure 0x8#4)     -- SLT
    (Signal.mux f3is1 (Signal.pure 0x5#4)     -- SLL
      (Signal.pure 0x0#4)))))))               -- ADD

  -- SUB: R-type with funct7[5]=1 and funct3=000
  let isSub := (· && ·) <$> ((· && ·) <$> isALUrr <*> f7bit5) <*> f3is0
  -- SRA: ALU with funct7[5]=1 and funct3=101
  let isSRA := (· && ·) <$> ((· && ·) <$> isALUany <*> f7bit5) <*> f3is5

  let aluOpAdj :=
    Signal.mux isSub (Signal.pure 0x1#4)      -- SUB
    (Signal.mux isSRA (Signal.pure 0x7#4)     -- SRA
      baseOp)

  -- Non-ALU ops: LUI=PASS, BRANCH=SUB, others=ADD
  let isLUI    := (· == ·) <$> opcode <*> Signal.pure 0b0110111#7   -- LUI
  let isBranch := (· == ·) <$> opcode <*> Signal.pure 0b1100011#7   -- BRANCH

  let nonAluOp :=
    Signal.mux isLUI (Signal.pure 0xA#4)      -- PASS
    (Signal.mux isBranch (Signal.pure 0x1#4)  -- SUB
      (Signal.pure 0x0#4))

  -- Final mux: ALU instructions use funct3-derived op, others use non-ALU op
  Signal.mux isALUany aluOpAdj nonAluOp

#synthesizeVerilog aluControlSignal

-- ============================================================================
-- Decoder: Control Signals (Combinational)
-- ============================================================================

/-- Generate control signals from opcode.
    Input:  opcode[6:0]
    Output: (alu_src_b × reg_write × mem_read × mem_write
             × mem_to_reg × is_branch × is_jump × auipc × is_jalr) -/
def controlSignalsSignal {dom : DomainConfig}
    (opcode : Signal dom (BitVec 7))
    : Signal dom ((Bool × (Bool × Bool)) × ((Bool × (Bool × Bool)) × (Bool × (Bool × Bool)))) :=
  -- Opcode comparisons (inline literals)
  let isALUrr  := (· == ·) <$> opcode <*> Signal.pure 0b0110011#7   -- ALU
  let isALUimm := (· == ·) <$> opcode <*> Signal.pure 0b0010011#7   -- ALUI
  let isLoad   := (· == ·) <$> opcode <*> Signal.pure 0b0000011#7   -- LOAD
  let isStore  := (· == ·) <$> opcode <*> Signal.pure 0b0100011#7   -- STORE
  let isBranch := (· == ·) <$> opcode <*> Signal.pure 0b1100011#7   -- BRANCH
  let isLUI    := (· == ·) <$> opcode <*> Signal.pure 0b0110111#7   -- LUI
  let isAUIPC  := (· == ·) <$> opcode <*> Signal.pure 0b0010111#7   -- AUIPC
  let isJAL    := (· == ·) <$> opcode <*> Signal.pure 0b1101111#7   -- JAL
  let isJALR   := (· == ·) <$> opcode <*> Signal.pure 0b1100111#7   -- JALR

  -- alu_src_b: true for ALU-imm, LOAD, STORE, LUI, AUIPC, JAL, JALR
  let aluSrcB_a := (· || ·) <$> isALUimm <*> isLoad
  let aluSrcB_b := (· || ·) <$> isStore <*> isLUI
  let aluSrcB_c := (· || ·) <$> isAUIPC <*> isJAL
  let aluSrcB_ab := (· || ·) <$> aluSrcB_a <*> aluSrcB_b
  let aluSrcB_abc := (· || ·) <$> aluSrcB_ab <*> aluSrcB_c
  let aluSrcB := (· || ·) <$> aluSrcB_abc <*> isJALR

  -- reg_write: true for ALU-rr, ALU-imm, LOAD, LUI, AUIPC, JAL, JALR
  let regWrite_a := (· || ·) <$> isALUrr <*> isALUimm
  let regWrite_b := (· || ·) <$> isLoad <*> isLUI
  let regWrite_c := (· || ·) <$> isAUIPC <*> isJAL
  let regWrite_ab := (· || ·) <$> regWrite_a <*> regWrite_b
  let regWrite_abc := (· || ·) <$> regWrite_ab <*> regWrite_c
  let regWrite := (· || ·) <$> regWrite_abc <*> isJALR

  -- mem_read: LOAD only
  let memRead := isLoad
  -- mem_write: STORE only
  let memWrite := isStore
  -- mem_to_reg: LOAD only
  let memToReg := isLoad
  -- is_branch
  let isBranchOut := isBranch
  -- is_jump: JAL or JALR
  let isJump := (· || ·) <$> isJAL <*> isJALR
  -- auipc: AUIPC or JAL (ALU src A = PC)
  let auipc := (· || ·) <$> isAUIPC <*> isJAL
  -- is_jalr
  let isJalrOut := isJALR

  -- Return as nested pairs using bundle2
  let triple1 := bundle2 aluSrcB (bundle2 regWrite memRead)
  let triple2 := bundle2 memWrite (bundle2 memToReg isBranchOut)
  let triple3 := bundle2 isJump (bundle2 auipc isJalrOut)
  let inner   := bundle2 triple2 triple3
  bundle2 triple1 inner

#synthesizeVerilog controlSignalsSignal

end Sparkle.Examples.RV32.Signal
