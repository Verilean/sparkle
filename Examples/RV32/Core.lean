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

namespace Sparkle.Examples.RV32

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
  let addR := a + b
  let subR := a - b
  let andR := a &&& b
  let orR  := a ||| b
  let xorR := a ^^^ b
  -- RV32I spec: shift amount uses only the lower 5 bits of b
  let shamt := b &&& 0x1F#32
  let sllR := a <<< shamt
  let srlR := a >>> shamt
  let sraR := Signal.ashr a shamt
  -- SLT/SLTU: compare and produce 0 or 1
  let sltCond  := Signal.slt a b
  let sltR     := Signal.mux sltCond (Signal.pure 1#32) (Signal.pure 0#32)
  let sltuCond := Signal.ult a b
  let sltuR    := Signal.mux sltuCond (Signal.pure 1#32) (Signal.pure 0#32)
  -- Mux tree: select result based on op code
  let isOp0 := op === 0#4   -- ADD
  let isOp1 := op === 1#4   -- SUB
  let isOp2 := op === 2#4   -- AND
  let isOp3 := op === 3#4   -- OR
  let isOp4 := op === 4#4   -- XOR
  let isOp5 := op === 5#4   -- SLL
  let isOp6 := op === 6#4   -- SRL
  let isOp7 := op === 7#4   -- SRA
  let isOp8 := op === 8#4   -- SLT
  let isOp9 := op === 9#4   -- SLTU
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
  let beq  := a === b
  let bne  := ~~~beq
  let blt  := Signal.slt a b
  let bge  := ~~~blt
  let bltu := Signal.ult a b
  let bgeu := ~~~bltu
  -- Mux tree: select condition based on funct3
  let f3is0 := funct3 === 0#3  -- BEQ
  let f3is1 := funct3 === 1#3  -- BNE
  let f3is4 := funct3 === 4#3  -- BLT
  let f3is5 := funct3 === 5#3  -- BGE
  let f3is6 := funct3 === 6#3  -- BLTU
  let f3is7 := funct3 === 7#3  -- BGEU
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
  let rdIsZero  := exRd === 0#5
  let rdNonZero := ~~~rdIsZero
  let rs1Match  := exRd === idRs1
  let rs2Match  := exRd === idRs2
  let anyMatch  := rs1Match ||| rs2Match
  let hazard    := rdNonZero &&& anyMatch
  exMemRead &&& hazard

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
    (inst31 === 1#1)
    (Signal.pure 0xFFFFF#20) (Signal.pure 0#20)
  let immI_lo := inst.map (BitVec.extractLsb' 20 12 ·)
  let immI := immI_hi ++ immI_lo

  -- S-type: {sign_ext, inst[31:25], inst[11:7]}
  let immS_hi := Signal.mux
    (inst31 === 1#1)
    (Signal.pure 0xFFFFF#20) (Signal.pure 0#20)
  let immS_mid := inst.map (BitVec.extractLsb' 25 7 ·)
  let immS_lo  := inst.map (BitVec.extractLsb' 7 5 ·)
  let immS_a := immS_hi ++ immS_mid
  let immS := immS_a ++ immS_lo

  -- B-type: {sign_ext[31:13], inst[31], inst[7], inst[30:25], inst[11:8], 0}
  let immB_hi := Signal.mux
    (inst31 === 1#1)
    (Signal.pure 0x7FFFF#19) (Signal.pure 0#19)
  let immB_b31 := inst.map (BitVec.extractLsb' 31 1 ·)
  let immB_b7  := inst.map (BitVec.extractLsb' 7 1 ·)
  let immB_mid := inst.map (BitVec.extractLsb' 25 6 ·)
  let immB_lo  := inst.map (BitVec.extractLsb' 8 4 ·)
  let immB_a := immB_hi ++ immB_b31
  let immB_b := immB_b7 ++ immB_mid
  let immB_c := immB_lo ++ 0#1
  let immB_ab := immB_a ++ immB_b
  let immB := immB_ab ++ immB_c

  -- U-type: {inst[31:12], 12'b0}
  let immU_hi := inst.map (BitVec.extractLsb' 12 20 ·)
  let immU := immU_hi ++ 0#12

  -- J-type: {sign_ext[31:21], inst[31], inst[19:12], inst[20], inst[30:21], 0}
  let immJ_hi  := Signal.mux
    (inst31 === 1#1)
    (Signal.pure 0x7FF#11) (Signal.pure 0#11)
  let immJ_b31   := inst.map (BitVec.extractLsb' 31 1 ·)
  let immJ_19_12 := inst.map (BitVec.extractLsb' 12 8 ·)
  let immJ_b20   := inst.map (BitVec.extractLsb' 20 1 ·)
  let immJ_30_21 := inst.map (BitVec.extractLsb' 21 10 ·)
  let immJ_a := immJ_hi ++ immJ_b31
  let immJ_b := immJ_19_12 ++ immJ_b20
  let immJ_c := immJ_30_21 ++ 0#1
  let immJ_ab := immJ_a ++ immJ_b
  let immJ := immJ_ab ++ immJ_c

  -- Opcode comparisons (inline literals to avoid let-binding issues in synthesis)
  let isStore  := opcode === 0b0100011#7   -- STORE
  let isBranch := opcode === 0b1100011#7   -- BRANCH
  let isLUI    := opcode === 0b0110111#7   -- LUI
  let isAUIPC  := opcode === 0b0010111#7   -- AUIPC
  let isUType  := isLUI ||| isAUIPC
  let isJAL    := opcode === 0b1101111#7   -- JAL

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
  let isALUrr  := opcode === 0b0110011#7   -- ALU
  let isALUimm := opcode === 0b0010011#7   -- ALUI
  let isALUany := isALUrr ||| isALUimm

  -- funct7 bit 5 (distinguishes ADD/SUB, SRL/SRA)
  let f7bit5_raw := funct7.map (BitVec.extractLsb' 5 1 ·)
  let f7bit5 := f7bit5_raw === 1#1

  -- funct3 comparisons
  let f3is0 := funct3 === 0#3
  let f3is1 := funct3 === 1#3
  let f3is2 := funct3 === 2#3
  let f3is3 := funct3 === 3#3
  let f3is4 := funct3 === 4#3
  let f3is5 := funct3 === 5#3
  let f3is6 := funct3 === 6#3
  let f3is7 := funct3 === 7#3

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
  let isSub := (isALUrr &&& f7bit5) &&& f3is0
  -- SRA: ALU with funct7[5]=1 and funct3=101
  let isSRA := (isALUany &&& f7bit5) &&& f3is5

  let aluOpAdj :=
    Signal.mux isSub (Signal.pure 0x1#4)      -- SUB
    (Signal.mux isSRA (Signal.pure 0x7#4)     -- SRA
      baseOp)

  -- Non-ALU ops: LUI=PASS, BRANCH=SUB, others=ADD
  let isLUI    := opcode === 0b0110111#7   -- LUI
  let isBranch := opcode === 0b1100011#7   -- BRANCH

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
  let isALUrr  := opcode === 0b0110011#7   -- ALU
  let isALUimm := opcode === 0b0010011#7   -- ALUI
  let isLoad   := opcode === 0b0000011#7   -- LOAD
  let isStore  := opcode === 0b0100011#7   -- STORE
  let isBranch := opcode === 0b1100011#7   -- BRANCH
  let isLUI    := opcode === 0b0110111#7   -- LUI
  let isAUIPC  := opcode === 0b0010111#7   -- AUIPC
  let isJAL    := opcode === 0b1101111#7   -- JAL
  let isJALR   := opcode === 0b1100111#7   -- JALR

  -- alu_src_b: true for ALU-imm, LOAD, STORE, LUI, AUIPC, JAL, JALR
  let aluSrcB_a := isALUimm ||| isLoad
  let aluSrcB_b := isStore ||| isLUI
  let aluSrcB_c := isAUIPC ||| isJAL
  let aluSrcB_ab := aluSrcB_a ||| aluSrcB_b
  let aluSrcB_abc := aluSrcB_ab ||| aluSrcB_c
  let aluSrcB := aluSrcB_abc ||| isJALR

  -- reg_write: true for ALU-rr, ALU-imm, LOAD, LUI, AUIPC, JAL, JALR
  let regWrite_a := isALUrr ||| isALUimm
  let regWrite_b := isLoad ||| isLUI
  let regWrite_c := isAUIPC ||| isJAL
  let regWrite_ab := regWrite_a ||| regWrite_b
  let regWrite_abc := regWrite_ab ||| regWrite_c
  let regWrite := regWrite_abc ||| isJALR

  -- mem_read: LOAD only
  let memRead := isLoad
  -- mem_write: STORE only
  let memWrite := isStore
  -- mem_to_reg: LOAD only
  let memToReg := isLoad
  -- is_branch
  let isBranchOut := isBranch
  -- is_jump: JAL or JALR
  let isJump := isJAL ||| isJALR
  -- auipc: AUIPC or JAL (ALU src A = PC)
  let auipc := isAUIPC ||| isJAL
  -- is_jalr
  let isJalrOut := isJALR

  -- Return as nested pairs using bundle2
  let triple1 := bundle2 aluSrcB (bundle2 regWrite memRead)
  let triple2 := bundle2 memWrite (bundle2 memToReg isBranchOut)
  let triple3 := bundle2 isJump (bundle2 auipc isJalrOut)
  let inner   := bundle2 triple2 triple3
  bundle2 triple1 inner

#synthesizeVerilog controlSignalsSignal

-- ============================================================================
-- M-Extension: Multiply/Divide (Pure Lean computation for simulation)
-- ============================================================================

/-- Pure Lean computation for all 8 M-extension instructions.

    funct3 encoding (within opcode=0110011, funct7=0000001):
      0 = MUL      lower 32 bits of signed * signed
      1 = MULH     upper 32 bits of signed * signed
      2 = MULHSU   upper 32 bits of signed * unsigned
      3 = MULHU    upper 32 bits of unsigned * unsigned
      4 = DIV      signed division
      5 = DIVU     unsigned division
      6 = REM      signed remainder
      7 = REMU     unsigned remainder

    Edge cases per RISC-V spec:
      DIV  by 0 -> 0xFFFFFFFF (-1 in two's complement)
      DIVU by 0 -> 0xFFFFFFFF
      REM  by 0 -> dividend
      REMU by 0 -> dividend
      Signed overflow: INT_MIN / -1 -> INT_MIN (DIV), 0 (REM) -/
def mextCompute (funct3 : BitVec 3) (rs1 rs2 : BitVec 32) : BitVec 32 :=
  match funct3.toNat with
  | 0 => -- MUL: lower 32 bits of signed * signed
    let prod : Int := rs1.toInt * rs2.toInt
    BitVec.ofInt 32 prod
  | 1 => -- MULH: upper 32 bits of signed * signed
    let prod : Int := rs1.toInt * rs2.toInt
    BitVec.ofInt 32 (prod >>> 32)
  | 2 => -- MULHSU: upper 32 bits of signed * unsigned
    let prod : Int := rs1.toInt * rs2.toNat
    BitVec.ofInt 32 (prod >>> 32)
  | 3 => -- MULHU: upper 32 bits of unsigned * unsigned
    let prod : Nat := rs1.toNat * rs2.toNat
    BitVec.ofNat 32 (prod >>> 32)
  | 4 => -- DIV: signed division
    if rs2 == 0#32 then
      0xFFFFFFFF#32  -- Division by zero
    else if rs1 == 0x80000000#32 && rs2 == 0xFFFFFFFF#32 then
      0x80000000#32  -- Signed overflow: INT_MIN / -1 = INT_MIN
    else
      BitVec.ofInt 32 (rs1.toInt / rs2.toInt)
  | 5 => -- DIVU: unsigned division
    if rs2 == 0#32 then
      0xFFFFFFFF#32  -- Division by zero
    else
      BitVec.ofNat 32 (rs1.toNat / rs2.toNat)
  | 6 => -- REM: signed remainder
    if rs2 == 0#32 then
      rs1  -- Remainder by zero returns dividend
    else if rs1 == 0x80000000#32 && rs2 == 0xFFFFFFFF#32 then
      0#32  -- Signed overflow: INT_MIN % -1 = 0
    else
      BitVec.ofInt 32 (rs1.toInt % rs2.toInt)
  | 7 => -- REMU: unsigned remainder
    if rs2 == 0#32 then
      rs1  -- Remainder by zero returns dividend
    else
      BitVec.ofNat 32 (rs1.toNat % rs2.toNat)
  | _ => 0#32  -- unreachable

-- ============================================================================
-- A-Extension: Atomic Read-Modify-Write (Pure Lean computation for simulation)
-- ============================================================================

/-- Pure Lean computation for AMO instructions (non-LR/SC).

    amoOp = funct7[6:2] (5 bits):
      00001 = AMOSWAP.W
      00000 = AMOADD.W
      00100 = AMOXOR.W
      01100 = AMOAND.W
      01000 = AMOOR.W
      10000 = AMOMIN.W
      10100 = AMOMAX.W
      11000 = AMOMINU.W
      11100 = AMOMAXU.W

    memVal: current value at memory address
    rs2Val: register value to combine with memVal
    Returns: new value to write back to memory -/
def amoCompute (amoOp : BitVec 5) (memVal rs2Val : BitVec 32) : BitVec 32 :=
  match amoOp.toNat with
  | 0b00001 => rs2Val                                                     -- AMOSWAP
  | 0b00000 => memVal + rs2Val                                            -- AMOADD
  | 0b00100 => memVal ^^^ rs2Val                                          -- AMOXOR
  | 0b01100 => memVal &&& rs2Val                                          -- AMOAND
  | 0b01000 => memVal ||| rs2Val                                          -- AMOOR
  | 0b10000 => if memVal.toInt ≤ rs2Val.toInt then memVal else rs2Val     -- AMOMIN
  | 0b10100 => if memVal.toInt ≥ rs2Val.toInt then memVal else rs2Val     -- AMOMAX
  | 0b11000 => if memVal.toNat ≤ rs2Val.toNat then memVal else rs2Val     -- AMOMINU
  | 0b11100 => if memVal.toNat ≥ rs2Val.toNat then memVal else rs2Val     -- AMOMAXU
  | _ => memVal

/-- Signal-level MUL computation (funct3=0..3) using 64-bit multiply.
    Only handles MUL/MULH/MULHSU/MULHU. DIV/REM use separate divider circuit. -/
def mulComputeSignal {dom : DomainConfig}
    (funct3 : Signal dom (BitVec 3))
    (rs1 rs2 : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  -- Sign extension to 64 bits
  let rs1Sign := rs1.map (BitVec.extractLsb' 31 1 ·)
  let rs1IsNeg := rs1Sign === 1#1
  let rs1HiSigned := Signal.mux rs1IsNeg (Signal.pure 0xFFFFFFFF#32) (Signal.pure 0#32)
  let rs1_64_signed := rs1HiSigned ++ rs1
  let rs1_64_unsigned := 0#32 ++ rs1
  let rs2Sign := rs2.map (BitVec.extractLsb' 31 1 ·)
  let rs2IsNeg := rs2Sign === 1#1
  let rs2HiSigned := Signal.mux rs2IsNeg (Signal.pure 0xFFFFFFFF#32) (Signal.pure 0#32)
  let rs2_64_signed := rs2HiSigned ++ rs2
  let rs2_64_unsigned := 0#32 ++ rs2
  -- 64-bit products (ss=signed×signed, su=signed×unsigned, uu=unsigned×unsigned)
  let prod_ss := rs1_64_signed * rs2_64_signed
  let prod_su := rs1_64_signed * rs2_64_unsigned
  let prod_uu := rs1_64_unsigned * rs2_64_unsigned
  -- Extract results
  let mulResult := prod_uu.map (BitVec.extractLsb' 0 32 ·)       -- MUL: lower 32
  let mulhResult := prod_ss.map (BitVec.extractLsb' 32 32 ·)     -- MULH: upper 32 signed×signed
  let mulhsuResult := prod_su.map (BitVec.extractLsb' 32 32 ·)   -- MULHSU: upper 32 signed×unsigned
  let mulhuResult := prod_uu.map (BitVec.extractLsb' 32 32 ·)    -- MULHU: upper 32 unsigned×unsigned
  -- Mux by funct3
  let isMul := funct3 === 0#3
  let isMulh := funct3 === 1#3
  let isMulhsu := funct3 === 2#3
  Signal.mux isMul mulResult
    (Signal.mux isMulh mulhResult
    (Signal.mux isMulhsu mulhsuResult
      mulhuResult))

/-- Signal-level AMO computation using Signal.mux chains (synthesizable).
    Equivalent to `amoCompute` but uses mux instead of if-then-else. -/
def amoComputeSignal {dom : DomainConfig}
    (amoOp : Signal dom (BitVec 5))
    (memVal rs2Val : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  -- Comparison signals
  let isSwap := amoOp === 0b00001#5
  let isAdd  := amoOp === 0b00000#5
  let isXor  := amoOp === 0b00100#5
  let isAnd  := amoOp === 0b01100#5
  let isOr   := amoOp === 0b01000#5
  let isMin  := amoOp === 0b10000#5
  let isMax  := amoOp === 0b10100#5
  let isMinu := amoOp === 0b11000#5
  let isMaxu := amoOp === 0b11100#5
  -- Arithmetic results
  let addResult := memVal + rs2Val
  let xorResult := memVal ^^^ rs2Val
  let andResult := memVal &&& rs2Val
  let orResult  := memVal ||| rs2Val
  -- Signed ≤ (BitVec.sle) and unsigned ≤ (BitVec.ule)
  let signedLe   := Signal.sle memVal rs2Val
  let signedGe   := Signal.sle rs2Val memVal
  let unsignedLe := Signal.ule memVal rs2Val
  let unsignedGe := Signal.ule rs2Val memVal
  -- Min/max results
  let minResult  := Signal.mux signedLe memVal rs2Val
  let maxResult  := Signal.mux signedGe memVal rs2Val
  let minuResult := Signal.mux unsignedLe memVal rs2Val
  let maxuResult := Signal.mux unsignedGe memVal rs2Val
  -- Priority mux chain (last match wins = first mux in chain)
  let result := memVal  -- default
  let result := Signal.mux isMaxu maxuResult result
  let result := Signal.mux isMinu minuResult result
  let result := Signal.mux isMax maxResult result
  let result := Signal.mux isMin minResult result
  let result := Signal.mux isOr orResult result
  let result := Signal.mux isAnd andResult result
  let result := Signal.mux isXor xorResult result
  let result := Signal.mux isAdd addResult result
  let result := Signal.mux isSwap rs2Val result
  result

end Sparkle.Examples.RV32
