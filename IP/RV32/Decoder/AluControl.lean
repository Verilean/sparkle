/-
  RV32 ALU control decoder — pure logic + invariants

  Extracted from `IP/RV32/Core.lean` (`aluControlSignal`, lines
  258..313). Picks the 4-bit ALU op given the opcode (selects
  R-type / I-type / load / store / branch / lui), funct3 (selects
  arithmetic operation within ALU), and funct7 (distinguishes
  ADD/SUB and SRL/SRA).

  RISC-V unprivileged spec §2.4:

    R-type (0110011) / I-type (0010011) — funct3 selects op:
      000  ADD/SUB    funct7[5]=0 → ADD (op=0), funct7[5]=1 → SUB (op=1)
      001  SLL        op=5
      010  SLT        op=8
      011  SLTU       op=9
      100  XOR        op=4
      101  SRL/SRA    funct7[5]=0 → SRL (op=6), funct7[5]=1 → SRA (op=7)
      110  OR         op=3
      111  AND        op=2

    LOAD (0000011) / STORE (0100011) / JAL (1101111) / JALR (1100111)
    / AUIPC (0010111) — all use ADD (op=0) for address computation.

    BRANCH (1100011) — uses SUB (op=1) for the comparator.
    (Branch outcome decided by `branchCompSignal` from funct3,
     not the ALU op.)

    LUI (0110111) — uses PASS (op=A) to pass through B operand.

  Note that I-type SUB (funct3=000, funct7[5]=1) is intentionally
  NOT a thing in RV32I (subi doesn't exist; you use addi with a
  negative immediate). Our decoder maps it to op=0 (ADD), matching
  the spec's behavior of ignoring funct7 for I-type ADDI.
-/

import Sparkle
import Sparkle.Compiler.Elab
import IP.RV32.Core

namespace Sparkle.IP.RV32.Decoder

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ## Pure ALU control decoder -/

/-- Pure ALU control. Mirrors the inline construction in
    `Core.lean`'s `aluControlSignal`. -/
@[inline] def aluControlPure
    (opcode : BitVec 7) (funct3 : BitVec 3) (funct7 : BitVec 7) : BitVec 4 :=
  let isALUrr  := opcode == 0b0110011#7
  let isALUimm := opcode == 0b0010011#7
  let isALUany := isALUrr || isALUimm
  let f7bit5 := funct7.extractLsb' 5 1 == 1#1
  -- Base op from funct3 (priority cascade matching Core.lean)
  let baseOp : BitVec 4 :=
    if funct3 == 7#3 then 0x2#4       -- AND
    else if funct3 == 6#3 then 0x3#4  -- OR
    else if funct3 == 5#3 then 0x6#4  -- SRL
    else if funct3 == 4#3 then 0x4#4  -- XOR
    else if funct3 == 3#3 then 0x9#4  -- SLTU
    else if funct3 == 2#3 then 0x8#4  -- SLT
    else if funct3 == 1#3 then 0x5#4  -- SLL
    else 0x0#4                          -- ADD (funct3=000)
  -- SUB: R-type only (not I-type), funct7[5]=1, funct3=0
  let isSub := isALUrr && f7bit5 && (funct3 == 0#3)
  -- SRA: any ALU, funct7[5]=1, funct3=5
  let isSRA := isALUany && f7bit5 && (funct3 == 5#3)
  let aluOpAdj : BitVec 4 :=
    if isSub then 0x1#4
    else if isSRA then 0x7#4
    else baseOp
  -- Non-ALU ops
  let isLUI    := opcode == 0b0110111#7
  let isBranch := opcode == 0b1100011#7
  let nonAluOp : BitVec 4 :=
    if isLUI then 0xA#4
    else if isBranch then 0x1#4
    else 0x0#4
  if isALUany then aluOpAdj else nonAluOp

/-! ## Per-instruction spec — closed by `decide` over relevant cases -/

/-- ADD: R-type or I-type, funct3=000, funct7[5]=0 → op=0. -/
theorem aluControl_ADD_rtype (funct7lo : BitVec 5) (funct7mid : BitVec 1) :
    aluControlPure 0b0110011#7 0#3 (funct7mid ++ (0#1 : BitVec 1) ++ funct7lo) = 0x0#4 := by
  unfold aluControlPure
  bv_decide

theorem aluControl_ADDI (funct7 : BitVec 7) :
    aluControlPure 0b0010011#7 0#3 funct7 = 0x0#4 := by
  unfold aluControlPure
  bv_decide

/-- SUB: R-type only, funct3=000, funct7[5]=1 → op=1. -/
theorem aluControl_SUB (funct7lo : BitVec 5) (funct7mid : BitVec 1) :
    aluControlPure 0b0110011#7 0#3 (funct7mid ++ (1#1 : BitVec 1) ++ funct7lo) = 0x1#4 := by
  unfold aluControlPure
  bv_decide

/-- SLL: funct3=001 → op=5. -/
theorem aluControl_SLL (funct7 : BitVec 7) :
    aluControlPure 0b0110011#7 1#3 funct7 = 0x5#4 := by
  unfold aluControlPure
  bv_decide

/-- SLT: funct3=010 → op=8. -/
theorem aluControl_SLT (funct7 : BitVec 7) :
    aluControlPure 0b0110011#7 2#3 funct7 = 0x8#4 := by
  unfold aluControlPure
  bv_decide

/-- SLTU: funct3=011 → op=9. -/
theorem aluControl_SLTU (funct7 : BitVec 7) :
    aluControlPure 0b0110011#7 3#3 funct7 = 0x9#4 := by
  unfold aluControlPure
  bv_decide

/-- XOR: funct3=100 → op=4. -/
theorem aluControl_XOR (funct7 : BitVec 7) :
    aluControlPure 0b0110011#7 4#3 funct7 = 0x4#4 := by
  unfold aluControlPure
  bv_decide

/-- SRL: funct3=101, funct7[5]=0 → op=6. -/
theorem aluControl_SRL (funct7lo : BitVec 5) (funct7mid : BitVec 1) :
    aluControlPure 0b0110011#7 5#3 (funct7mid ++ (0#1 : BitVec 1) ++ funct7lo) = 0x6#4 := by
  unfold aluControlPure
  bv_decide

/-- SRA: funct3=101, funct7[5]=1 → op=7. -/
theorem aluControl_SRA (funct7lo : BitVec 5) (funct7mid : BitVec 1) :
    aluControlPure 0b0110011#7 5#3 (funct7mid ++ (1#1 : BitVec 1) ++ funct7lo) = 0x7#4 := by
  unfold aluControlPure
  bv_decide

/-- OR: funct3=110 → op=3. -/
theorem aluControl_OR (funct7 : BitVec 7) :
    aluControlPure 0b0110011#7 6#3 funct7 = 0x3#4 := by
  unfold aluControlPure
  bv_decide

/-- AND: funct3=111 → op=2. -/
theorem aluControl_AND (funct7 : BitVec 7) :
    aluControlPure 0b0110011#7 7#3 funct7 = 0x2#4 := by
  unfold aluControlPure
  bv_decide

/-! ### Non-ALU ops -/

/-- LOAD always gets ADD (op=0) for address computation. -/
theorem aluControl_LOAD (funct3 : BitVec 3) (funct7 : BitVec 7) :
    aluControlPure 0b0000011#7 funct3 funct7 = 0x0#4 := by
  unfold aluControlPure
  bv_decide

/-- STORE always gets ADD. -/
theorem aluControl_STORE (funct3 : BitVec 3) (funct7 : BitVec 7) :
    aluControlPure 0b0100011#7 funct3 funct7 = 0x0#4 := by
  unfold aluControlPure
  bv_decide

/-- BRANCH gets SUB (op=1) for the comparator. -/
theorem aluControl_BRANCH (funct3 : BitVec 3) (funct7 : BitVec 7) :
    aluControlPure 0b1100011#7 funct3 funct7 = 0x1#4 := by
  unfold aluControlPure
  bv_decide

/-- LUI gets PASS (op=A). -/
theorem aluControl_LUI (funct3 : BitVec 3) (funct7 : BitVec 7) :
    aluControlPure 0b0110111#7 funct3 funct7 = 0xA#4 := by
  unfold aluControlPure
  bv_decide

/-- AUIPC gets ADD. -/
theorem aluControl_AUIPC (funct3 : BitVec 3) (funct7 : BitVec 7) :
    aluControlPure 0b0010111#7 funct3 funct7 = 0x0#4 := by
  unfold aluControlPure
  bv_decide

/-- JAL/JALR get ADD (default for non-ALU/non-LUI/non-BRANCH). -/
theorem aluControl_JAL (funct3 : BitVec 3) (funct7 : BitVec 7) :
    aluControlPure 0b1101111#7 funct3 funct7 = 0x0#4 := by
  unfold aluControlPure
  bv_decide

theorem aluControl_JALR (funct3 : BitVec 3) (funct7 : BitVec 7) :
    aluControlPure 0b1100111#7 funct3 funct7 = 0x0#4 := by
  unfold aluControlPure
  bv_decide

end Sparkle.IP.RV32.Decoder
