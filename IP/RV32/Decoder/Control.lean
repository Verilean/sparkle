/-
  RV32 control-signals decoder — pure logic + invariants

  Extracted from `IP/RV32/Core.lean` (`controlSignalsSignal`,
  lines 325..375). Maps a 7-bit opcode into 9 control booleans
  consumed by the EX/MEM/WB stages.

  Per RV32I §2 (instruction encoding) — for each opcode we know
  exactly which control signals must be set:

    opcode    aluSrcB  regWrite  memRead  memWrite  memToReg
              isBranch isJump    auipc    isJalr
    -------   --------------------------------------------
    0110011   F  T  F  F  F      F  F     F  F      (R-type)
    0010011   T  T  F  F  F      F  F     F  F      (I-OP)
    0000011   T  T  T  F  T      F  F     F  F      (LOAD)
    0100011   T  F  F  T  F      F  F     F  F      (STORE)
    1100011   F  F  F  F  F      T  F     F  F      (BRANCH)
    0110111   T  T  F  F  F      F  F     F  F      (LUI)
    0010111   T  T  F  F  F      F  F     T  F      (AUIPC)
    1101111   T  T  F  F  F      F  T     T  F      (JAL)
    1100111   T  T  F  F  F      F  T     F  T      (JALR)

  This is the canonical "control table" of RV32I, made
  machine-checkable.
-/

import Sparkle
import Sparkle.Compiler.Elab
import IP.RV32.Core

namespace Sparkle.IP.RV32.Decoder

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ## Per-control pure functions -/

/-- ALU srcB selector: TRUE means use the immediate; FALSE means rs2.
    Set for every opcode except R-type and BRANCH. -/
@[inline] def ctrlAluSrcBPure (opcode : BitVec 7) : Bool :=
  (opcode == 0b0010011#7) || (opcode == 0b0000011#7) ||
  (opcode == 0b0100011#7) || (opcode == 0b0110111#7) ||
  (opcode == 0b0010111#7) || (opcode == 0b1101111#7) ||
  (opcode == 0b1100111#7)

/-- Reg-write enable. TRUE for every opcode that writes a destination
    register. False for STORE and BRANCH. -/
@[inline] def ctrlRegWritePure (opcode : BitVec 7) : Bool :=
  (opcode == 0b0110011#7) || (opcode == 0b0010011#7) ||
  (opcode == 0b0000011#7) || (opcode == 0b0110111#7) ||
  (opcode == 0b0010111#7) || (opcode == 0b1101111#7) ||
  (opcode == 0b1100111#7)

/-- mem_read: only LOAD reads memory in EX/MEM. -/
@[inline] def ctrlMemReadPure (opcode : BitVec 7) : Bool :=
  opcode == 0b0000011#7

/-- mem_write: only STORE writes memory. -/
@[inline] def ctrlMemWritePure (opcode : BitVec 7) : Bool :=
  opcode == 0b0100011#7

/-- mem_to_reg: only LOAD writes back from memory. -/
@[inline] def ctrlMemToRegPure (opcode : BitVec 7) : Bool :=
  opcode == 0b0000011#7

/-- is_branch: only BRANCH instructions. -/
@[inline] def ctrlIsBranchPure (opcode : BitVec 7) : Bool :=
  opcode == 0b1100011#7

/-- is_jump: JAL or JALR. -/
@[inline] def ctrlIsJumpPure (opcode : BitVec 7) : Bool :=
  (opcode == 0b1101111#7) || (opcode == 0b1100111#7)

/-- auipc-style: ALU srcA = PC. AUIPC or JAL. -/
@[inline] def ctrlAuipcPure (opcode : BitVec 7) : Bool :=
  (opcode == 0b0010111#7) || (opcode == 0b1101111#7)

/-- is_jalr: only JALR (used to mask jumpTarget's LSB). -/
@[inline] def ctrlIsJalrPure (opcode : BitVec 7) : Bool :=
  opcode == 0b1100111#7

/-! ## Per-opcode spec — `bv_decide` over BitVec 7 -/

/-- Generic unfold-then-bv_decide tactic for the per-opcode theorems. -/
local macro "ctrl_decide" : tactic =>
  `(tactic|
     first
     | (simp only [ctrlAluSrcBPure, ctrlRegWritePure, ctrlMemReadPure,
                  ctrlMemWritePure, ctrlMemToRegPure, ctrlIsBranchPure,
                  ctrlIsJumpPure, ctrlAuipcPure, ctrlIsJalrPure]; bv_decide)
     | bv_decide)

/-- R-type (0110011): aluSrcB=F, regWrite=T, all-others=F. -/
theorem ctrl_R_TYPE :
    ctrlAluSrcBPure 0b0110011#7 = false ∧
    ctrlRegWritePure 0b0110011#7 = true ∧
    ctrlMemReadPure 0b0110011#7 = false ∧
    ctrlMemWritePure 0b0110011#7 = false ∧
    ctrlMemToRegPure 0b0110011#7 = false ∧
    ctrlIsBranchPure 0b0110011#7 = false ∧
    ctrlIsJumpPure 0b0110011#7 = false ∧
    ctrlAuipcPure 0b0110011#7 = false ∧
    ctrlIsJalrPure 0b0110011#7 = false := by

  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ctrl_decide

/-- I-OP (0010011): aluSrcB=T, regWrite=T. -/
theorem ctrl_I_OP :
    ctrlAluSrcBPure 0b0010011#7 = true ∧
    ctrlRegWritePure 0b0010011#7 = true ∧
    ctrlMemReadPure 0b0010011#7 = false ∧
    ctrlMemWritePure 0b0010011#7 = false := by

  refine ⟨?_, ?_, ?_, ?_⟩ <;> ctrl_decide

/-- LOAD (0000011): aluSrcB=T, regWrite=T, memRead=T, memToReg=T. -/
theorem ctrl_LOAD :
    ctrlAluSrcBPure 0b0000011#7 = true ∧
    ctrlRegWritePure 0b0000011#7 = true ∧
    ctrlMemReadPure 0b0000011#7 = true ∧
    ctrlMemWritePure 0b0000011#7 = false ∧
    ctrlMemToRegPure 0b0000011#7 = true := by

  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> ctrl_decide

/-- STORE (0100011): aluSrcB=T, regWrite=F, memWrite=T. -/
theorem ctrl_STORE :
    ctrlAluSrcBPure 0b0100011#7 = true ∧
    ctrlRegWritePure 0b0100011#7 = false ∧
    ctrlMemReadPure 0b0100011#7 = false ∧
    ctrlMemWritePure 0b0100011#7 = true := by

  refine ⟨?_, ?_, ?_, ?_⟩ <;> ctrl_decide

/-- BRANCH (1100011): all base-control bits clear, isBranch=T. -/
theorem ctrl_BRANCH :
    ctrlAluSrcBPure 0b1100011#7 = false ∧
    ctrlRegWritePure 0b1100011#7 = false ∧
    ctrlMemReadPure 0b1100011#7 = false ∧
    ctrlMemWritePure 0b1100011#7 = false ∧
    ctrlIsBranchPure 0b1100011#7 = true := by

  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> ctrl_decide

/-- LUI (0110111): aluSrcB=T, regWrite=T. -/
theorem ctrl_LUI :
    ctrlAluSrcBPure 0b0110111#7 = true ∧
    ctrlRegWritePure 0b0110111#7 = true ∧
    ctrlAuipcPure 0b0110111#7 = false := by

  refine ⟨?_, ?_, ?_⟩ <;> ctrl_decide

/-- AUIPC (0010111): aluSrcB=T, regWrite=T, auipc=T. -/
theorem ctrl_AUIPC :
    ctrlAluSrcBPure 0b0010111#7 = true ∧
    ctrlRegWritePure 0b0010111#7 = true ∧
    ctrlAuipcPure 0b0010111#7 = true := by

  refine ⟨?_, ?_, ?_⟩ <;> ctrl_decide

/-- JAL (1101111): aluSrcB=T, regWrite=T, isJump=T, auipc=T. -/
theorem ctrl_JAL :
    ctrlAluSrcBPure 0b1101111#7 = true ∧
    ctrlRegWritePure 0b1101111#7 = true ∧
    ctrlIsJumpPure 0b1101111#7 = true ∧
    ctrlAuipcPure 0b1101111#7 = true ∧
    ctrlIsJalrPure 0b1101111#7 = false := by

  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> ctrl_decide

/-- JALR (1100111): aluSrcB=T, regWrite=T, isJump=T, auipc=F, isJalr=T. -/
theorem ctrl_JALR :
    ctrlAluSrcBPure 0b1100111#7 = true ∧
    ctrlRegWritePure 0b1100111#7 = true ∧
    ctrlIsJumpPure 0b1100111#7 = true ∧
    ctrlAuipcPure 0b1100111#7 = false ∧
    ctrlIsJalrPure 0b1100111#7 = true := by

  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> ctrl_decide

/-! ## Mutual exclusion (per-opcode safety) -/

/-- mem_read and mem_write are never both set: a single instruction
    is either a load or a store, not both. -/
theorem ctrl_memRead_memWrite_disjoint (opcode : BitVec 7) :
    !(ctrlMemReadPure opcode && ctrlMemWritePure opcode) = true := by
  unfold ctrlMemReadPure ctrlMemWritePure
  revert opcode; bv_decide

/-- isJalr implies isJump (JALR is a jump). -/
theorem ctrl_jalr_implies_jump (opcode : BitVec 7) :
    ctrlIsJalrPure opcode = true → ctrlIsJumpPure opcode = true := by
  unfold ctrlIsJalrPure ctrlIsJumpPure
  intro h
  rw [h]
  cases opcode == 0b1101111#7 <;> rfl

end Sparkle.IP.RV32.Decoder
