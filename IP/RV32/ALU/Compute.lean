/-
  RV32 ALU computation — pure logic + invariants

  The Signal-level `aluSignal` is in `IP/RV32/Core.lean`. This file
  adds the pure counterpart over `BitVec 4` (opcode) and two
  `BitVec 32` operands, with `bv_decide`-closed correctness for
  each of the eleven ALU operations.

  Op encoding (per `ALUOp.toBitVec4`):

    0  ADD     a + b
    1  SUB     a - b
    2  AND     a ∧ b
    3  OR      a ∨ b
    4  XOR     a ⊕ b
    5  SLL     a <<< (b & 0x1F)        (logical-left shift)
    6  SRL     a >>> (b & 0x1F)        (logical-right shift)
    7  SRA     ashr a   (b & 0x1F)     (arithmetic-right shift)
    8  SLT     (a <ₛ b) ? 1 : 0        (signed)
    9  SLTU    (a <ᵤ b) ? 1 : 0        (unsigned)
    A  PASS    b                       (pass-through, used for LUI)

  RV32I shift instructions use only the low 5 bits of `b` as the
  shift amount (per spec §2.4.1). The mask `b & 0x1F` is part of
  the implementation.
-/

import Sparkle
import Sparkle.Compiler.Elab
import IP.RV32.Core

namespace Sparkle.IP.RV32.ALU

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ## Pure ALU compute -/

/-- 11-way ALU. Default arm = pass-through `b`. -/
@[inline] def aluComputePure
    (op : BitVec 4) (a b : BitVec 32) : BitVec 32 :=
  let shamt := b &&& 0x1F#32
  if op == 0#4 then a + b                               -- ADD
  else if op == 1#4 then a - b                          -- SUB
  else if op == 2#4 then a &&& b                        -- AND
  else if op == 3#4 then a ||| b                        -- OR
  else if op == 4#4 then a ^^^ b                        -- XOR
  else if op == 5#4 then a <<< shamt                    -- SLL
  else if op == 6#4 then a >>> shamt                    -- SRL
  else if op == 7#4 then BitVec.sshiftRight' a shamt    -- SRA
  else if op == 8#4 then (if a.slt b then 1#32 else 0#32) -- SLT
  else if op == 9#4 then (if a.ult b then 1#32 else 0#32) -- SLTU
  else b                                                -- PASS (op=A)

/-! ## Per-op specs — closed by `bv_decide` -/

theorem alu_ADD (a b : BitVec 32) :
    aluComputePure 0#4 a b = a + b := by
  unfold aluComputePure
  bv_decide

theorem alu_SUB (a b : BitVec 32) :
    aluComputePure 1#4 a b = a - b := by
  unfold aluComputePure
  bv_decide

theorem alu_AND (a b : BitVec 32) :
    aluComputePure 2#4 a b = a &&& b := by
  unfold aluComputePure
  bv_decide

theorem alu_OR (a b : BitVec 32) :
    aluComputePure 3#4 a b = a ||| b := by
  unfold aluComputePure
  bv_decide

theorem alu_XOR (a b : BitVec 32) :
    aluComputePure 4#4 a b = a ^^^ b := by
  unfold aluComputePure
  bv_decide

theorem alu_SLL (a b : BitVec 32) :
    aluComputePure 5#4 a b = a <<< (b &&& 0x1F#32) := by
  unfold aluComputePure
  bv_decide

theorem alu_SRL (a b : BitVec 32) :
    aluComputePure 6#4 a b = a >>> (b &&& 0x1F#32) := by
  unfold aluComputePure
  bv_decide

theorem alu_SRA (a b : BitVec 32) :
    aluComputePure 7#4 a b = BitVec.sshiftRight' a (b &&& 0x1F#32) := by
  unfold aluComputePure
  bv_decide

theorem alu_SLT (a b : BitVec 32) :
    aluComputePure 8#4 a b = (if a.slt b then 1#32 else 0#32) := by
  unfold aluComputePure
  bv_decide

theorem alu_SLTU (a b : BitVec 32) :
    aluComputePure 9#4 a b = (if a.ult b then 1#32 else 0#32) := by
  unfold aluComputePure
  bv_decide

/-- PASS: any op outside 0..9 returns b (lui's "load upper immediate"). -/
theorem alu_PASS_A (a b : BitVec 32) :
    aluComputePure 0xA#4 a b = b := by
  unfold aluComputePure
  bv_decide

/-! ## Sanity invariants -/

/-- ADD with zero is identity. -/
theorem alu_ADD_zero (a : BitVec 32) :
    aluComputePure 0#4 a 0#32 = a := by
  unfold aluComputePure
  bv_decide

/-- SUB with self is zero. -/
theorem alu_SUB_self (a : BitVec 32) :
    aluComputePure 1#4 a a = 0#32 := by
  unfold aluComputePure
  bv_decide

/-- AND with all-ones is identity. -/
theorem alu_AND_allOnes (a : BitVec 32) :
    aluComputePure 2#4 a 0xFFFFFFFF#32 = a := by
  unfold aluComputePure
  bv_decide

/-- OR with zero is identity. -/
theorem alu_OR_zero (a : BitVec 32) :
    aluComputePure 3#4 a 0#32 = a := by
  unfold aluComputePure
  bv_decide

/-- XOR with self is zero. -/
theorem alu_XOR_self (a : BitVec 32) :
    aluComputePure 4#4 a a = 0#32 := by
  unfold aluComputePure
  bv_decide

/-- SLT a a is 0 (a <ₛ a is false). -/
theorem alu_SLT_self (a : BitVec 32) :
    aluComputePure 8#4 a a = 0#32 := by
  unfold aluComputePure
  bv_decide

/-- SLTU a a is 0 (a <ᵤ a is false). -/
theorem alu_SLTU_self (a : BitVec 32) :
    aluComputePure 9#4 a a = 0#32 := by
  unfold aluComputePure
  bv_decide

end Sparkle.IP.RV32.ALU
