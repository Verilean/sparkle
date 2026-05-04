/-
  RV32 ALU/Mext result composition — pure logic + invariants

  Extracted from `IP/RV32/SoC.lean` (lines 1117..1118). The
  EX-stage produces a single result by combining:

    1. Base ALU result (`aluSignal idex_aluOp alu_a alu_b`).
    2. M-extension result (multiply or divide).

  Spec:

      mextResult = if isDivOp then divResult else mulResult
      alu_result = if idex_isMext then mextResult else alu_result_raw

  The `isDivOp` predicate is `funct3[2] = 1` (DIV/DIVU/REM/REMU
  have funct3 ∈ {4,5,6,7}, all with bit 2 set; MUL/MULH/MULHSU/
  MULHU have funct3 ∈ {0,1,2,3}, bit 2 clear).

  Companion to:
    * Mext/Mul.lean   — multiply ops
    * Mext/Div.lean   — divide edge cases
    * ALU/Compute.lean — base ALU
-/

import Sparkle
import Sparkle.Compiler.Elab

namespace Sparkle.IP.RV32.Pipeline

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ## Pure result composition -/

/-- isDivOp: funct3[2] = 1 (DIV/DIVU/REM/REMU). -/
@[inline] def isDivOpPure (funct3 : BitVec 3) : Bool :=
  funct3.extractLsb' 2 1 == 1#1

/-- M-ext result: divResult if DIV/REM op, else mulResult. -/
@[inline] def mextResultPure
    (isDivOp : Bool) (divResult mulResult : BitVec 32) : BitVec 32 :=
  if isDivOp then divResult else mulResult

/-- Final EX result: M-ext result if M-extension instruction, else base ALU. -/
@[inline] def aluResultPure
    (idex_isMext : Bool) (mextResult alu_result_raw : BitVec 32) : BitVec 32 :=
  if idex_isMext then mextResult else alu_result_raw

/-! ## Spec invariants — closed by `bv_decide` / `rfl` -/

/-- DIV/REM op (funct3=4,5,6,7) → isDivOp fires. -/
theorem isDivOp_div : isDivOpPure 4#3 = true := by
  unfold isDivOpPure; bv_decide

theorem isDivOp_divu : isDivOpPure 5#3 = true := by
  unfold isDivOpPure; bv_decide

theorem isDivOp_rem : isDivOpPure 6#3 = true := by
  unfold isDivOpPure; bv_decide

theorem isDivOp_remu : isDivOpPure 7#3 = true := by
  unfold isDivOpPure; bv_decide

/-- MUL/MULH/MULHSU/MULHU (funct3=0..3) → isDivOp clear. -/
theorem isDivOp_mul : isDivOpPure 0#3 = false := by
  unfold isDivOpPure; bv_decide

theorem isDivOp_mulh : isDivOpPure 1#3 = false := by
  unfold isDivOpPure; bv_decide

theorem isDivOp_mulhsu : isDivOpPure 2#3 = false := by
  unfold isDivOpPure; bv_decide

theorem isDivOp_mulhu : isDivOpPure 3#3 = false := by
  unfold isDivOpPure; bv_decide

/-! ### Composition spec -/

/-- M-ext: divOp → divResult. -/
@[simp] theorem mextResult_div (divResult mulResult : BitVec 32) :
    mextResultPure true divResult mulResult = divResult := by rfl

/-- M-ext: !divOp → mulResult. -/
@[simp] theorem mextResult_mul (divResult mulResult : BitVec 32) :
    mextResultPure false divResult mulResult = mulResult := by rfl

/-- alu_result: M-extension instruction → mextResult. -/
@[simp] theorem aluResult_mext (mextResult alu_result_raw : BitVec 32) :
    aluResultPure true mextResult alu_result_raw = mextResult := by rfl

/-- alu_result: non-M instruction → alu_result_raw. -/
@[simp] theorem aluResult_base (mextResult alu_result_raw : BitVec 32) :
    aluResultPure false mextResult alu_result_raw = alu_result_raw := by rfl

/-! ## Composite specs -/

theorem mextResultPure_spec
    (isDivOp : Bool) (divResult mulResult : BitVec 32) :
    mextResultPure isDivOp divResult mulResult =
      (if isDivOp then divResult else mulResult) := by rfl

theorem aluResultPure_spec
    (idex_isMext : Bool) (mextResult alu_result_raw : BitVec 32) :
    aluResultPure idex_isMext mextResult alu_result_raw =
      (if idex_isMext then mextResult else alu_result_raw) := by rfl

/-! ## Signal-level wrappers -/

def isDivOpSignal {dom : DomainConfig}
    (funct3 : Signal dom (BitVec 3)) : Signal dom Bool :=
  (funct3.map (BitVec.extractLsb' 2 1 ·)) === 1#1

def mextResultSignal {dom : DomainConfig}
    (isDivOp : Signal dom Bool)
    (divResult mulResult : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  Signal.mux isDivOp divResult mulResult

def aluResultSignal {dom : DomainConfig}
    (idex_isMext : Signal dom Bool)
    (mextResult alu_result_raw : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  Signal.mux idex_isMext mextResult alu_result_raw

end Sparkle.IP.RV32.Pipeline
