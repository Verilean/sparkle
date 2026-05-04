/-
  RV32 ALU input selectors — pure logic + invariants

  Extracted from `IP/RV32/SoC.lean` (lines 441..442, 893..894).
  Each ALU operand has a 2-way mux:

    alu_a = if idex_auipc   then idex_pc  else ex_rs1
    alu_b = if idex_aluSrcB then idex_imm else ex_rs2

  Per RV32I §2.4:
    * AUIPC and JAL use PC as srcA (the "auipc" control signal
      is set for both — the result is `pc + imm` for AUIPC and
      the JAL return-address). All other instructions use rs1.
    * OP-IMM, LOAD, STORE, LUI, AUIPC, JAL, JALR use the
      immediate as srcB (the "aluSrcB" control signal). R-type
      and BRANCH use rs2.

  This file proves the per-control-signal cases.
-/

import Sparkle
import Sparkle.Compiler.Elab

namespace Sparkle.IP.RV32.Pipeline

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ## Pure ALU input selectors -/

/-- ALU srcA selector. -/
@[inline] def aluSrcAPure
    (idex_auipc : Bool) (pc rs1 : BitVec 32) : BitVec 32 :=
  if idex_auipc then pc else rs1

/-- ALU srcB selector. -/
@[inline] def aluSrcBPure
    (idex_aluSrcB : Bool) (imm rs2 : BitVec 32) : BitVec 32 :=
  if idex_aluSrcB then imm else rs2

/-! ## Spec invariants -/

/-- AUIPC/JAL → use PC as srcA. -/
@[simp] theorem aluSrcA_pc (pc rs1 : BitVec 32) :
    aluSrcAPure true pc rs1 = pc := by rfl

/-- Other instructions → use rs1 as srcA. -/
@[simp] theorem aluSrcA_rs1 (pc rs1 : BitVec 32) :
    aluSrcAPure false pc rs1 = rs1 := by rfl

/-- aluSrcB=1 → use immediate as srcB. -/
@[simp] theorem aluSrcB_imm (imm rs2 : BitVec 32) :
    aluSrcBPure true imm rs2 = imm := by rfl

/-- aluSrcB=0 → use rs2 as srcB. -/
@[simp] theorem aluSrcB_rs2 (imm rs2 : BitVec 32) :
    aluSrcBPure false imm rs2 = rs2 := by rfl

/-! ## Composite specs -/

theorem aluSrcAPure_spec
    (idex_auipc : Bool) (pc rs1 : BitVec 32) :
    aluSrcAPure idex_auipc pc rs1 =
      (if idex_auipc then pc else rs1) := by rfl

theorem aluSrcBPure_spec
    (idex_aluSrcB : Bool) (imm rs2 : BitVec 32) :
    aluSrcBPure idex_aluSrcB imm rs2 =
      (if idex_aluSrcB then imm else rs2) := by rfl

/-! ## Signal-level wrappers -/

def aluSrcASignal {dom : DomainConfig}
    (idex_auipc : Signal dom Bool)
    (pc rs1 : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  Signal.mux idex_auipc pc rs1

def aluSrcBSignal {dom : DomainConfig}
    (idex_aluSrcB : Signal dom Bool)
    (imm rs2 : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  Signal.mux idex_aluSrcB imm rs2

end Sparkle.IP.RV32.Pipeline
