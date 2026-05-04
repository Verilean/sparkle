/-
  RV32 register-file read — pure logic + invariants

  Extracted from `IP/RV32/SoC.lean` (lines 1255..1268). The
  ID-stage register read involves:

    1. Read the regfile via `Signal.memoryComboRead` — returns
       value at the WB write address if `wb_en`, else the
       stored value.
    2. WB-stage bypass: if the *current* WB cycle writes to the
       same register (wb_addr = id_rs), forward `wb_data`.
    3. Prev-WB-stage bypass: if the *previous* WB-cycle wrote to
       the same register but the regfile read hasn't picked it
       up (memoryComboRead semantics), forward `prev_wb_data`.
    4. x0 carve-out: if `id_rs = 0`, return 0 regardless (RISC-V
       invariant: x0 always reads as 0).

  Spec:

      bypass_value =
        if wb_fwd     then wb_data
        else if prev_fwd then prev_wb_data
        else                  rf_raw

      id_rsVal =
        if id_rs == 0 then 0
        else                  bypass_value

  This file proves:
    * x0 always returns 0.
    * The bypass priority cascade.
    * `wb_fwd` correctness: fires iff `wb_en ∧ wb_addr = id_rs`.

  Note: the wb-bypass path (steps 2 + 3) is structurally similar to
  `Pipeline/Forward.lean` (commit f57f532's WB→EX forwarding) but
  operates at the *register-read* port (ID stage) rather than the
  *operand-input* port (EX stage). The two paths are independent
  and both required to handle the no-forwarding policy correctly.
-/

import Sparkle
import Sparkle.Compiler.Elab

namespace Sparkle.IP.RV32.Pipeline

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ## Pure x0 carve-out -/

/-- x0 always reads as 0; any other index returns the bypass value. -/
@[inline] def x0CarveOutPure
    (rsIdx : BitVec 5) (bypassVal : BitVec 32) : BitVec 32 :=
  if rsIdx == 0#5 then 0#32 else bypassVal

/-! ## Pure WB bypass -/

/-- Two-level WB bypass: priority wb > prev_wb > raw.

    `wb_fwd_rs`     = wb_en  ∧ wb_addr  = id_rs
    `prev_fwd_rs`   = prev_en ∧ prev_addr = id_rs

    The cascade picks the freshest write that targets `id_rs`. -/
@[inline] def wbBypassPure
    (wb_fwd : Bool) (wb_data : BitVec 32)
    (prev_fwd : Bool) (prev_data : BitVec 32)
    (rf_raw : BitVec 32) : BitVec 32 :=
  if wb_fwd then wb_data
  else if prev_fwd then prev_data
  else rf_raw

/-- The ID-stage rs match for WB bypass: en ∧ (addr = idx). -/
@[inline] def wbFwdMatchPure
    (en : Bool) (addr idx : BitVec 5) : Bool :=
  en && (addr == idx)

/-! ## Composed: ID-stage register-read value -/

/-- Final id_rsVal: combines bypass with x0 carve-out. -/
@[inline] def idRsValPure
    (rsIdx : BitVec 5)
    (wb_fwd : Bool) (wb_data : BitVec 32)
    (prev_fwd : Bool) (prev_data : BitVec 32)
    (rf_raw : BitVec 32) : BitVec 32 :=
  x0CarveOutPure rsIdx
    (wbBypassPure wb_fwd wb_data prev_fwd prev_data rf_raw)

/-! ## Spec invariants — closed by `decide` / `rfl` -/

/-- **x0 invariant**: reading x0 always returns 0. -/
@[simp] theorem idRsVal_x0_is_zero
    (wb_fwd : Bool) (wb_data : BitVec 32)
    (prev_fwd : Bool) (prev_data rf_raw : BitVec 32) :
    idRsValPure 0#5 wb_fwd wb_data prev_fwd prev_data rf_raw = 0#32 := by
  unfold idRsValPure x0CarveOutPure
  rfl

/-- For non-zero rs, value comes from bypass cascade. -/
theorem idRsVal_nonzero
    (rsIdx : BitVec 5) (h : rsIdx ≠ 0#5)
    (wb_fwd : Bool) (wb_data : BitVec 32)
    (prev_fwd : Bool) (prev_data rf_raw : BitVec 32) :
    idRsValPure rsIdx wb_fwd wb_data prev_fwd prev_data rf_raw =
      wbBypassPure wb_fwd wb_data prev_fwd prev_data rf_raw := by
  unfold idRsValPure x0CarveOutPure
  have : (rsIdx == 0#5) = false := by
    cases h_eq : rsIdx == 0#5
    · rfl
    · exfalso; apply h
      -- BitVec.beq → eq
      cases hb : rsIdx
      bv_decide
  rw [this]
  rfl

/-! ### WB bypass cascade -/

/-- WB-fwd takes priority over prev-fwd. -/
@[simp] theorem wbBypass_wb_priority
    (wb_data : BitVec 32) (prev_fwd : Bool)
    (prev_data rf_raw : BitVec 32) :
    wbBypassPure true wb_data prev_fwd prev_data rf_raw = wb_data := by rfl

/-- prev-fwd applies when wb-fwd is clear. -/
@[simp] theorem wbBypass_prev_only
    (wb_data prev_data rf_raw : BitVec 32) :
    wbBypassPure false wb_data true prev_data rf_raw = prev_data := by rfl

/-- No fwd → pass through raw. -/
@[simp] theorem wbBypass_no_fwd
    (wb_data prev_data rf_raw : BitVec 32) :
    wbBypassPure false wb_data false prev_data rf_raw = rf_raw := by rfl

/-! ### wbFwdMatch spec -/

/-- en clear → no match. -/
@[simp] theorem wbFwdMatch_no_en (addr idx : BitVec 5) :
    wbFwdMatchPure false addr idx = false := by rfl

/-- addr ≠ idx → no match. -/
theorem wbFwdMatch_no_match
    (en : Bool) (addr idx : BitVec 5)
    (h : (addr == idx) = false) :
    wbFwdMatchPure en addr idx = false := by
  unfold wbFwdMatchPure
  simp [h]

/-- en + addr = idx → match. -/
theorem wbFwdMatch_fires (addr idx : BitVec 5) (h : addr == idx) :
    wbFwdMatchPure true addr idx = true := by
  unfold wbFwdMatchPure
  simp [h]

/-! ## Composite specs -/

theorem x0CarveOutPure_spec
    (rsIdx : BitVec 5) (bypassVal : BitVec 32) :
    x0CarveOutPure rsIdx bypassVal =
      (if rsIdx == 0#5 then 0#32 else bypassVal) := by rfl

theorem wbBypassPure_spec
    (wb_fwd : Bool) (wb_data : BitVec 32)
    (prev_fwd : Bool) (prev_data rf_raw : BitVec 32) :
    wbBypassPure wb_fwd wb_data prev_fwd prev_data rf_raw =
      (if wb_fwd then wb_data
       else if prev_fwd then prev_data
       else rf_raw) := by rfl

/-! ## Signal-level wrappers -/

def x0CarveOutSignal {dom : DomainConfig}
    (rsIdx : Signal dom (BitVec 5))
    (bypassVal : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  Signal.mux (rsIdx === 0#5) (Signal.pure 0#32) bypassVal

def wbFwdMatchSignal {dom : DomainConfig}
    (en : Signal dom Bool)
    (addr idx : Signal dom (BitVec 5)) : Signal dom Bool :=
  en &&& (addr === idx)

def wbBypassSignal {dom : DomainConfig}
    (wb_fwd : Signal dom Bool) (wb_data : Signal dom (BitVec 32))
    (prev_fwd : Signal dom Bool) (prev_data rf_raw : Signal dom (BitVec 32))
    : Signal dom (BitVec 32) :=
  Signal.mux wb_fwd wb_data
    (Signal.mux prev_fwd prev_data rf_raw)

/-! ## Register-file read-address select

  The rf_rs{1,2}_addr inputs to the regfile mux between two
  sources:

    stall = true  →  use the latched id_rs{1,2} (the address
                     used last cycle, since IFID is held).
    stall = false →  extract bits [19:15] (rs1) or [24:20] (rs2)
                     from the new ifid_inst.

  This matches IFID's stall-hold semantics: when IFID holds,
  the regfile must keep reading the same registers to give the
  ALU stable inputs; when IFID advances, the new instruction's
  register fields drive the read.
-/

@[inline] def rfRsAddrPure
    (stall : Bool) (idRs ifidRsField : BitVec 5) : BitVec 5 :=
  if stall then idRs else ifidRsField

@[simp] theorem rfRsAddr_stall (idRs ifidRsField : BitVec 5) :
    rfRsAddrPure true idRs ifidRsField = idRs := rfl

@[simp] theorem rfRsAddr_advance (idRs ifidRsField : BitVec 5) :
    rfRsAddrPure false idRs ifidRsField = ifidRsField := rfl

theorem rfRsAddrPure_spec
    (stall : Bool) (idRs ifidRsField : BitVec 5) :
    rfRsAddrPure stall idRs ifidRsField =
      (if stall then idRs else ifidRsField) := rfl

def rfRsAddrSignal {dom : DomainConfig}
    (stall : Signal dom Bool)
    (idRs ifidRsField : Signal dom (BitVec 5)) : Signal dom (BitVec 5) :=
  Signal.mux stall idRs ifidRsField

end Sparkle.IP.RV32.Pipeline
