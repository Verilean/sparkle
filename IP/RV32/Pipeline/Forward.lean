/-
  RV32 register-file forwarding — pure logic + invariants

  Extracted from `IP/RV32/SoC.lean` (lines 395..401, 858..859). The
  Sparkle pipeline does NOT forward general results — instead, it
  uses a single WB→EX forwarding path *with a load-use stall*.

  Forwarding logic:

      fwd_rs_match = wb_en ∧ (wb_addr = idex_rs_idx)
      ex_rs        = if fwd_rs_match then wb_data else idex_rs_val

  Where `wb_en = exwb_regW ∧ (exwb_rd ≠ 0)`, computed upstream.

  This file captures the match predicate and the value selector,
  proving:
    - When wb_en clear, no forwarding (always returns idex_rsVal).
    - When wb_addr ≠ idex_rs_idx, no forwarding.
    - When wb_addr = idex_rs_idx and wb_en, returns wb_data.

  These invariants are the core "no stale read" guarantee for the
  EX stage's source operands when the immediately-prior instruction
  wrote to the same register (and is not a load — load-use is
  handled by stalling, not forwarding).

  Reference: docs/RV32_Architecture_Status.md §1.2 (pipeline policy:
  "no general forwarding, only WB→EX, with load-use stall").
-/

import Sparkle
import Sparkle.Compiler.Elab

namespace Sparkle.IP.RV32.Pipeline

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ## Pure forwarding logic -/

/-- Forwarding-match predicate: wb_en ∧ (wb_addr = rs_idx).

    `wb_en` is upstream-gated to be `false` when `exwb_rd = 0`, so this
    predicate is also implicitly `false` for `rs_idx = 0` (never forward
    to x0; x0 always reads as 0). -/
@[inline] def fwdMatchPure
    (wb_en : Bool) (wb_addr rs_idx : BitVec 5) : Bool :=
  wb_en && (wb_addr == rs_idx)

/-- Forwarded EX-stage source operand:
    `if fwd_match then wb_data else idex_rsVal`. -/
@[inline] def fwdValuePure
    (fwd_match : Bool) (wb_data idex_rsVal : BitVec 32) : BitVec 32 :=
  if fwd_match then wb_data else idex_rsVal

/-! ## Spec invariants — closed by `decide` / `bv_decide` -/

/-- When `wb_en` is clear, no forwarding. -/
@[simp] theorem fwdMatch_no_writeback
    (wb_addr rs_idx : BitVec 5) :
    fwdMatchPure false wb_addr rs_idx = false := by
  rfl

/-- When wb_addr ≠ rs_idx, no forwarding (regardless of wb_en). -/
theorem fwdMatch_no_match
    (wb_en : Bool) (wb_addr rs_idx : BitVec 5)
    (h : (wb_addr == rs_idx) = false) :
    fwdMatchPure wb_en wb_addr rs_idx = false := by
  unfold fwdMatchPure
  simp [h]

/-- When wb_en and wb_addr = rs_idx, forwarding fires. -/
theorem fwdMatch_fires
    (wb_addr rs_idx : BitVec 5) (h : wb_addr == rs_idx) :
    fwdMatchPure true wb_addr rs_idx = true := by
  unfold fwdMatchPure
  simp [h]

/-- Match implies wb_en is true. -/
theorem fwdMatch_implies_wb_en
    (wb_en : Bool) (wb_addr rs_idx : BitVec 5) :
    fwdMatchPure wb_en wb_addr rs_idx = true → wb_en = true := by
  unfold fwdMatchPure
  intro h
  rcases (Bool.and_eq_true _ _).mp h with ⟨h1, _⟩
  exact h1

/-- Match implies wb_addr `==` rs_idx (Bool form). -/
theorem fwdMatch_implies_addr_beq
    (wb_en : Bool) (wb_addr rs_idx : BitVec 5) :
    fwdMatchPure wb_en wb_addr rs_idx = true →
    (wb_addr == rs_idx) = true := by
  unfold fwdMatchPure
  intro h
  rcases (Bool.and_eq_true _ _).mp h with ⟨_, h2⟩
  exact h2

/-! ## Forwarded-value spec -/

/-- No match: pass through the IDEX-stage value. -/
@[simp] theorem fwdValue_no_match
    (wb_data idex_rsVal : BitVec 32) :
    fwdValuePure false wb_data idex_rsVal = idex_rsVal := by
  rfl

/-- Match: take the WB-stage value. -/
@[simp] theorem fwdValue_match
    (wb_data idex_rsVal : BitVec 32) :
    fwdValuePure true wb_data idex_rsVal = wb_data := by
  rfl

/-! ## Approximate forwarded value (load-aware)

  For combinational EX paths (e.g., store address, mtimecmp IRQ
  decision) where the exact rs1 value matters but the WB-stage
  load result isn't ready (loads only resolve in the second WB
  cycle), conservatively pick:

    fwdValApprox = if exwb_m2r then idex_rsVal       -- load not ready
                   else                wb_data_non_mem

  When `exwb_m2r` (memory-to-register, i.e., a load) is in WB,
  the WB result is the load datum which the EX-stage path can't
  see this cycle — so we use idex_rsVal (a stale-but-safe value).

  Then the standard `fwdMatchPure`/`fwdValuePure` is applied on
  top to choose between this approx and idex_rsVal.

  This matches SoC.lean's `fwd_val_approx`/`fwd_val2_approx`
  inline mux at lines 451 / 454. -/

@[inline] def fwdValApproxPure
    (exwb_m2r : Bool) (idex_rsVal wb_data_non_mem : BitVec 32) : BitVec 32 :=
  if exwb_m2r then idex_rsVal else wb_data_non_mem

/-- Load in WB: approx-fwd takes the IDEX value (load result not ready). -/
@[simp] theorem fwdValApprox_load
    (idex_rsVal wb_data_non_mem : BitVec 32) :
    fwdValApproxPure true idex_rsVal wb_data_non_mem = idex_rsVal := rfl

/-- Non-load in WB: approx-fwd takes the WB-stage non-mem result. -/
@[simp] theorem fwdValApprox_non_load
    (idex_rsVal wb_data_non_mem : BitVec 32) :
    fwdValApproxPure false idex_rsVal wb_data_non_mem = wb_data_non_mem := rfl

theorem fwdValApproxPure_spec :
    ∀ (exwb_m2r : Bool) (idex_rsVal wb_data_non_mem : BitVec 32),
      fwdValApproxPure exwb_m2r idex_rsVal wb_data_non_mem =
        (if exwb_m2r then idex_rsVal else wb_data_non_mem) := by
  intros; rfl

/-! ## Composite specs -/

theorem fwdMatchPure_spec :
    ∀ (wb_en : Bool) (wb_addr rs_idx : BitVec 5),
      fwdMatchPure wb_en wb_addr rs_idx =
        (wb_en && (wb_addr == rs_idx)) := by
  intros; rfl

theorem fwdValuePure_spec :
    ∀ (fwd_match : Bool) (wb_data idex_rsVal : BitVec 32),
      fwdValuePure fwd_match wb_data idex_rsVal =
        (if fwd_match then wb_data else idex_rsVal) := by
  intros; rfl

/-! ## Signal-level wrappers -/

def fwdMatchSignal {dom : DomainConfig}
    (wb_en : Signal dom Bool)
    (wb_addr rs_idx : Signal dom (BitVec 5)) : Signal dom Bool :=
  wb_en &&& (wb_addr === rs_idx)

def fwdValueSignal {dom : DomainConfig}
    (fwd_match : Signal dom Bool)
    (wb_data idex_rsVal : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  Signal.mux fwd_match wb_data idex_rsVal

/-- Approx forwarded value (load-aware) Signal wrapper. -/
def fwdValApproxSignal {dom : DomainConfig}
    (exwb_m2r : Signal dom Bool)
    (idex_rsVal wb_data_non_mem : Signal dom (BitVec 32))
    : Signal dom (BitVec 32) :=
  Signal.mux exwb_m2r idex_rsVal wb_data_non_mem

/-! ## Cycle-wise equivalences -/

private theorem signal_eq_val_bv {dom : DomainConfig} {n : Nat}
    (a b : Signal dom (BitVec n)) (t : Nat) :
    (a === b).val t = (a.val t == b.val t) := by
  show (Signal.ap (Signal.map (· == ·) a) b).val t = _
  rfl

private theorem signal_and_val {dom : DomainConfig}
    (a b : Signal dom Bool) (t : Nat) :
    (a &&& b).val t = (a.val t && b.val t) := by
  show (Signal.ap (Signal.map (· && ·) a) b).val t = _
  rfl

theorem fwdMatchSignal_eq_pure {dom : DomainConfig}
    (wb_en : Signal dom Bool) (wb_addr rs_idx : Signal dom (BitVec 5))
    (t : Nat) :
    (fwdMatchSignal wb_en wb_addr rs_idx).val t =
      fwdMatchPure (wb_en.val t) (wb_addr.val t) (rs_idx.val t) := by
  unfold fwdMatchSignal fwdMatchPure
  simp [signal_and_val, signal_eq_val_bv]

theorem fwdValueSignal_eq_pure {dom : DomainConfig}
    (fwd_match : Signal dom Bool)
    (wb_data idex_rsVal : Signal dom (BitVec 32)) (t : Nat) :
    (fwdValueSignal fwd_match wb_data idex_rsVal).val t =
      fwdValuePure (fwd_match.val t) (wb_data.val t) (idex_rsVal.val t) := by
  unfold fwdValueSignal fwdValuePure
  show (Signal.mux _ _ _).val t = _
  unfold Signal.mux
  cases h : fwd_match.val t <;> simp [h]

end Sparkle.IP.RV32.Pipeline
