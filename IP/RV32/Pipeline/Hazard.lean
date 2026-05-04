/-
  RV32 load-use hazard — pure predicate + invariants

  The Signal-level `hazardSignal` is in `IP/RV32/Core.lean`. This
  file adds the *pure* form, proves the per-case spec with `decide`
  / `bv_decide`, and proves the cycle-wise equivalence.

  Spec (no forwarding; load-use stalls):

      hazard = exMemRead ∧ (exRd ≠ 0) ∧ (exRd = idRs1 ∨ exRd = idRs2)

  Stalling on rd=x0 is wrong because x0 always reads as 0; we don't
  need to wait for the load. The rd=x0 carve-out is encoded by the
  `rdNonZero` clause.

  This is the only "stall" source besides MMU PTW; together with
  branch flush, mret/sret flush, and AMO writeback freeze, it
  determines when the IDEX register holds vs advances.
-/

import Sparkle
import Sparkle.Compiler.Elab
import IP.RV32.Core

namespace Sparkle.IP.RV32.Pipeline

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ## Pure hazard predicate -/

/-- Load-use hazard predicate.

    Stalls iff:
      - The EX-stage instruction is a load (`exMemRead`).
      - Its destination register is not x0.
      - That register matches one of ID's source registers.
-/
@[inline] def hazardPure
    (exMemRead : Bool) (exRd idRs1 idRs2 : BitVec 5) : Bool :=
  let rdNonZero := !(exRd == 0#5)
  let rs1Match := exRd == idRs1
  let rs2Match := exRd == idRs2
  exMemRead && rdNonZero && (rs1Match || rs2Match)

/-! ## Spec invariants — closed by `decide` / `bv_decide` -/

/-- A non-load EX never stalls. -/
@[simp] theorem hazard_no_load
    (exRd idRs1 idRs2 : BitVec 5) :
    hazardPure false exRd idRs1 idRs2 = false := by
  unfold hazardPure
  rfl

/-- Load with `exRd = x0` never stalls (x0 always reads 0). -/
@[simp] theorem hazard_x0_no_stall
    (idRs1 idRs2 : BitVec 5) :
    hazardPure true 0#5 idRs1 idRs2 = false := by
  unfold hazardPure
  bv_decide

/-- Load with no register match never stalls. -/
theorem hazard_no_match
    (exRd idRs1 idRs2 : BitVec 5)
    (h1 : (exRd == idRs1) = false)
    (h2 : (exRd == idRs2) = false) :
    hazardPure true exRd idRs1 idRs2 = false := by
  unfold hazardPure
  simp [h1, h2]

/-- Load with rs1 match (and exRd≠0) stalls. -/
theorem hazard_rs1_match
    (exRd idRs1 idRs2 : BitVec 5)
    (hnz : (exRd == 0#5) = false)
    (hm : exRd == idRs1) :
    hazardPure true exRd idRs1 idRs2 = true := by
  unfold hazardPure
  simp [hnz, hm]

/-- Load with rs2 match (and exRd≠0) stalls. -/
theorem hazard_rs2_match
    (exRd idRs1 idRs2 : BitVec 5)
    (hnz : (exRd == 0#5) = false)
    (hm : exRd == idRs2) :
    hazardPure true exRd idRs1 idRs2 = true := by
  unfold hazardPure
  simp [hnz, hm]

/-! ## Composite spec -/

theorem hazardPure_spec :
    ∀ (exMemRead : Bool) (exRd idRs1 idRs2 : BitVec 5),
      hazardPure exMemRead exRd idRs1 idRs2 =
        (exMemRead && !(exRd == 0#5) && ((exRd == idRs1) || (exRd == idRs2))) := by
  intros; rfl

/-! ## Cycle-wise equivalence with `Sparkle.IP.RV32.hazardSignal` -/

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

private theorem signal_or_val {dom : DomainConfig}
    (a b : Signal dom Bool) (t : Nat) :
    (a ||| b).val t = (a.val t || b.val t) := by
  show (Signal.ap (Signal.map (· || ·) a) b).val t = _
  rfl

private theorem signal_not_val {dom : DomainConfig}
    (a : Signal dom Bool) (t : Nat) :
    (~~~a).val t = !(a.val t) := by
  show (Signal.map (fun x => !x) a).val t = _
  rfl

private theorem signal_pure_val {dom : DomainConfig} {α : Type}
    (x : α) (t : Nat) : (Signal.pure (dom := dom) x).val t = x := rfl

/-- `hazardSignal = hazardPure` cycle-by-cycle. -/
theorem hazardSignal_eq_pure {dom : DomainConfig}
    (exMemRead : Signal dom Bool) (exRd idRs1 idRs2 : Signal dom (BitVec 5))
    (t : Nat) :
    (Sparkle.IP.RV32.hazardSignal exMemRead exRd idRs1 idRs2).val t =
      hazardPure (exMemRead.val t) (exRd.val t)
        (idRs1.val t) (idRs2.val t) := by
  unfold Sparkle.IP.RV32.hazardSignal hazardPure
  simp [signal_eq_val_bv, signal_and_val, signal_or_val, signal_not_val,
        signal_pure_val, Bool.and_assoc]

end Sparkle.IP.RV32.Pipeline
