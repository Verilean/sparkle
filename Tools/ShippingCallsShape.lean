import Tools.ShippingRankRun
import Tools.ShippingMachineClosesData

/-! # The shape condition of the one-output calls' rank (S3), decided on data

`transition_fields` / `rank_of_facts` ask that the fields of the packed body
use the tail binders (the calls' outputs, the slots, the `let`s) as `okRule`
allows: a call's output only once the call's argument `let`s are passed, a
`let` only if earlier. Here: the Bool check on a `MachineData` and its
soundness. That the shape READER always produces data passing it is NOT
proved (it is evaluated per declaration). -/
namespace Tools.ShippingCallsShape
open Sparkle.Compiler.Elab
open Tools.ShippingUnifiedSource Tools.ShippingMachineRef Tools.ShippingMachineAuto
open Tools.ShippingUnifiedSpine Tools.ShippingSpineOrder Tools.ShippingMachineCloses
open Tools.ShippingMachineClosesData Tools.ShippingRankRun Tools.ShippingMachineEntry

/-- The bound of a call's argument `let`s: one more than the largest. -/
def argBound (args : List Nat) : Nat := args.foldl (fun m a => max m (a + 1)) 0

theorem argBound_spec : ∀ (args : List Nat) (m0 : Nat) (a : Nat), a ∈ args →
    a < args.foldl (fun m a => max m (a + 1)) m0
  | b :: rest, m0, a, h => by
    have ge : ∀ (l : List Nat) (x : Nat), x ≤ l.foldl (fun m a => max m (a + 1)) x := by
      intro l
      induction l with
      | nil => exact fun _ => Nat.le_refl _
      | cons c l ih => exact fun x => Nat.le_trans (Nat.le_max_left x (c + 1)) (ih _)
    rcases List.mem_cons.mp h with e | h
    · subst e
      have := ge rest (max m0 (a + 1))
      have h2 : a + 1 ≤ max m0 (a + 1) := Nat.le_max_right _ _
      simp only [List.foldl_cons]
      omega
    · exact argBound_spec rest _ a h

def okRuleB (kI n : Nat) (cs : List Nat) (i idx : Nat) : Bool :=
  (!decide (idx < kI) || (match cs[idx]? with
    | some c => decide (c ≤ i)
    | none => false)) &&
  (!decide (kI + n ≤ idx) || decide (idx - (kI + n) < i))

theorem okRule_of_B {kI n : Nat} {cs : List Nat} {i idx : Nat} (h : okRuleB kI n cs i idx = true) :
    okRule kI n cs i idx := by
  simp only [okRuleB, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    decide_eq_true_eq] at h
  refine ⟨fun hlt => ?_, fun hge => ?_⟩
  · rcases h.1 with h1 | h1
    · exact absurd hlt h1
    · cases hc : cs[idx]? with
      | none => rw [hc] at h1; cases h1
      | some c =>
        rw [hc] at h1
        exact ⟨c, rfl, by simpa using h1⟩
  · rcases h.2 with h2 | h2
    · exact absurd hge h2
    · exact h2

/-- A binder position field `i` may read: before the tail, or as the rule
allows. -/
def posOk (nA kI n : Nat) (cs : List Nat) (i pos : Nat) : Bool :=
  decide (pos < nA) || okRuleB kI n cs i (pos - nA)

def fieldsOkB (bpos vpos : Nat → Nat) (nA kI n : Nat) (cs : List Nat) :
    Nat → List (Σ w : Nat, Term (.bits w)) → Bool
  | _, [] => true
  | i, f :: rest =>
    reads (fun j => posOk nA kI n cs i (bpos j)) (fun j => posOk nA kI n cs i (vpos j)) f.2 &&
      fieldsOkB bpos vpos nA kI n cs (i + 1) rest

theorem posOk_rule {nA kI n : Nat} {cs : List Nat} {i pos : Nat}
    (h : posOk nA kI n cs i pos = true) : ∀ idx, pos = nA + idx → okRule kI n cs i idx := by
  intro idx e
  subst e
  simp only [posOk, Bool.or_eq_true, decide_eq_true_eq, Nat.add_sub_cancel_left] at h
  rcases h with h | h
  · omega
  · exact okRule_of_B h

/-- **The check is the scope `transition_fields` asks.** -/
theorem fieldsOK_of_B {bpos vpos : Nat → Nat} {kb kv : Nat} {vw : Nat → Nat} {nA kI n : Nat}
    {cs : List Nat} :
    ∀ (fs : List (Σ w : Nat, Term (.bits w))) (i : Nat) {c : Nat} (core : Term (.bits c)),
      fieldsOkB bpos vpos nA kI n cs i fs = true → (packLets fs core).2.WF kb kv vw →
      FieldsOK (fun k q => q < kb ∧ ∀ idx, bpos q = nA + idx → okRule kI n cs k idx)
        (fun k q => q < kv ∧ ∀ idx, vpos q = nA + idx → okRule kI n cs k idx) kb kv vw i fs
  | [], _, _, _, _, _ => trivial
  | f :: fs, i, _, core, h, hw => by
    simp only [fieldsOkB, Bool.and_eq_true] at h
    exact ⟨hw.1,
      uses_of_reads (fun j hj hr => ⟨hj, posOk_rule hr⟩) (fun j hj hr => ⟨hj, posOk_rule hr⟩)
        f.2 hw.1 h.1,
      fieldsOK_of_B fs (i + 1) core h.2 hw.2⟩

end Tools.ShippingCallsShape

namespace Tools.ShippingMachineAuto.MachineData
open Tools.ShippingCallsShape

/-- The calls' bounds. -/
def callBounds (d : MachineData) : List Nat := d.shape.insts.map fun c => argBound c.2.1

/-- **S3 on a machine's data** (one-output calls): `nDecl` declaration
binders, then the calls' outputs, the slots, the `let`s; every field and the
core use them as `okRule` allows, and every call's arguments are `let`s. -/
def callsOk (d : MachineData) (nDecl : Nat) : Bool :=
  decide (nDecl + d.shape.insts.length = d.nIn) &&
  d.shape.insts.all (fun c => c.2.1.all fun a => decide (a < d.ls.length)) &&
  fieldsOkB d.bpos d.vpos nDecl d.shape.insts.length d.ss.length d.callBounds 0 d.letFields &&
  Tools.ShippingMachineRef.reads
    (fun j => posOk nDecl d.shape.insts.length d.ss.length d.callBounds d.ls.length (d.bpos j))
    (fun j => posOk nDecl d.shape.insts.length d.ss.length d.callBounds d.ls.length (d.vpos j))
    d.core.2

end Tools.ShippingMachineAuto.MachineData
