import Tools.ShippingReaderFuelEval
import Tools.ShippingLetsReaderInvMain

/-! # Unit LC8 prototype (part 4): the LEAST FIXPOINT of the existing reader body `step senv`

Reviewer route (REVIEW-LC8): do NOT re-copy the seven readers.  Take the existing body
`step senv : (c : Call) → FM Call RB (RB c)` (`Tools/ShippingReaderFuelDefs.lean`), whose monotonicity is
the `FM.mono` field, and form its least fixpoint with Lean's `Lean.Order.fix` (the engine under
`partial_fixpoint`) over the pointwise flat order on `(c : Call) → Option (RB c)`.

* outer `none` = no finite derivation (the bottom); `some none` = refusal; `some (some v)` = success.
* `lfp_iff`        : `lfp c = some r ↔ EvalG Φ c r`   (finite derivation tree; `Compact` bodies only).
* `lfpBlock_iff`   : `lfpBlock senv c = some r ↔ ∃ n, readF senv n c = some r`   (the ACCEPTANCE condition).
* `lfp_unfold`     : the unfolding equation `lfp c = (Φ c).run lfp`.

NOT proved here: any link from the old `partial def`s (opaque in the kernel) to `lfpBlock` — see
`docs/parallel/reader-fixpoint-proposal.md`.  No `sorry`, no axiom, no `native_decide`.
BUILT/UNBUILT: see REPORT-LC8.md (run names). -/
namespace Tools.Prototype.ReaderLfp
open Lean.Order Sparkle.Compiler.Elab Tools.ShippingReaderFuel

section Generic
variable {κ : Type} {R : κ → Type}

/-- The flat order on `Option` is "answers less, but never differently". -/
theorem rel_option {α : Type} (a b : Option α) : a ⊑ b ↔ ∀ r, a = some r → b = some r := by
  constructor
  · intro h r ha
    cases h with
    | bot => cases ha
    | refl => exact ha
  · intro h
    cases a with
    | none => exact FlatOrder.rel.bot
    | some r =>
      have e := h r rfl
      first | (rw [e]; done) | (rw [e]; exact FlatOrder.rel.refl)

/-- One unfolding of the body against a table. -/
def Fn (Φ : (c : κ) → FM κ R (R c)) : ((c : κ) → Option (R c)) → ((c : κ) → Option (R c)) :=
  fun h c => (Φ c).run h

theorem Fn_mono (Φ : (c : κ) → FM κ R (R c)) : monotone (Fn Φ) := by
  intro h₁ h₂ hle c
  rw [rel_option]
  intro r hr
  exact (Φ c).mono h₁ h₂ (fun c' r' hc => (rel_option _ _).mp (hle c') r' hc) r hr

/-- The least fixpoint of the body. -/
noncomputable def lfp (Φ : (c : κ) → FM κ R (R c)) : (c : κ) → Option (R c) :=
  fix (Fn Φ) (Fn_mono Φ)

/-- **Unfolding equation** (what `partial def` does not give in the kernel). -/
theorem lfp_unfold (Φ : (c : κ) → FM κ R (R c)) (c : κ) : lfp Φ c = (Φ c).run (lfp Φ) :=
  congrFun (fix_eq (Fn_mono Φ)) c

/-- A finite derivation is an answer of the least fixpoint (no hypothesis on the body). -/
theorem evalG_lfp {Φ : (c : κ) → FM κ R (R c)} {c : κ} {r : R c} (h : EvalG Φ c r) :
    lfp Φ c = some r := by
  induction h with
  | node L _ hrun ih =>
    rw [lfp_unfold]
    exact hrun (lfp Φ) ih

/-- An answer of the least fixpoint is a finite derivation (for a compact body): fixpoint induction. -/
theorem lfp_evalG {Φ : (c : κ) → FM κ R (R c)} (hΦ : ∀ c, Compact (Φ c))
    {c : κ} {r : R c} (h : lfp Φ c = some r) : EvalG Φ c r := by
  have key : ∀ (c : κ) (r : R c), lfp Φ c = some r → EvalG Φ c r := by
    have := fix_induct (Fn_mono Φ) (fun h => ∀ (c : κ) (r : R c), h c = some r → EvalG Φ c r)
      (admissible_pi_apply _ (fun c => admissible_pi _ (fun r => Option.admissible_eq_some _ r)))
      (fun h ih c r hr => by
        obtain ⟨L, e, k⟩ := (hΦ c).ok h r hr
        exact EvalG.node L (fun p hp => ih p.1 p.2 (e p hp)) k)
    exact this
  exact key c r h

theorem lfp_iff {Φ : (c : κ) → FM κ R (R c)} (hΦ : ∀ c, Compact (Φ c)) {c : κ} {r : R c} :
    lfp Φ c = some r ↔ EvalG Φ c r :=
  ⟨lfp_evalG hΦ, evalG_lfp⟩

theorem lfp_iff_fuel {Φ : (c : κ) → FM κ R (R c)} (hΦ : ∀ c, Compact (Φ c)) {c : κ} {r : R c} :
    lfp Φ c = some r ↔ ∃ n, fuel Φ n c = some r :=
  ⟨fun h => evalG_fuel (lfp_evalG hΦ h), fun ⟨n, h⟩ => evalG_lfp (fuel_evalG hΦ n c r h)⟩

end Generic

/-! ## The reader block -/

/-- The seven readers as ONE least fixpoint, outer `none` = ⊥, `some none` = refusal. -/
noncomputable def lfpBlock (senv : StructEnv) : (c : Call) → Option (RB c) := lfp (step senv)

theorem lfpBlock_unfold (senv : StructEnv) (c : Call) :
    lfpBlock senv c = (step senv c).run (lfpBlock senv) := lfp_unfold _ c

/-- **ACCEPTANCE**: `lfpBlock c = some r ↔ ∃ fuel, readF fuel c = some r`, success and refusal alike. -/
theorem lfpBlock_iff (senv : StructEnv) {c : Call} {r : RB c} :
    lfpBlock senv c = some r ↔ ∃ n, readF senv n c = some r :=
  lfp_iff_fuel (compact_step senv)

theorem lfpBlock_iff_eval (senv : StructEnv) {c : Call} {r : RB c} :
    lfpBlock senv c = some r ↔ Eval senv c r :=
  lfp_iff (compact_step senv)

/-- The seven entry points, read off the one fixpoint. -/
noncomputable def protoLoopBody (senv : StructEnv) (base : Nat) (env : List MachVal) (e : Lean.Expr)
    (st : MachRead) : Option (Option MachRead) := lfpBlock senv (.loopBody base env e st)

theorem protoLoopBody_iff (senv : StructEnv) {base : Nat} {env : List MachVal} {e : Lean.Expr}
    {st : MachRead} {r : Option MachRead} :
    protoLoopBody senv base env e st = some r ↔ ∃ n, machLoopBodyF n senv base env e st = some r :=
  lfpBlock_iff senv

/-- The LC3 joint invariant, transported to the least fixpoint: the premises are exactly those of
`machLoopBodyF_post`; only the conclusion's subject changes from "the fuel twin at fuel n" to the
fixpoint. -/
theorem protoLoopBody_post {senv : StructEnv}
    (hroot : Tools.ShippingLetsReaderInv.RootFloatRange) (hlift : Tools.ShippingLetsReaderInv.LiftRange)
    (hinst1 : Tools.ShippingLetsReaderInv.Inst1Range) (hsig : Tools.ShippingLetsReaderInv.SigTyRange senv)
    (hbundle : Tools.ShippingLetsReaderInv.BundleIotaRange)
    {base : Nat} {env : List MachVal} {e : Lean.Expr} {st st' : MachRead}
    (hst : Tools.ShippingLetsReaderInv.RdOk st)
    (hE : Tools.ShippingLetsReaderInv.EnvOk st.lets.size env)
    (hl : Tools.ShippingLetsReaderInv.LetOk 0 e = true)
    (h : protoLoopBody senv base env e st = some (some st')) :
    Tools.ShippingLetsReaderInv.RdOk st' ∧ st.lets.size ≤ st'.lets.size := by
  obtain ⟨n, hn⟩ := (protoLoopBody_iff senv).mp h
  exact Tools.ShippingLetsReaderInv.machLoopBodyF_post hroot hlift hinst1 hsig hbundle hst hE hl hn

#print axioms lfpBlock_iff
#print axioms lfpBlock_unfold
#print axioms protoLoopBody_post

end Tools.Prototype.ReaderLfp
