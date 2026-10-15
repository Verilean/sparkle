import Tools.ShippingReaderFuelDefs

/-! # The fuel candidate: stability, monotonicity, agreement with every solution

WRITTEN, NOT BUILT (worker A, branch `par/r-3`). No `sorry`, no axiom, no
`native_decide`.

Generic over ANY body `Φ : (c : κ) → FM κ R (R c)` (`FM` carries its own
monotonicity, `Tools/ShippingReaderFuelDefs.lean`), then instantiated at the
machine reader block (`step senv`) and at `machNorm` (`normStep senv`):

1. **stability** `fuel_stable` — `fuel Φ n c = some r → n ≤ m → fuel Φ m c = some r`;
2. **monotonicity** `fuel_mono` — `n ≤ m → HLe (fuel Φ n) (fuel Φ m)`;
   **fuel independence** `fuel_det` — two non-OUT answers are equal;
3. **agreement** `fuel_agree` — for EVERY `g` solving the body's equation
   (`IsSol Φ g`: `Φ` run against the total table `some ∘ g` returns `g`),
   `fuel Φ n c = some r → g c = r`. For the block `r : Option c.Res`, so this
   is agreement on the old `some r` AND on the old `none` (refusal).

`IsSol` is the source equation in the body's own form. That every solution
of the VERBATIM source text is an `IsSol` is
`Tools/ShippingReaderFuelOldEq.lean` (per arm). -/
namespace Tools.ShippingReaderFuel
open Lean
open Sparkle.Compiler.Elab

section Generic
variable {κ : Type} {R : κ → Type}

theorem fuel_zero (Φ : (c : κ) → FM κ R (R c)) (c : κ) : fuel Φ 0 c = none := rfl

theorem fuel_succ (Φ : (c : κ) → FM κ R (R c)) (n : Nat) (c : κ) :
    fuel Φ (n + 1) c = (Φ c).run (fuel Φ n) := rfl

theorem fuel_le_succ (Φ : (c : κ) → FM κ R (R c)) : ∀ n, HLe (fuel Φ n) (fuel Φ (n + 1))
  | 0 => fun c r h => by
    rw [fuel_zero] at h
    cases h
  | n + 1 => fun c r h => by
    rw [fuel_succ] at h ⊢
    exact (Φ c).mono _ _ (fuel_le_succ Φ n) r h

/-- **Monotonicity in the fuel.** -/
theorem fuel_mono (Φ : (c : κ) → FM κ R (R c)) {n m : Nat} (hnm : n ≤ m) :
    HLe (fuel Φ n) (fuel Φ m) := by
  induction hnm with
  | refl => exact fun _ _ h => h
  | step _ ih => exact fun c r h => fuel_le_succ Φ _ c r (ih c r h)

/-- **Stability of a successful (non-OUT) answer across fuel.** -/
theorem fuel_stable (Φ : (c : κ) → FM κ R (R c)) {n m : Nat} {c : κ} {r : R c}
    (h : fuel Φ n c = some r) (hnm : n ≤ m) : fuel Φ m c = some r :=
  fuel_mono Φ hnm c r h

/-- **Fuel independence**: two non-OUT answers are the same answer (the
certificate of an answer is the fuel number alone). -/
theorem fuel_det (Φ : (c : κ) → FM κ R (R c)) {n m : Nat} {c : κ} {r r' : R c}
    (h : fuel Φ n c = some r) (h' : fuel Φ m c = some r') : r = r' := by
  rcases Nat.le_total n m with hnm | hmn
  · have h2 := fuel_mono Φ hnm c r h
    rw [h'] at h2
    exact (Option.some.inj h2).symm
  · have h2 := fuel_mono Φ hmn c r' h'
    rw [h] at h2
    exact Option.some.inj h2

/-- `g` solves the body's equation: the body run against the total table of
`g` answers `g`. -/
def IsSol (Φ : (c : κ) → FM κ R (R c)) (g : (c : κ) → R c) : Prop :=
  ∀ c, (Φ c).run (fun c => some (g c)) = some (g c)

theorem fuel_le_sol (Φ : (c : κ) → FM κ R (R c)) (g : (c : κ) → R c) (hg : IsSol Φ g) :
    ∀ n, HLe (fuel Φ n) (fun c => some (g c))
  | 0 => fun c r h => by
    rw [fuel_zero] at h
    cases h
  | n + 1 => fun c r h => by
    rw [fuel_succ] at h
    have h1 := (Φ c).mono _ _ (fuel_le_sol Φ g hg n) r h
    rw [hg c] at h1
    exact h1

/-- **Agreement**: a non-OUT answer at any fuel is the value of every
solution of the body's equation. -/
theorem fuel_agree (Φ : (c : κ) → FM κ R (R c)) (g : (c : κ) → R c) (hg : IsSol Φ g)
    {n : Nat} {c : κ} {r : R c} (h : fuel Φ n c = some r) : g c = r :=
  Option.some.inj (fuel_le_sol Φ g hg n c r h)

/-- Two solutions agree wherever some fuel answers. -/
theorem sol_agree (Φ : (c : κ) → FM κ R (R c)) (g g' : (c : κ) → R c) (hg : IsSol Φ g)
    (hg' : IsSol Φ g') {n : Nat} {c : κ} {r : R c} (h : fuel Φ n c = some r) : g c = g' c :=
  (fuel_agree Φ g hg h).trans (fuel_agree Φ g' hg' h).symm

end Generic

/-! ## The block -/

theorem readF_stable (senv : StructEnv) {n m : Nat} {c : Call} {r : RB c}
    (h : readF senv n c = some r) (hnm : n ≤ m) : readF senv m c = some r :=
  fuel_stable (step senv) h hnm

theorem readF_mono (senv : StructEnv) {n m : Nat} (hnm : n ≤ m) :
    HLe (readF senv n) (readF senv m) :=
  fuel_mono (step senv) hnm

theorem readF_det (senv : StructEnv) {n m : Nat} {c : Call} {r r' : RB c}
    (h : readF senv n c = some r) (h' : readF senv m c = some r') : r = r' :=
  fuel_det (step senv) h h'

/-- **Agreement of the block** with every solution `g` of its equation: on
the old `some r` and on the old `none` alike. -/
theorem readF_agree (senv : StructEnv) (g : (c : Call) → RB c) (hg : IsSol (step senv) g)
    {n : Nat} {c : Call} {r : RB c} (h : readF senv n c = some r) : g c = r :=
  fuel_agree (step senv) g hg h

theorem machConvF_stable {n m : Nat} {senv : StructEnv} {env : List MachVal} {d : Nat}
    {e : Lean.Expr} {st : MachRead} {r : Option (Lean.Expr × MachRead)}
    (h : machConvF n senv env d e st = some r) (hnm : n ≤ m) :
    machConvF m senv env d e st = some r :=
  readF_stable senv h hnm

theorem machChainF_stable {n m : Nat} {senv : StructEnv} {env : List MachVal}
    {e : Lean.Expr} {st : MachRead} {r : Option (List (Nat × Lean.Expr) × Lean.Expr × MachRead)}
    (h : machChainF n senv env e st = some r) (hnm : n ≤ m) :
    machChainF m senv env e st = some r :=
  readF_stable senv h hnm

theorem machLoopRootF_stable {n m : Nat} {senv : StructEnv} {env : List MachVal}
    {e : Lean.Expr} {st : MachRead} {r : Option (MachVal × MachRead)}
    (h : machLoopRootF n senv env e st = some r) (hnm : n ≤ m) :
    machLoopRootF m senv env e st = some r :=
  readF_stable senv h hnm

/-! ## `machNorm` -/

theorem machNormF_stable {n m : Nat} {senv : StructEnv} {e r : Lean.Expr}
    (h : machNormF n senv e = some r) (hnm : n ≤ m) : machNormF m senv e = some r :=
  fuel_stable (normStep senv) h hnm

theorem machNormF_det {n m : Nat} {senv : StructEnv} {e r r' : Lean.Expr}
    (h : machNormF n senv e = some r) (h' : machNormF m senv e = some r') : r = r' :=
  fuel_det (normStep senv) h h'

theorem machNormF_agree (senv : StructEnv) (g : Lean.Expr → Lean.Expr)
    (hg : IsSol (normStep senv) g) {n : Nat} {e r : Lean.Expr}
    (h : machNormF n senv e = some r) : g e = r :=
  fuel_agree (normStep senv) g hg h

end Tools.ShippingReaderFuel
