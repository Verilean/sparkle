import Tools.ShippingEntrySoundness

/-! # `splitReturnLeaves` on a scalar Signal result: one leaf, `("out", e)`

`splitReturnLeaves e` (`Sparkle/Compiler/Elab.lean`) is
`fuelFixM2 splitReturnLeavesStep helperFuelLimit e none`. On a result that is
not a lambda and whose type's weak head normal form is headed by the constant
`Sparkle.Core.Signal.Signal`, the step returns the single leaf
`(none.getD "out", e)` WITHOUT reducing `e` (`needsReduce` is false for a
Signal head) and without recursion.

**Proved here** (`splitReturnLeaves_scalar`): for such an `e`, every
successful run returns `leaves` with `leaves.toList = [("out", e)]`.

**Premises**

| Premise | Statement | Class |
|---|---|---|
| `hlam` | `e.isLambda = false` | closed computation on the leaf (`rfl` for an application) |
| `SignalTyped e` | every successful `inferType e` followed by a successful `whnf` of its result gives a type `tyN` with `tyN.getAppFn = .const ``Signal us` | the RESULT-TYPE ORACLE: reflection of the environment through `inferType` / `whnf` (same class as `hunfE`; quantified over every run, so it speaks of every environment a run may see) |

**Program shapes EXPECTED at each inversion (not observed)** — after
`unfold splitReturnLeavesStep`, with `prefix? = none`:

```
L0  if e.isLambda = true then (lambdaTelescope e … >>= …) else REST
      (or `have __do_jp := fun _ => REST; if … then … else __do_jp ()`)   (ite; `mret_if_neg`)
L1  REST = inferType e >>= fun ty => whnf ty >>= fun tyN => A tyN         (two binds)
L2  A tyN = let needsReduce := (tyN.isAppOf ``Prod && tyN.getAppNumArgs == 2) ||
              (match tyN.getAppFn with | .const n _ => n != ``Signal | _ => false);
            JOIN POINT (`let e ← if needsReduce then whnf e else pure e`):
              have __do_jp := fun e => C e
              if needsReduce = true then whnf e >>= fun r => __do_jp r
              else pure e >>= fun r => __do_jp r                          (alternative A)
            or the plain bind
              (if needsReduce = true then whnf e else pure e) >>= fun e => C e   (alternative B)
            or `… else __do_jp e`                                         (alternative C)
L3  C e = if tyN.isAppOf ``Signal = true then
            (let portName := none.getD "out"; pure #[(portName, e)])
          else …                                                          (ite; `mret_if_pos`)
```

The two Boolean facts about `tyN` (`needsReduce` is false, the Signal test is
true) are proved from `tyN.getAppFn = .const ``Signal us` by unfolding
`Expr.isAppOf`, rewriting the head and evaluating two closed name tests. -/
namespace Tools.ShippingLegacySem
open Lean Meta Sparkle.Compiler.Elab
open Tools.ShippingEntrySoundness

/-! ## Inversions of an `if` in `MetaM` -/

theorem mret_if_pos {α : Type} {c : Prop} [Decidable c] {a b : MetaM α} {r : α}
    (h : MReturns (if c then a else b) r) (hc : c) : MReturns a r := by
  rw [if_pos hc] at h
  exact h

theorem mret_if_neg {α : Type} {c : Prop} [Decidable c] {a b : MetaM α} {r : α}
    (h : MReturns (if c then a else b) r) (hc : ¬ c) : MReturns b r := by
  rw [if_neg hc] at h
  exact h

/-! ## The result-type oracle and the two tests on its result -/

/-- The result-type oracle on `e`: the weak head normal form of its inferred
type is headed by the constant `Signal`. -/
def SignalTyped (e : Lean.Expr) : Prop :=
  ∀ (ty tyN : Lean.Expr), MReturns (inferType e) ty → MReturns (whnf ty) tyN →
    ∃ us : List Level, tyN.getAppFn = .const ``Sparkle.Core.Signal.Signal us

/-- The step's `needsReduce`, as it computes it (the text of
`splitReturnLeavesStep`). -/
def needsReduceOf (tyN : Lean.Expr) : Bool :=
  (tyN.isAppOf ``Prod && tyN.getAppNumArgs == 2) ||
    (match tyN.getAppFn with
      | .const indName _ =>
        indName != ``Sparkle.Core.Signal.Signal
      | _ => false)

/-- A closed test on two name literals, by evaluation. -/
macro "name_test" : tactic => `(tactic| first | decide | decide +kernel | rfl)

theorem signal_ne_prod : ((``Sparkle.Core.Signal.Signal : Name) == ``Prod) = false := by
  name_test

theorem signal_bne_self :
    ((``Sparkle.Core.Signal.Signal : Name) != ``Sparkle.Core.Signal.Signal) = false := by
  name_test

theorem signal_beq_self :
    ((``Sparkle.Core.Signal.Signal : Name) == ``Sparkle.Core.Signal.Signal) = true := by
  name_test

/-- The two tests with the head evaluated: a closed Boolean. -/
theorem needsReduce_closed (k : Nat) :
    ((((``Sparkle.Core.Signal.Signal : Name) == ``Prod) && k == 2) ||
      ((``Sparkle.Core.Signal.Signal : Name) != ``Sparkle.Core.Signal.Signal)) = false := by
  rw [signal_ne_prod, signal_bne_self] <;> rfl

/-- For a Signal-headed type the step does not reduce the result. -/
theorem needsReduceOf_signal {tyN : Lean.Expr} {us : List Level}
    (hfn : tyN.getAppFn = .const ``Sparkle.Core.Signal.Signal us) :
    needsReduceOf tyN = false := by
  unfold needsReduceOf Lean.Expr.isAppOf
  rw [hfn]
  -- (`done` first: `rw` closes a goal it can prove by `rfl`)
  first
    | done
    | exact needsReduce_closed tyN.getAppNumArgs
    | (dsimp only
       exact needsReduce_closed tyN.getAppNumArgs)
    | simp [signal_ne_prod, signal_bne_self]

/-- For a Signal-headed type the step's Signal test succeeds. -/
theorem isAppOf_signal {tyN : Lean.Expr} {us : List Level}
    (hfn : tyN.getAppFn = .const ``Sparkle.Core.Signal.Signal us) :
    tyN.isAppOf ``Sparkle.Core.Signal.Signal = true := by
  unfold Lean.Expr.isAppOf
  rw [hfn]
  first
    | done
    | exact signal_beq_self
    | (dsimp only
       exact signal_beq_self)
    | simp

/-! ## The walk -/

/-- **A scalar Signal result has one leaf, named `out`, carrying the result
itself.** -/
theorem splitReturnLeaves_scalar {e : Lean.Expr} (hlam : e.isLambda = false)
    (hty : SignalTyped e) {leaves : Array (String × Lean.Expr)}
    (h : MReturns (splitReturnLeaves e) leaves) : leaves.toList = [("out", e)] := by
  -- one unfolding of the fuel recursion (the idiom used for
  -- `translateFuelFix translateStep translateFuelLimit`)
  change MReturns (splitReturnLeavesStep
    (fuelFixM2 splitReturnLeavesStep (helperFuelLimit - 1)) e none) leaves at h
  unfold splitReturnLeavesStep at h
  -- L0: not a lambda
  have a1 := mret_if_neg h (fun hc => Bool.false_ne_true (hlam.symm.trans hc))
  -- L1: the result type and its weak head normal form
  obtain ⟨ty, hty1, a2⟩ := MReturns.bind a1
  obtain ⟨tyN, hty2, a3⟩ := MReturns.bind a2
  obtain ⟨us, hfn⟩ := hty ty tyN hty1 hty2
  have hnr : needsReduceOf tyN = false := needsReduceOf_signal hfn
  have hsg : tyN.isAppOf ``Sparkle.Core.Signal.Signal = true := isAppOf_signal hfn
  -- L2 (the result is not reduced) and L3 (the Signal case). Three shapes of
  -- the `let e ← if …` item: join point with `pure e >>= jp` (A), plain bind
  -- (B), join point applied directly (C)
  first
    | (have a4 := mret_if_neg a3 (fun hc => Bool.false_ne_true (hnr.symm.trans hc))
       obtain ⟨e1, he1, a5⟩ := MReturns.bind a4
       have ee : e1 = e := MReturns.pure he1
       rw [ee] at a5
       have a6 := mret_if_pos a5 hsg)
    | (obtain ⟨e1, he1, a5⟩ := MReturns.bind a3
       have ee : e1 = e :=
         MReturns.pure (mret_if_neg he1 (fun hc => Bool.false_ne_true (hnr.symm.trans hc)))
       rw [ee] at a5
       have a6 := mret_if_pos a5 hsg)
    | (have a5 := mret_if_neg a3 (fun hc => Bool.false_ne_true (hnr.symm.trans hc))
       have a6 := mret_if_pos a5 hsg)
  have hl := MReturns.pure a6
  subst hl
  first | rfl | simp [Option.getD]

end Tools.ShippingLegacySem
