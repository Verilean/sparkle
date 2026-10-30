# M4 parametric: Layer A (pure model of the success condition) — freeze, complete types

Issue `sparkle-gen4-parametric-supply`, branch `kjob/g4par-r8`, base 441dd15f. Docs only; no Lean of Layer A exists yet.
Words: "this survey did not find X" = the cited sources were read and X was not there; never "impossible". A "mutant" in the Check is a rejection by signature/defeq, not a semantic counterexample.

## 0. What Layer A is, and is not
Layer A is a statement about a TOTAL MODEL `evalM` that is copied from the text of `DimExpr.evaluate` (Sparkle/IR/Type.lean:68-93). It is **not** a statement about `DimExpr.evaluate` / `specializeType` / `specializeExpr` / `specializeDesign` (those are `partial` or call partial functions; Layer B, freeze §13.2 / F5, is not supplied). It therefore does **not** count as a production I5b supply, does not discharge T, and adds no law, no TRUSTED boundary, no production edit. The only claim it supports: "for the class PosDim, the MODEL evaluates to a value ≥ 1 for every binding whose values are ≥ 1 and which binds every parameter of the expression", plus the slice-order fact for `SliceOK`, plus (separately) that the model fails at one concrete binding for `n - 1` (a fact about the model).

## 1. New file (new Lean only in new files; lakefile gets `lean_lib` entries only)
`Tools/ShippingGen4ParamLayerA.lean` (imports `Sparkle.IR.Type` only), check `Tests/Gen4/ParamLayerACheck.lean`.

## 2. Complete types (namespace `Tools.ShippingGen4ParamLayerA`, `open Sparkle.IR.Type`)
```lean
def clog2M (v : Nat) : Nat := if v == 1 then 0 else Nat.log2 (v - 1) + 1      -- used only when v ≠ 0
def evalM (θ : List (String × Nat)) : DimExpr → Except String Nat             -- structural on DimExpr
  | .literal v => .ok v
  | .parameter n => match θ.lookup n with | some v => .ok v | none => .error "missing"
  | .add a b => (· + ·) <$> evalM θ a <*> evalM θ b                           -- written with bind, same shape as `evaluate`
  | .sub a b => …  (error if lhs < rhs) | .mul … | .div … (error if rhs = 0) | .mod … (error if rhs = 0)
  | .pow … | .clog2 v (error if v = 0) | .min … | .max …
def Bound (θ : List (String × Nat)) (e : DimExpr) : Prop          -- every .parameter n in e has θ.lookup n ≠ none
def AllPos (θ : List (String × Nat)) : Prop := ∀ p ∈ θ, 0 < p.2
def PosDim : DimExpr → Prop                                      -- exactly §13.3
def NonNegDim (e : DimExpr) : Prop := e = .literal 0 ∨ PosDim e
def SliceOK (hi lo : DimExpr) : Prop                              -- exactly §13.3

theorem evalM_pos {θ e} (hp : PosDim e) (hb : Bound θ e) (ha : AllPos θ) : ∃ v, evalM θ e = .ok v ∧ 0 < v
theorem evalM_nonneg {θ e} (hp : NonNegDim e) (hb : Bound θ e) (ha : AllPos θ) : ∃ v, evalM θ e = .ok v
theorem sliceOK_order {θ hi lo} (h : SliceOK hi lo) (hb : Bound θ hi ∧ Bound θ lo) (ha : AllPos θ) :
    ∃ h' l', evalM θ hi = .ok h' ∧ evalM θ lo = .ok l' ∧ l' ≤ h'
theorem evalM_sub_one_at_one : evalM [("n", 1)] (.sub (.parameter "n") (.literal 1)) = .ok 0     -- n-1 at n=1 EVALUATES to 0 (model)
```
(`evalM_sub_one_at_one`: the MODEL returns `.ok 0` for `n - 1` at `n = 1`; it does not throw. The failure in the production path comes from `requirePositive` in `specializeType` (Specialize.lean:51), which Layer A does not model. Types and expressions are Layer B territory; no `specializeType` model is planned.)
`mkSub` normalisation: `SliceOK` is stated on the un-normalised pair `(s + l) - 1`, `s`, as in §13.3; no lemma about `mkAdd/mkSub/mkMul` smart constructors is claimed.

## 3. Check (`Tests/Gen4/ParamLayerACheck.lean`)
TYPE (isDefEq to an independent copy of each statement written in the Check), MUTANT (≥ 1 well-typed one-point mutant per theorem, e.g. `0 < v` → `0 ≤ v` is not defeq: rejected by the same comparator; this is signature rejection, not a semantic counterexample), AXIOMS (propext/choice/Quot only), CLOSURE (explicit `thmInfo.value`/`defnInfo.value`, no `Laws`/`T1Hyp`/`T1HypND`; opaque untracked, logged) with proof-only negative and clean controls through the same detector, reusing the detector of `ParamIfaceCheck`.

## 4. Open and unchanged
T, Layer B, F1-F6, source/clock/PostTransfer/FG connection: OPEN. Issue not complete.
