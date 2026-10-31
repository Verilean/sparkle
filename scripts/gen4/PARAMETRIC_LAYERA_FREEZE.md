# M4 parametric: Layer A (pure model of the success condition) — freeze, complete types

Issue `sparkle-gen4-parametric-supply`, branch `kjob/g4par-r9`, base ada16f86 (revision 2: R1 of the ada16f86 review — complete `evalM`/`Bound`, one `SliceOK`, the `n - 1` model fact synchronised). Docs only; no Lean of Layer A exists yet.
Words: "this survey did not find X" = the cited sources were read and X was not there; never "impossible". A "mutant" in the Check is a rejection by signature/defeq, not a semantic counterexample.

## 0. What Layer A is, and is not
Layer A is a statement about a TOTAL MODEL `evalM` that is copied from the text of `DimExpr.evaluate` (Sparkle/IR/Type.lean:68-93). It is **not** a statement about `DimExpr.evaluate` / `specializeType` / `specializeExpr` / `specializeDesign` (those are `partial` or call partial functions; Layer B, freeze §13.2 / F5, is not supplied). It therefore does **not** count as a production I5b supply, does not discharge T, and adds no law, no TRUSTED boundary, no production edit. The only claim it supports: "for the class PosDim, the MODEL evaluates to a value ≥ 1 for every binding whose values are ≥ 1 and which binds every parameter of the expression", plus the slice-order fact for `SliceOK`, plus (separately) the model fact that `n - 1` at `n = 1` evaluates to `.ok 0` (the model does not fail there; the production failure for a zero width is `requirePositive` in `specializeType`, which Layer A does not model).

## 1. New file (new Lean only in new files; lakefile gets `lean_lib` entries only)
`Tools/ShippingGen4ParamLayerA.lean` (imports `Sparkle.IR.Type` only), check `Tests/Gen4/ParamLayerACheck.lean`.

## 2. Complete types (namespace `Tools.ShippingGen4ParamLayerA`, `open Sparkle.IR.Type`)
```lean
abbrev Binding := List (String × Nat)

def clog2M (v : Nat) : Nat := if v == 1 then 0 else Nat.log2 (v - 1) + 1      -- copy of the arithmetic in `evaluate`; used only when v ≠ 0

-- Total model of DimExpr.evaluate (Type.lean:68-93), clause by clause, same error conditions, structural on DimExpr.
def evalM (θ : Binding) : DimExpr → Except String Nat
  | .literal v => .ok v
  | .parameter n => match θ.lookup n with
      | some v => .ok v
      | none => .error s!"missing specialization binding for parameter '{n}'"
  | .add a b => do let x ← evalM θ a; let y ← evalM θ b; pure (x + y)
  | .sub a b => do let x ← evalM θ a; let y ← evalM θ b
                   if x < y then throw s!"hardware dimension subtraction underflow: {x} - {y}" else pure (x - y)
  | .mul a b => do let x ← evalM θ a; let y ← evalM θ b; pure (x * y)
  | .div a b => do let x ← evalM θ a; let y ← evalM θ b
                   if y == 0 then throw "hardware dimension division by zero" else pure (x / y)
  | .mod a b => do let x ← evalM θ a; let y ← evalM θ b
                   if y == 0 then throw "hardware dimension modulo by zero" else pure (x % y)
  | .pow a b => do let x ← evalM θ a; let y ← evalM θ b; pure (x ^ y)
  | .clog2 a => do let x ← evalM θ a
                   if x == 0 then throw "clog2 is undefined for hardware dimension 0" else pure (clog2M x)
  | .min a b => do let x ← evalM θ a; let y ← evalM θ b; pure (Nat.min x y)
  | .max a b => do let x ← evalM θ a; let y ← evalM θ b; pure (Nat.max x y)

-- every `.parameter n` occurring in e is bound by θ
def Bound (θ : Binding) : DimExpr → Prop
  | .literal _ => True
  | .parameter n => ∃ v, θ.lookup n = some v
  | .add a b | .sub a b | .mul a b | .div a b | .mod a b | .pow a b | .min a b | .max a b => Bound θ a ∧ Bound θ b
  | .clog2 a => Bound θ a

def AllPos (θ : Binding) : Prop := ∀ p ∈ θ, 0 < p.2

def PosDim : DimExpr → Prop
  | .literal c => 0 < c
  | .parameter _ => True
  | .add a b | .mul a b | .pow a b | .min a b | .max a b => PosDim a ∧ PosDim b
  | .sub .. | .div .. | .mod .. | .clog2 _ => False        -- conservative (E1-E3 sources, freeze §11.1)
def NonNegDim (e : DimExpr) : Prop := e = .literal 0 ∨ PosDim e

-- THE ONE SliceOK (identical to freeze §13.3): the pair the translator builds, with the SMART constructors.
def SliceOK (hi lo : DimExpr) : Prop :=
  ∃ s l, lo = s ∧ hi = DimExpr.mkSub (DimExpr.mkAdd s l) (.literal 1) ∧ NonNegDim s ∧ PosDim l

-- Preservation lemmas for the smart constructors (needed because SliceOK uses them).
theorem evalM_mkAdd (θ) (a b) : evalM θ (DimExpr.mkAdd a b) = evalM θ (.add a b)
theorem evalM_mkSub_of_le {θ a b x y} (ha : evalM θ a = .ok x) (hb : evalM θ b = .ok y) (h : y ≤ x) :
    evalM θ (DimExpr.mkSub a b) = .ok (x - y)

theorem evalM_pos {θ e} (hp : PosDim e) (hb : Bound θ e) (ha : AllPos θ) : ∃ v, evalM θ e = .ok v ∧ 0 < v
theorem evalM_nonneg {θ e} (hp : NonNegDim e) (hb : Bound θ e) (ha : AllPos θ) : ∃ v, evalM θ e = .ok v
theorem sliceOK_order {θ hi lo} (h : SliceOK hi lo) (hb : Bound θ hi ∧ Bound θ lo) (ha : AllPos θ) :
    ∃ h' l', evalM θ hi = .ok h' ∧ evalM θ lo = .ok l' ∧ l' ≤ h'
theorem evalM_sub_one_at_one : evalM [("n", 1)] (.sub (.parameter "n") (.literal 1)) = .ok 0   -- the MODEL gives .ok 0
```
Decisions fixed by this revision:
1. `SliceOK` is the smart-constructor version (the shape the translator emits, Elab:856-859); the earlier un-normalised wording at the end of the previous revision is withdrawn. Because `hi` is then `mkSub (mkAdd s l) 1`, the two preservation lemmas above are part of the freeze: `evalM_mkAdd` holds unconditionally (each `mkAdd` clause only drops a literal `0` operand or folds two literals); `evalM_mkSub_of_le` needs `y ≤ x` because `mkSub` on two literals truncates (`.literal (a - b)`) whereas `evalM (.sub ..)` errors on underflow — so equality is claimed only under `y ≤ x`, which `sliceOK_order` discharges from `PosDim l` (`x = s + l ≥ 1 = y`).
2. `Bound` only asks for parameter lookup success; it does not ask for declared-ness (freeze §13.3 premise 1 stays separate and unsupplied).
3. `evalM` has no `partial`; each clause recurses on a structural subterm. The match arms are the clauses of `evaluate` in the same order; only the `do`-notation of the original (`return (← evaluate ..) + (← evaluate ..)`) is expanded to explicit binds, left operand first.
4. `evalM_sub_one_at_one` is a statement about `evalM`. It is **not** a statement that `specializeType` accepts or rejects `n - 1` at `n = 1`, and not a counterexample to anything in production.

## 3. Check (`Tests/Gen4/ParamLayerACheck.lean`)
TYPE (isDefEq to an independent copy of each statement written in the Check), MUTANT (≥ 1 well-typed one-point mutant per theorem, e.g. `0 < v` → `0 ≤ v` is not defeq: rejected by the same comparator; this is signature rejection, not a semantic counterexample), AXIOMS (propext/choice/Quot only), CLOSURE (explicit `thmInfo.value`/`defnInfo.value`, no `Laws`/`T1Hyp`/`T1HypND`; opaque untracked, logged) with proof-only negative and clean controls through the same detector, reusing the detector of `ParamIfaceCheck`.

## 4. Open and unchanged
T, Layer B, F1-F6, source/clock/PostTransfer/FG connection: OPEN. Issue not complete.
