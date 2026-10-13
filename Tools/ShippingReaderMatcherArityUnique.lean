import Tools.ShippingReaderMatcherArity

/-! # `prodMatcherArity?.go`: its recursion equation has exactly one solution, the total `goT`

WRITTEN, NOT BUILT (par/h-1). Separate from
`Tools/ShippingReaderMatcherArity.lean` because the proofs here are the
fragile ones (case splits of a `match` with a deep pattern, written blind):
a failure here does not block the definitions, the success theorems or the
shadow comparison.

## Statements

    abbrev GoEq (eqv) (g : Expr → Nat → List Nat → Nat → Option Nat) : Prop :=
      ∀ e subj vars depth, g e subj vars depth = step (leafT eqv) g e subj vars depth

`step (leafT eqv) g` is ONE unfolding of the compiler's `go` with the
recursive call `g`, in structural form (`headT` / `argsT` for `getAppFn` /
`getAppArgs`, a constructor pattern for the array pattern, `listEqv eqv` for
`==`, `List.length` for `Array.size`).

    goT_sol    : GoEq eqv (goT eqv)                                   -- existence
    go_unique  : GoEq eqv g → ∀ e subj vars depth,
                   g e subj vars depth = goT eqv e subj vars depth    -- uniqueness

    goT_some_iff  : goT eqv e subj vars depth = some k ↔
                      ∃ d, walkT e subj vars depth = some d ∧ leafD eqv d = some k
    leafT_some_iff : leafT eqv hIdx args subj vars depth = some k ↔
                      (hIdx != depth) = false ∧
                      listEqv eqv args ((vars ++ [subj]).map Expr.bvar) = true ∧
                      args.length = k

and the two links to the compiler's text that ARE provable:

    listEqv_exprEqv    : listEqv exprEqv l1 l2 = (l1 == l2)
    headT_eq_getAppFn  : headT e = e.getAppFn

(`argsT e = e.getAppArgs.toList` is NOT here: `getAppArgsAux` is `private`
in a `module`; measured by the shadow.)

Uniqueness is by induction on `sizeOf e`: `casesArm` calls its recursive
argument on a strictly smaller term only (`casesArm_congr`).

No `sorry`, no axiom, no `native_decide`. PREDICTED axioms: `propext`,
`Quot.sound`, possibly `Classical.choice` (through `simp` / `split`). -/
namespace Tools.ShippingReaderMatcherArity
open Lean

/-! ## The result, characterised -/

theorem goT_some_iff (eqv : Expr → Expr → Bool) (e : Expr) (subj : Nat) (vars : List Nat)
    (depth k : Nat) :
    goT eqv e subj vars depth = some k ↔
      ∃ d, walkT e subj vars depth = some d ∧ leafD eqv d = some k := by
  first
    | exact Option.bind_eq_some_iff
    | (unfold goT; exact Option.bind_eq_some_iff)
    | (unfold goT
       cases walkT e subj vars depth with
       | none => simp
       | some d => simp)

theorem leafT_some_iff (eqv : Expr → Expr → Bool) (hIdx : Nat) (args : List Expr) (subj : Nat)
    (vars : List Nat) (depth k : Nat) :
    leafT eqv hIdx args subj vars depth = some k ↔
      (hIdx != depth) = false ∧
        listEqv eqv args ((vars ++ [subj]).map Expr.bvar) = true ∧ args.length = k := by
  unfold leafT
  cases hb : (hIdx != depth) <;>
    cases hl : listEqv eqv args ((vars ++ [subj]).map Expr.bvar) <;>
      simp

/-! ## The recursive call is on a smaller term -/

/-- `casesArm` uses its recursive argument on strictly smaller terms only. -/
theorem casesArm_congr {ρ : Type} (r1 r2 : Expr → Nat → List Nat → Nat → Option ρ) (e : Expr)
    (subj : Nat) (vars : List Nat) (depth : Nat)
    (h : ∀ e', sizeOf e' < sizeOf e → ∀ s v d, r1 e' s v d = r2 e' s v d) :
    casesArm r1 e subj vars depth = casesArm r2 e subj vars depth := by
  unfold casesArm
  repeat' split
  all_goals first
    | rfl
    | (apply h; simp only [Lean.Expr.app.sizeOf_spec, Lean.Expr.lam.sizeOf_spec]; omega)
    | (apply h; simp; omega)
    | (apply h; simp +arith)
    | (apply h; decreasing_tactic)
    | contradiction
    | (exfalso; simp_all)

/-- A bind after `casesArm` is `casesArm` over the bound recursive call. -/
theorem casesArm_bind {ρ σ : Type} (r : Expr → Nat → List Nat → Nat → Option ρ)
    (f : ρ → Option σ) (e : Expr) (subj : Nat) (vars : List Nat) (depth : Nat) :
    (casesArm r e subj vars depth).bind f =
      casesArm (fun e s v d => (r e s v d).bind f) e subj vars depth := by
  unfold casesArm
  repeat' split
  all_goals first
    | rfl
    | contradiction
    | (exfalso; simp_all)
    | simp_all

theorem step_congr {ρ : Type} (leaf : Nat → List Expr → Nat → List Nat → Nat → Option ρ)
    (r1 r2 : Expr → Nat → List Nat → Nat → Option ρ) (e : Expr)
    (subj : Nat) (vars : List Nat) (depth : Nat)
    (h : ∀ e', sizeOf e' < sizeOf e → ∀ s v d, r1 e' s v d = r2 e' s v d) :
    step leaf r1 e subj vars depth = step leaf r2 e subj vars depth := by
  unfold step
  generalize headT e = hd
  cases hd <;> first
    | rfl
    | exact casesArm_congr r1 r2 e subj vars depth h

theorem step_bind {ρ σ : Type} (leaf1 : Nat → List Expr → Nat → List Nat → Nat → Option ρ)
    (leaf2 : Nat → List Expr → Nat → List Nat → Nat → Option σ) (f : ρ → Option σ)
    (hleaf : ∀ h a s v d, (leaf1 h a s v d).bind f = leaf2 h a s v d)
    (r : Expr → Nat → List Nat → Nat → Option ρ) (e : Expr) (subj : Nat) (vars : List Nat)
    (depth : Nat) :
    (step leaf1 r e subj vars depth).bind f =
      step leaf2 (fun e s v d => (r e s v d).bind f) e subj vars depth := by
  unfold step
  generalize headT e = hd
  cases hd <;> first
    | exact hleaf _ _ _ _ _
    | exact casesArm_bind r f e subj vars depth

/-! ## Existence and uniqueness -/

/-- Two solutions of the recursion equation are equal. -/
theorem step_unique {ρ : Type} (leaf : Nat → List Expr → Nat → List Nat → Nat → Option ρ)
    (w1 w2 : Expr → Nat → List Nat → Nat → Option ρ)
    (h1 : ∀ e s v d, w1 e s v d = step leaf w1 e s v d)
    (h2 : ∀ e s v d, w2 e s v d = step leaf w2 e s v d) :
    ∀ e s v d, w1 e s v d = w2 e s v d := by
  have key : ∀ (n : Nat) (e : Expr), sizeOf e ≤ n → ∀ s v d, w1 e s v d = w2 e s v d := by
    intro n
    induction n with
    | zero =>
      intro e hn s v d
      exact (h1 e s v d).trans
        ((step_congr leaf w1 w2 e s v d (fun e' hlt => absurd hlt (by omega))).trans
          (h2 e s v d).symm)
    | succ n ih =>
      intro e hn s v d
      exact (h1 e s v d).trans
        ((step_congr leaf w1 w2 e s v d (fun e' hlt => ih e' (by omega))).trans
          (h2 e s v d).symm)
  intro e s v d
  exact key (sizeOf e) e (Nat.le_refl _) s v d

/-- The recursion equation of the compiler's `go`, in structural form. -/
abbrev GoEq (eqv : Expr → Expr → Bool) (g : Expr → Nat → List Nat → Nat → Option Nat) : Prop :=
  ∀ (e : Expr) (subj : Nat) (vars : List Nat) (depth : Nat),
    g e subj vars depth = step (leafT eqv) g e subj vars depth

/-- EXISTENCE: the total `go` satisfies the equation. -/
theorem goT_sol (eqv : Expr → Expr → Bool) : GoEq eqv (goT eqv) := by
  intro e subj vars depth
  exact (congrArg (fun o : Option LeafData => o.bind (leafD eqv))
      (walkT_sol e subj vars depth)).trans
    (step_bind leafW (leafT eqv) (leafD eqv) (fun _ _ _ _ _ => rfl) walkT e subj vars depth)

/-- UNIQUENESS: a function satisfying the equation is the total `go`. -/
theorem go_unique (eqv : Expr → Expr → Bool) (g : Expr → Nat → List Nat → Nat → Option Nat)
    (hg : GoEq eqv g) : ∀ e subj vars depth, g e subj vars depth = goT eqv e subj vars depth :=
  step_unique (leafT eqv) g (goT eqv) hg (goT_sol eqv)

/-- The equation on the first arm's shape, read off `goT_sol`. -/
theorem goT_shape (eqv : Expr → Expr → Bool) (c : Name)
    (us : List Level) (a1 a2 a3 : Expr) (t : Nat) (n1 : Name) (t1 : Expr) (bi1 : BinderInfo)
    (n2 : Name) (t2 : Expr) (bi2 : BinderInfo) (rest : Expr) (subj : Nat) (vars : List Nat)
    (depth : Nat) :
    goT eqv (shapeE c us a1 a2 a3 t n1 t1 bi1 n2 t2 bi2 rest) subj vars depth =
      if c = ``Prod.casesOn then
        if t != subj then none else goT eqv rest 0 ((vars.map (· + 2)) ++ [1]) (depth + 2)
      else none :=
  (goT_sol eqv (shapeE c us a1 a2 a3 t n1 t1 bi1 n2 t2 bi2 rest) subj vars depth).trans
    (step_shape (leafT eqv) (goT eqv) c us a1 a2 a3 t n1 t1 bi1 n2 t2 bi2 rest subj vars depth)

/-- The equation at a term whose head is a bound variable: the leaf. -/
theorem goT_bvar (eqv : Expr → Expr → Bool) (e : Expr) (subj : Nat) (vars : List Nat)
    (depth : Nat) (h : Nat) (hh : headT e = .bvar h) :
    goT eqv e subj vars depth = leafT eqv h (argsT e) subj vars depth :=
  (goT_sol eqv e subj vars depth).trans (step_bvar (leafT eqv) (goT eqv) e subj vars depth h hh)

/-! ## The provable links to the compiler's text -/

/-- At the compiler's test, `listEqv` is the compiler's `==` on lists. -/
theorem listEqv_exprEqv : ∀ (l1 l2 : List Expr), listEqv exprEqv l1 l2 = (l1 == l2)
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | a :: as, b :: bs =>
    (congrArg (fun r : Bool => (a == b) && r) (listEqv_exprEqv as bs) :
      ((a == b) && listEqv exprEqv as bs) = ((a == b) && (as == bs)))

/-- `headT` is `Lean.Expr.getAppFn`. -/
theorem headT_eq_getAppFn : ∀ e : Expr, headT e = e.getAppFn
  | .app f _ => headT_eq_getAppFn f
  | .bvar _ => rfl
  | .fvar _ => rfl
  | .mvar _ => rfl
  | .sort _ => rfl
  | .const _ _ => rfl
  | .lam _ _ _ _ => rfl
  | .forallE _ _ _ _ => rfl
  | .letE _ _ _ _ _ => rfl
  | .lit _ => rfl
  | .mdata _ _ => rfl
  | .proj _ _ _ => rfl

end Tools.ShippingReaderMatcherArity
