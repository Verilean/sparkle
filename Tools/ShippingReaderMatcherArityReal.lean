import Tools.ShippingReaderMatcherArityArray
import Sparkle.Compiler.MachRawSurface

/-! # `prodMatcherArity?` after the switch-over: theorems about the REAL function

WRITTEN, NOT BUILT (branch `fix/reader-p1`; record:
`docs/parallel/P-reader-2.md`). Needs the switch-over (the compiler's
`prodMatcherArity?` a plain `def`, its `go` = `MachProdMatcher.goS (· == ·)`).
No `sorry`, no axiom, no `native_decide`.

Every theorem below has the compiler's constant on its left-hand side:

* `goS_sol` / `goS_eq_goT` — the structural walk of the compiler solves the
  structural recursion equation `GoEq` (`Tools/ShippingReaderMatcherArityUnique.lean`),
  hence is `goT` (uniqueness, BUILT);
* `real_go_eq`, `real_go_fun` — the compiler's `prodMatcherArity?.go` IS
  `goT exprEqv`;
* `real_go_oldEq` — the compiler's `go` satisfies the OLD source equation
  (the array-form text of the `partial` function it replaced), and
  `real_go_unique` — it is the ONLY function that does;
* `prodMatcherArity_text`, `prodMatcherArity_eq` — the compiler's
  `prodMatcherArity?` IS `prodMatcherArityT` (H's total function), so every
  theorem about `prodMatcherArityT` / `prodMatcherArityG exprEqv` is about the
  real reader: `real_canon` (success on canonical pair matchers, the one
  premise about `Expr.eqv` kept explicit), `real_old` (the OLD text over any
  solution of the old equation returns what the compiler returns now).

PREDICTED axioms: `propext`, `Classical.choice`, `Quot.sound`. -/
namespace Tools.ShippingReaderMatcherArityReal
open Lean
open Tools.ShippingReaderMatcherArity
open Tools.ShippingReaderMatcherArityArray

theorem argsAccS_eq : ∀ (e : Expr) (acc : List Expr),
    Sparkle.Compiler.MachProdMatcher.argsAccS e acc = argsAcc e acc
  | .app f a, acc => argsAccS_eq f (a :: acc)
  | .bvar _, _ => rfl
  | .fvar _, _ => rfl
  | .mvar _, _ => rfl
  | .sort _, _ => rfl
  | .const _ _, _ => rfl
  | .lam _ _ _ _, _ => rfl
  | .forallE _ _ _ _, _ => rfl
  | .letE _ _ _ _ _, _ => rfl
  | .lit _, _ => rfl
  | .mdata _ _, _ => rfl
  | .proj _ _ _, _ => rfl

theorem argsS_eq (e : Expr) : Sparkle.Compiler.MachProdMatcher.argsS e = argsT e :=
  argsAccS_eq e []

theorem listEqvS_eq (eqv : Expr → Expr → Bool) : ∀ (l1 l2 : List Expr),
    Sparkle.Compiler.MachProdMatcher.listEqvS eqv l1 l2 = listEqv eqv l1 l2
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | a :: as, b :: bs =>
    (congrArg (fun r : Bool => eqv a b && r) (listEqvS_eq eqv as bs) :
      (eqv a b && Sparkle.Compiler.MachProdMatcher.listEqvS eqv as bs) =
        (eqv a b && listEqv eqv as bs))

theorem listEqvS_fun (eqv : Expr → Expr → Bool) :
    Sparkle.Compiler.MachProdMatcher.listEqvS eqv = listEqv eqv :=
  funext fun l1 => funext fun l2 => listEqvS_eq eqv l1 l2

/-- The compiler's walk solves the structural recursion equation. -/
theorem goS_sol (eqv : Expr → Expr → Bool) : GoEq eqv (Sparkle.Compiler.MachProdMatcher.goS eqv) := by
  intro e subj vars depth
  have hh : e.getAppFn = headT e := (headT_eq_getAppFn e).symm
  have ha : Sparkle.Compiler.MachProdMatcher.argsS e = argsT e := argsS_eq e
  have hl := listEqvS_fun eqv
  first
    | (rw [Sparkle.Compiler.MachProdMatcher.goS.eq_def, hh, ha, hl]; rfl)
    | (rw [Sparkle.Compiler.MachProdMatcher.goS.eq_def, hh, ha, hl])
    | (rw [Sparkle.Compiler.MachProdMatcher.goS.eq_def, hh, ha, hl]
       unfold step stepH casesArm leafT
       rfl)
    | (unfold Sparkle.Compiler.MachProdMatcher.goS
       rw [hh, ha, hl]
       rfl)
    | (unfold Sparkle.Compiler.MachProdMatcher.goS
       rw [hh, ha, hl]
       unfold step stepH casesArm leafT
       rfl)

theorem goS_eq_goT (eqv : Expr → Expr → Bool) :
    ∀ (e : Expr) (subj : Nat) (vars : List Nat) (depth : Nat),
      Sparkle.Compiler.MachProdMatcher.goS eqv e subj vars depth = goT eqv e subj vars depth :=
  go_unique eqv (Sparkle.Compiler.MachProdMatcher.goS eqv) (goS_sol eqv)

/-- **The compiler's `go` is `goT exprEqv`.** -/
theorem real_go_eq (e : Expr) (subj : Nat) (vars : List Nat) (depth : Nat) :
    Sparkle.Compiler.MachRawSurface.prodMatcherArity?.go e subj vars depth =
      goT exprEqv e subj vars depth :=
  goS_eq_goT exprEqv e subj vars depth

theorem real_go_fun : Sparkle.Compiler.MachRawSurface.prodMatcherArity?.go = goT exprEqv :=
  funext fun e => funext fun s => funext fun v => funext fun d => real_go_eq e s v d

/-- **The compiler's `go` satisfies the OLD source equation** (the array-form
text of the `partial` function it replaced). -/
theorem real_go_oldEq : OldEq Sparkle.Compiler.MachRawSurface.prodMatcherArity?.go := by
  rw [real_go_fun]
  exact goT_oldSol

/-- … and it is the only function that does. -/
theorem real_go_unique (g : Expr → Nat → List Nat → Nat → Option Nat) (h : OldEq g) :
    ∀ (e : Expr) (subj : Nat) (vars : List Nat) (depth : Nat),
      g e subj vars depth = Sparkle.Compiler.MachRawSurface.prodMatcherArity?.go e subj vars depth :=
  fun e s v d => (old_unique g h e s v d).trans (real_go_eq e s v d).symm

/-- The compiler's `prodMatcherArity?` text is `infoArityOf` over its `go`. -/
theorem prodMatcherArity_text (env : Environment) (n : Name) :
    Sparkle.Compiler.MachRawSurface.prodMatcherArity? env n =
      infoArityOf Sparkle.Compiler.MachRawSurface.prodMatcherArity?.go (env.find? n) := by
  first
    | rfl
    | (unfold Sparkle.Compiler.MachRawSurface.prodMatcherArity? infoArityOf valueArityOf; rfl)
    | (unfold Sparkle.Compiler.MachRawSurface.prodMatcherArity? infoArityOf
       cases env.find? n with
       | none => rfl
       | some ci =>
         cases ci <;> first
           | rfl
           | (unfold valueArityOf; rfl)
           | (unfold valueArityOf; split <;> rfl))

/-- **The compiler's `prodMatcherArity?` IS `prodMatcherArityT`.** -/
theorem prodMatcherArity_eq (env : Environment) (n : Name) :
    Sparkle.Compiler.MachRawSurface.prodMatcherArity? env n = prodMatcherArityT env n :=
  (prodMatcherArity_text env n).trans
    (congrArg (fun g : Expr → Nat → List Nat → Nat → Option Nat => infoArityOf g (env.find? n))
      real_go_fun)

theorem prodMatcherArity_fun :
    Sparkle.Compiler.MachRawSurface.prodMatcherArity? = prodMatcherArityT :=
  funext fun env => funext fun n => prodMatcherArity_eq env n

/-- Success on every canonical pair matcher, about the REAL function (the
one premise about the extern `Expr.eqv` stays an explicit hypothesis). -/
theorem real_canon (hrefl : ∀ i : Nat, ((Expr.bvar i) == (Expr.bvar i)) = true)
    (env : Environment) (n : Name)
    (d : DefinitionVal) (m0 m1 m2 : Name × Expr × BinderInfo) (dcs : List Deco)
    (hf : env.find? n = some (.defnInfo d)) (hv : d.value = matcherE m0 m1 m2 dcs) :
    Sparkle.Compiler.MachRawSurface.prodMatcherArity? env n = some (dcs.length + 1) :=
  (prodMatcherArity_eq env n).trans (prodMatcherArityT_canon hrefl env n d m0 m1 m2 dcs hf hv)

/-- The OLD text over any `go` solving the OLD source equation returns what
the compiler returns now. -/
theorem real_old (go : Expr → Nat → List Nat → Nat → Option Nat) (h : OldEq go)
    (env : Environment) (n : Name) :
    prodMatcherArityOldOf go env n = Sparkle.Compiler.MachRawSurface.prodMatcherArity? env n :=
  (oldArity_unique go h env n).trans (prodMatcherArity_eq env n).symm

end Tools.ShippingReaderMatcherArityReal
