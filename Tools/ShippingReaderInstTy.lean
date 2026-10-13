import Lean

/-! # The machine reader's `machInstanceS.inst`, total (reader generalisation, third unit)

WRITTEN, NOT BUILT (par/h-1). NOT wired into the reader: the compiler is not
edited and does not import this file. Record: `docs/parallel/H-reader-units.md`.

## The function

The local `inst` of `Sparkle.Compiler.Elab.machInstanceS` (Elab.lean
4084–4087) computes the result type of a call from the callee's type and the
arguments:

    let rec inst : Lean.Expr → List Lean.Expr → Option Lean.Expr
      | e, [] => some e
      | .forallE _ _ b _, a :: as => inst (b.instantiate1 a) as
      | _, _ => none

It recurses on the ARGUMENT LIST, which shrinks: structural as written. It
is `partial` only by position (a `let rec` inside a `partial def` of a
mutual block). The term it recurses with, `b.instantiate1 a`, is the result
of an extern (`@[extern "lean_expr_instantiate1"] opaque`), but no measure
goes through it.

## What is here

* `instW` — the compiler's text, verbatim, as a `def` (structural on the
  list). No fuel.
* `instG subst` — the same function with the list matched first and the
  substitution a PARAMETER; `instT = instG (fun b a => b.instantiate1 a)`.
* `instW_eq_instT` — a kernel equation (both total).
* the recursion equation `InstEq subst r` (one unfolding, `instStep`), that
  `instG subst` satisfies it (`instG_sol`) and that it has exactly one
  solution (`inst_unique`); `instStepW_eq` — the compiler's text as an
  equation (`InstEqW`) is `InstEq` at `instantiate1`, so
  `inst_uniqueW : InstEqW r → r e args = instW e args`.
* SUCCESSFUL INPUTS (`instG_some`): with the premise that the substitution
  does not remove leading binders (`∀ b a, piDepth b ≤ piDepth (subst b a)`
  — at `instantiate1` a statement about the extern: not proved, not assumed),
  the function returns a result whenever there are at most as many arguments
  as the type has leading binders. The reader's call has exactly that many
  (`instG_callSite`, first part of `Tools/ShippingReaderInstTyShadow.lean`,
  which imports the compiler for `telescopeKinds`). Without the premise:
  `instG_nil` (no argument: always a result).

## The boundary

1. `machInstanceS.inst` is `partial`: an opaque constant. No kernel equation
   with it exists; none is assumed. By `inst_uniqueW` the ONLY statement left
   outside the kernel is: the compiled function satisfies its own source
   equation.
2. `Expr.instantiate1` is an extern: what `inst` RETURNS cannot be computed
   in the kernel, for the old function or the new one. The new definition
   does not change which extern is called or on what.

Well-typedness premises: none for the definition and the correspondence.
The success theorem's premise is about substitution, not about typing.
Acceptance is not narrowed: the definition has the compiler's three clauses
and no bound. -/
namespace Tools.ShippingReaderInstTy
open Lean

/-- The compiler's text (Elab.lean 4084–4087), as a `def`. -/
def instW : Expr → List Expr → Option Expr
  | e, [] => some e
  | .forallE _ _ b _, a :: as => instW (b.instantiate1 a) as
  | _, _ => none

/-- The same function, the argument list matched first, the substitution a
parameter. Structural on the list. -/
def instG (subst : Expr → Expr → Expr) (e : Expr) (args : List Expr) : Option Expr :=
  match args with
  | [] => some e
  | a :: as =>
    match e with
    | .forallE _ _ b _ => instG subst (subst b a) as
    | _ => none

/-- The compiler's substitution (an extern). -/
def inst1 (b a : Expr) : Expr := b.instantiate1 a

/-- `inst`, total. -/
def instT (e : Expr) (args : List Expr) : Option Expr := instG inst1 e args

theorem instG_nil (subst : Expr → Expr → Expr) (e : Expr) : instG subst e [] = some e := rfl

theorem instG_forall (subst : Expr → Expr → Expr) (n : Name) (t b : Expr) (bi : BinderInfo)
    (a : Expr) (as : List Expr) :
    instG subst (.forallE n t b bi) (a :: as) = instG subst (subst b a) as := rfl

/-- **The compiler's text is the total definition** (both total; a kernel
equation). -/
theorem instW_eq_instT : ∀ (as : List Expr) (e : Expr), instW e as = instT e as
  | [], e => by
    cases e <;> rfl
  | a :: as, e => by
    cases e with
    | forallE n t b bi => exact instW_eq_instT as (b.instantiate1 a)
    | _ => rfl

/-! ## The recursion equation has exactly one solution -/

/-- One unfolding, the recursive call `r` a parameter. -/
def instStep (subst : Expr → Expr → Expr) (r : Expr → List Expr → Option Expr) (e : Expr)
    (args : List Expr) : Option Expr :=
  match args with
  | [] => some e
  | a :: as =>
    match e with
    | .forallE _ _ b _ => r (subst b a) as
    | _ => none

/-- The recursion equation of `inst`. -/
abbrev InstEq (subst : Expr → Expr → Expr) (r : Expr → List Expr → Option Expr) : Prop :=
  ∀ (e : Expr) (args : List Expr), r e args = instStep subst r e args

/-- EXISTENCE. -/
theorem instG_sol (subst : Expr → Expr → Expr) : InstEq subst (instG subst) := by
  intro e args
  cases args with
  | nil => rfl
  | cons a as => cases e <;> rfl

/-- UNIQUENESS (induction on the argument list). -/
theorem inst_unique (subst : Expr → Expr → Expr) (r : Expr → List Expr → Option Expr)
    (h : InstEq subst r) : ∀ (args : List Expr) (e : Expr), r e args = instG subst e args
  | [], e => h e []
  | a :: as, e =>
    (h e (a :: as)).trans (by
      cases e with
      | forallE n t b bi => exact inst_unique subst r h as (subst b a)
      | _ => rfl)

/-- One unfolding of the compiler's text, as written (the pair of the type
and the list matched together). -/
def instStepW (r : Expr → List Expr → Option Expr) : Expr → List Expr → Option Expr
  | e, [] => some e
  | .forallE _ _ b _, a :: as => r (b.instantiate1 a) as
  | _, _ => none

/-- The compiler's text as an equation. -/
abbrev InstEqW (r : Expr → List Expr → Option Expr) : Prop :=
  ∀ (e : Expr) (args : List Expr), r e args = instStepW r e args

theorem instStepW_eq (r : Expr → List Expr → Option Expr) (e : Expr) (args : List Expr) :
    instStepW r e args = instStep inst1 r e args := by
  cases args with
  | nil => cases e <;> rfl
  | cons a as => cases e <;> rfl

/-- **A function satisfying the compiler's text as an equation is the
compiler's text as a `def`.** What is left outside the kernel is exactly the
premise at the compiled `partial` function. -/
theorem inst_uniqueW (r : Expr → List Expr → Option Expr) (h : InstEqW r) (e : Expr)
    (args : List Expr) : r e args = instW e args :=
  (inst_unique inst1 r (fun e args => (h e args).trans (instStepW_eq r e args)) args e).trans
    (instW_eq_instT args e).symm

/-! ## Successful inputs are preserved -/

/-- The number of leading binders of a type, syntactically. -/
def piDepth : Expr → Nat
  | .forallE _ _ b _ => piDepth b + 1
  | _ => 0

/-- **Successful inputs**: a substitution that does not remove leading
binders, and at most as many arguments as the type has leading binders. -/
theorem instG_some (subst : Expr → Expr → Expr)
    (hsub : ∀ b a, piDepth b ≤ piDepth (subst b a)) :
    ∀ (args : List Expr) (e : Expr), args.length ≤ piDepth e →
      ∃ r, instG subst e args = some r
  | [], e, _ => ⟨e, rfl⟩
  | a :: as, e, h => by
    cases e with
    | forallE n t b bi =>
      have h' : as.length + 1 ≤ piDepth b + 1 := h
      have hs := hsub b a
      exact instG_some subst hsub as (subst b a) (by omega)
    | _ =>
      exact absurd h (by
        show ¬ (as.length + 1 ≤ 0)
        omega)

/-- More arguments than the function reads binders for: refused, when the
type left is not a binder (no premise). -/
theorem instG_none_of_not_forall (subst : Expr → Expr → Expr) (e a : Expr) (as : List Expr)
    (h : piDepth e = 0) : instG subst e (a :: as) = none := by
  cases e with
  | forallE n t b bi =>
    exact absurd h (by
      show ¬ (piDepth b + 1 = 0)
      omega)
  | _ => rfl

end Tools.ShippingReaderInstTy
