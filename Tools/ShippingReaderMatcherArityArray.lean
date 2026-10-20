import Tools.ShippingReaderMatcherArityUnique
import Tools.ShippingSparseCasesTac

/-! # `prodMatcherArity?.go`: the ARRAY form of its source equation is the structural one

WRITTEN, NOT BUILT (branch `fix/reader-p1`; record:
`docs/parallel/P-reader-2.md`). No `sorry`, no axiom, no `native_decide`.

Round 3 (branch `fix/reader-p3`, WRITTEN, NOT BUILT): the first build FAILED
at `stepOldP_eq` (`split` on `stepOldP.match_1`: v4.32.1 cannot generate the
equations / splitter of a matcher with name-literal and array-literal
patterns, measured by the integrator). Every statement is unchanged; the
proof of `stepOldP_eq` no longer splits that matcher. It goes through four
helper facts about `stepOldP`, each proved from the matcher's DEFINITION
(technique of `Tools.ShippingReaderRawNodeArm.match15_three`):
`stepOldP_bvar` / `stepOldP_other` (`rfl`: the head is a constructor),
`stepOldP_shape` (five arguments of the first arm's shape, any constant:
split the name into components, unfold the sparse case analyses, split the
string / size `dite`s) and `stepOldP_none` (any argument list NOT of that
shape: the same, then the list and its 4th/5th elements into constructors).
The sparse auxiliaries are unfolded by `dsimp_sparse_aux`
(`Tools/ShippingSparseCasesTac.lean`), which reads their generated names off
the goal. On the structural side only `casesArm`'s own matcher is split
(its splitter is generated: `casesArm_congr` builds).
Independent of the switch-over: it builds on poc as it is (it mentions no
constant of the compiler).

`docs/parallel/H-reader-units.md` §2b left one link of the boundary of
`prodMatcherArity?` unproved: "the source equation (array form) is the
structural form `GoEq`" — because `Lean.Expr.getAppArgs` is defined through
`getAppArgsAux`, a `private` definition of the `module` `Lean.Expr`, which
cannot be named from here. This file proves that link without naming it:

* `getAppArgs_of_eqns` — for ANY functions `g`, `ng` satisfying the two
  defining equations each of `getAppArgsAux` / `getAppNumArgsAux`,
  `g e (Array.replicate (ng e 0) d) (ng e 0 - 1) = (argsT e).toArray`;
* `getAppArgs_eq : e.getAppArgs = (argsT e).toArray` — after unfolding
  `Expr.getAppArgs` / `Expr.getAppNumArgs`, the goal IS that statement at
  the two private constants (found by unification; a fallback names them
  through the private-name scheme `mkPrivateNameCore`), and their equations
  hold by `rfl` (structural definitions; a non-module file imports the
  private level of a module, `Lean/Environment.lean` 1612);
* `stepOld` — the OLD compiler's `go` body VERBATIM (MachRawSurface.lean
  40–52 at c3176ef1), the recursive call a parameter; `stepOld_eq_step`:
  it is `step (leafT exprEqv)` for every recursive call;
* hence `OldEq g ↔ GoEq exprEqv g`, `goT_oldSol` (the total function solves
  the OLD source equation) and `old_unique` (every solution of the OLD
  source equation is `goT exprEqv`), `oldArity_unique` (the same for the
  whole `prodMatcherArity?` text).

What stays outside the kernel after this file: ONLY "the compiled `partial`
`prodMatcherArity?` / `go` satisfy their own source equations" (the meaning
of `partial`), and `Expr.eqv` stays a parameter where it was one (here it is
the compiler's own `==`, `exprEqv`; nothing about the extern is used).

PREDICTED axioms: `propext`, `Classical.choice`, `Quot.sound`. -/
namespace Tools.ShippingReaderMatcherArityArray
open Lean
open Tools.ShippingReaderMatcherArity

/-! ## The spine, structurally -/

theorem argsAcc_append : ∀ (e : Expr) (acc : List Expr), argsAcc e acc = argsT e ++ acc
  | .app f a, acc =>
    (argsAcc_append f (a :: acc)).trans
      ((congrArg (· ++ acc) (argsAcc_append f [a])).trans (List.append_assoc _ _ _)).symm
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

theorem argsT_app (f a : Expr) : argsT (.app f a) = argsT f ++ [a] :=
  argsAcc_append f [a]

theorem len_snoc (L : List Expr) (a : Expr) : (L ++ [a]).length = L.length + 1 := by
  simp

theorem succ_sub_one' (n : Nat) : n + 1 - 1 = n := by
  omega

theorem mkL_headT_argsAcc : ∀ (e : Expr) (acc : List Expr),
    mkL (headT e) (argsAcc e acc) = mkL e acc
  | .app f a, acc => mkL_headT_argsAcc f (a :: acc)
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

/-- A term is its head applied to its arguments. -/
theorem mkL_headT_argsT (e : Expr) : mkL (headT e) (argsT e) = e :=
  mkL_headT_argsAcc e []

/-! ## `getAppArgs` from the equations of its auxiliaries -/

theorem set_mid {α : Type} (a b : α) (S : List α) :
    ∀ P : List α, (P ++ b :: S).set P.length a = P ++ a :: S
  | [] => rfl
  | p :: P => congrArg (p :: ·) (set_mid a b S P)

theorem rep_set (n : Nat) (d a : Expr) (S : List Expr) :
    (List.replicate (n + 1) d ++ S).toArray.set! n a = (List.replicate n d ++ a :: S).toArray := by
  apply Array.ext'
  rw [Array.toList_set!]
  show (List.replicate (n + 1) d ++ S).set n a = List.replicate n d ++ a :: S
  rw [List.replicate_succ', List.append_assoc]
  have h := set_mid a d S (List.replicate n d)
  rw [List.length_replicate] at h
  exact h

/-- What `getAppArgsAux` computes, for any function with its two equations:
started on `k = (argsT e).length` placeholders in front of `S` at index
`k - 1`, it writes the arguments over the placeholders. -/
theorem appArgs_spec (g : Expr → Array Expr → Nat → Array Expr) (d : Expr)
    (happ : ∀ (f a : Expr) (as : Array Expr) (i : Nat), g (.app f a) as i = g f (as.set! i a) (i - 1))
    (hnot : ∀ (x : Expr) (as : Array Expr) (i : Nat), (∀ f a, x ≠ .app f a) → g x as i = as) :
    ∀ (e : Expr) (S : List Expr),
      g e (List.replicate (argsT e).length d ++ S).toArray ((argsT e).length - 1) =
        (argsT e ++ S).toArray
  | .app f a, S => by
    rw [argsT_app, len_snoc, succ_sub_one', happ, rep_set, List.append_assoc]
    exact appArgs_spec g d happ hnot f (a :: S)
  | .bvar i, S => hnot (.bvar i) _ _ (by intro _ _ h; cases h)
  | .fvar i, S => hnot (.fvar i) _ _ (by intro _ _ h; cases h)
  | .mvar i, S => hnot (.mvar i) _ _ (by intro _ _ h; cases h)
  | .sort u, S => hnot (.sort u) _ _ (by intro _ _ h; cases h)
  | .const c us, S => hnot (.const c us) _ _ (by intro _ _ h; cases h)
  | .lam n t b bi, S => hnot (.lam n t b bi) _ _ (by intro _ _ h; cases h)
  | .forallE n t b bi, S => hnot (.forallE n t b bi) _ _ (by intro _ _ h; cases h)
  | .letE n t v b nd, S => hnot (.letE n t v b nd) _ _ (by intro _ _ h; cases h)
  | .lit l, S => hnot (.lit l) _ _ (by intro _ _ h; cases h)
  | .mdata md b, S => hnot (.mdata md b) _ _ (by intro _ _ h; cases h)
  | .proj s i b, S => hnot (.proj s i b) _ _ (by intro _ _ h; cases h)

/-- What `getAppNumArgsAux` computes, for any function with its two equations. -/
theorem appNumArgs_spec (ng : Expr → Nat → Nat)
    (happ : ∀ (f a : Expr) (n : Nat), ng (.app f a) n = ng f (n + 1))
    (hnot : ∀ (x : Expr) (n : Nat), (∀ f a, x ≠ .app f a) → ng x n = n) :
    ∀ (e : Expr) (n : Nat), ng e n = (argsT e).length + n
  | .app f a, n => by
    rw [happ, appNumArgs_spec ng happ hnot f (n + 1), argsT_app, len_snoc]
    omega
  | .bvar i, n => (hnot (.bvar i) n (by intro _ _ h; cases h)).trans (Nat.zero_add n).symm
  | .fvar i, n => (hnot (.fvar i) n (by intro _ _ h; cases h)).trans (Nat.zero_add n).symm
  | .mvar i, n => (hnot (.mvar i) n (by intro _ _ h; cases h)).trans (Nat.zero_add n).symm
  | .sort u, n => (hnot (.sort u) n (by intro _ _ h; cases h)).trans (Nat.zero_add n).symm
  | .const c us, n => (hnot (.const c us) n (by intro _ _ h; cases h)).trans (Nat.zero_add n).symm
  | .lam m t b bi, n =>
    (hnot (.lam m t b bi) n (by intro _ _ h; cases h)).trans (Nat.zero_add n).symm
  | .forallE m t b bi, n =>
    (hnot (.forallE m t b bi) n (by intro _ _ h; cases h)).trans (Nat.zero_add n).symm
  | .letE m t v b nd, n =>
    (hnot (.letE m t v b nd) n (by intro _ _ h; cases h)).trans (Nat.zero_add n).symm
  | .lit l, n => (hnot (.lit l) n (by intro _ _ h; cases h)).trans (Nat.zero_add n).symm
  | .mdata md b, n => (hnot (.mdata md b) n (by intro _ _ h; cases h)).trans (Nat.zero_add n).symm
  | .proj s i b, n => (hnot (.proj s i b) n (by intro _ _ h; cases h)).trans (Nat.zero_add n).symm

/-- `Expr.getAppArgs`' text over any two functions with the equations of its
two private auxiliaries. -/
theorem getAppArgs_of_eqns (g : Expr → Array Expr → Nat → Array Expr) (ng : Expr → Nat → Nat)
    (d : Expr)
    (happ : ∀ (f a : Expr) (as : Array Expr) (i : Nat), g (.app f a) as i = g f (as.set! i a) (i - 1))
    (hnot : ∀ (x : Expr) (as : Array Expr) (i : Nat), (∀ f a, x ≠ .app f a) → g x as i = as)
    (nhapp : ∀ (f a : Expr) (n : Nat), ng (.app f a) n = ng f (n + 1))
    (nhnot : ∀ (x : Expr) (n : Nat), (∀ f a, x ≠ .app f a) → ng x n = n)
    (e : Expr) :
    g e (Array.replicate (ng e 0) d) (ng e 0 - 1) = (argsT e).toArray := by
  have h1 : ng e 0 = (argsT e).length := appNumArgs_spec ng nhapp nhnot e 0
  have h2 := appArgs_spec g d happ hnot e []
  rw [h1]
  simp only [List.append_nil] at h2
  exact h2

open Lean Elab Term in
/-- A private auxiliary `Lean.Expr.<n>` of the module `Lean.Expr`, as a
constant: the name `mkPrivateNameCore` gives it (`Lean/PrivateName.lean` 29).
Used only as a fallback of `getAppArgs_eq`. -/
elab "exprPrivate%" n:ident : term => do
  let full := Name.mkNum (`_private ++ `Lean.Expr) 0 ++ (`Lean.Expr ++ n.getId)
  return mkConst full

/-- **`Expr.getAppArgs` is `argsT`**, as arrays: the link of H's boundary 2. -/
theorem getAppArgs_eq (e : Expr) : e.getAppArgs = (argsT e).toArray := by
  first
    | (unfold Lean.Expr.getAppArgs Lean.Expr.getAppNumArgs
       try dsimp only
       apply getAppArgs_of_eqns
       all_goals first
         | (intro f a as i; rfl)
         | (intro f a n; rfl)
         | (intro x as i h; cases x <;> first | rfl | exact absurd rfl (h _ _))
         | (intro x n h; cases x <;> first | rfl | exact absurd rfl (h _ _)))
    | (delta Lean.Expr.getAppArgs Lean.Expr.getAppNumArgs
       try dsimp only
       apply getAppArgs_of_eqns
       all_goals first
         | (intro f a as i; rfl)
         | (intro f a n; rfl)
         | (intro x as i h; cases x <;> first | rfl | exact absurd rfl (h _ _))
         | (intro x n h; cases x <;> first | rfl | exact absurd rfl (h _ _)))
    | exact getAppArgs_of_eqns (exprPrivate% getAppArgsAux) (exprPrivate% getAppNumArgsAux)
        (mkSort Level.zero)
        (fun _ _ _ _ => rfl)
        (by intro x as i h; cases x <;> first | rfl | exact absurd rfl (h _ _))
        (fun _ _ _ => rfl)
        (by intro x n h; cases x <;> first | rfl | exact absurd rfl (h _ _))
        e

/-! ## The OLD source equation of `go`, verbatim -/

/-- The OLD compiler's `go` body, VERBATIM (`Sparkle/Compiler/MachRawSurface.lean`
40–52 at c3176ef1), with its two discriminants passed in and the recursive
call `r`. -/
def stepOldP (r : Expr → Nat → List Nat → Nat → Option Nat) (hd : Expr) (args : Array Expr)
    (subj : Nat) (vars : List Nat) (depth : Nat) : Option Nat :=
  match hd, args with
  | .const ``Prod.casesOn _, #[_, _, _, .bvar t, .lam _ _ (.lam _ _ rest _) _] =>
    if t != subj then none else
    -- under two binders: fst = bvar 1, snd = bvar 0; earlier vars shift by 2
    r rest 0 ((vars.map (· + 2)) ++ [1]) (depth + 2)
  | .bvar hIdx, args =>
    -- `h` sits at index `depth + 0` relative to the walk start (+2 per level)
    if hIdx != depth then none else
    let expected := vars ++ [subj]
    if args.toList == expected.map Lean.Expr.bvar then some args.size else none
  | _, _ => none

/-- ONE unfolding of the OLD `go`: `match e.getAppFn, e.getAppArgs with …`. -/
def stepOld (r : Expr → Nat → List Nat → Nat → Option Nat) (e : Expr) (subj : Nat)
    (vars : List Nat) (depth : Nat) : Option Nat :=
  stepOldP r e.getAppFn e.getAppArgs subj vars depth

/-- The OLD source equation of `go`. -/
abbrev OldEq (g : Expr → Nat → List Nat → Nat → Option Nat) : Prop :=
  ∀ (e : Expr) (subj : Nat) (vars : List Nat) (depth : Nat),
    g e subj vars depth = stepOld g e subj vars depth

theorem arm1 (r : Expr → Nat → List Nat → Nat → Option Nat) (e : Expr) (us : List Level)
    (a1 a2 a3 : Expr) (t : Nat) (n1 : Name) (ty1 : Expr) (n2 : Name) (ty2 : Expr) (rest : Expr)
    (bi2 bi1 : BinderInfo) (subj : Nat) (vars : List Nat) (depth : Nat)
    (hh : headT e = .const ``Prod.casesOn us)
    (ha : (argsT e).toArray = #[a1, a2, a3, .bvar t, .lam n1 ty1 (.lam n2 ty2 rest bi2) bi1]) :
    (if t != subj then none else r rest 0 ((vars.map (· + 2)) ++ [1]) (depth + 2)) =
      step (leafT exprEqv) r e subj vars depth := by
  have hL : argsT e = [a1, a2, a3, .bvar t, .lam n1 ty1 (.lam n2 ty2 rest bi2) bi1] :=
    congrArg Array.toList ha
  have hm := mkL_headT_argsT e
  rw [hh, hL] at hm
  have he : e = shapeE ``Prod.casesOn us a1 a2 a3 t n1 ty1 bi1 n2 ty2 bi2 rest := hm.symm
  rw [he, step_shape]
  exact (if_pos rfl).symm

theorem arm2 (r : Expr → Nat → List Nat → Nat → Option Nat) (e : Expr) (hIdx : Nat)
    (args : Array Expr) (subj : Nat) (vars : List Nat) (depth : Nat)
    (hh : headT e = .bvar hIdx) (ha : (argsT e).toArray = args) :
    (if hIdx != depth then none else
      let expected := vars ++ [subj]
      if args.toList == expected.map Lean.Expr.bvar then some args.size else none) =
      step (leafT exprEqv) r e subj vars depth := by
  subst ha
  rw [step_bvar (leafT exprEqv) r e subj vars depth hIdx hh]
  unfold leafT
  rw [listEqv_exprEqv]
  rfl

/-! ## `stepOldP` from its matcher's definition

v4.32.1 does not generate the equations / splitter of `stepOldP.match_1`
(name-literal + array-literal patterns; measured), so no `split` /
`match_1.eq_N` on it below. Each fact is proved either by `rfl` (the head is
a constructor: the matcher's first sparse case analysis reduces) or on the
unfolded matcher: the `Name` split into components (`Prod`, `casesOn`, then
`anonymous`), the sparse case analyses unfolded (`dsimp_sparse_aux`, which
reads their generated names off the goal), the `dite`s on the component
strings and on `args.size = 5` split. -/

open Tools.ShippingSparseCasesTac

/-- `Prod.casesOn`, as the constructors of `Name` (the pattern's literal). -/
local notation "pcN" => Name.str (Name.str Name.anonymous "Prod") "casesOn"

/-- The first arm's body (a constant, so that `split` does not split the
right-hand side's copy of the `t != subj` test before the left-hand side's). -/
def armA (r : Expr → Nat → List Nat → Nat → Option Nat) (t : Nat) (rest : Expr) (subj : Nat)
    (vars : List Nat) (depth : Nat) : Option Nat :=
  if t != subj then none else r rest 0 ((vars.map (· + 2)) ++ [1]) (depth + 2)

/-- The second arm: a bound-variable head. -/
theorem stepOldP_bvar (r : Expr → Nat → List Nat → Nat → Option Nat) (hIdx : Nat)
    (args : Array Expr) (subj : Nat) (vars : List Nat) (depth : Nat) :
    stepOldP r (.bvar hIdx) args subj vars depth =
      (if hIdx != depth then none else
        let expected := vars ++ [subj]
        if args.toList == expected.map Lean.Expr.bvar then some args.size else none) := by
  first
    | rfl
    | exact rfl
    | (unfold stepOldP
       first | unfold stepOldP.match_1 | unfold_matchers_aux
       try dsimp_sparse_aux
       rfl)

/-- A head that is neither a constant nor a bound variable: the catch-all. -/
theorem stepOldP_other (r : Expr → Nat → List Nat → Nat → Option Nat) (hd : Expr)
    (args : Array Expr) (subj : Nat) (vars : List Nat) (depth : Nat)
    (hc : ∀ c us, hd ≠ .const c us) (hb : ∀ i, hd ≠ .bvar i) :
    stepOldP r hd args subj vars depth = none := by
  cases hd with
  | bvar i => exact absurd rfl (hb i)
  | const c us => exact absurd rfl (hc c us)
  | _ =>
    first
      | rfl
      | exact rfl
      | (unfold stepOldP
         first | unfold stepOldP.match_1 | unfold_matchers_aux
         try dsimp_sparse_aux
         rfl)

set_option maxHeartbeats 2000000 in
/-- Five arguments of the first arm's shape, ANY constant head. -/
theorem stepOldP_shape (r : Expr → Nat → List Nat → Nat → Option Nat) (c : Name)
    (us : List Level) (a1 a2 a3 : Expr) (t : Nat) (n1 : Name) (t1 : Expr) (bi1 : BinderInfo)
    (n2 : Name) (t2 : Expr) (bi2 : BinderInfo) (rest : Expr) (subj : Nat) (vars : List Nat)
    (depth : Nat) :
    stepOldP r (.const c us) #[a1, a2, a3, .bvar t, .lam n1 t1 (.lam n2 t2 rest bi2) bi1]
        subj vars depth =
      if c = pcN then armA r t rest subj vars depth else none := by
  unfold stepOldP
  first | unfold stepOldP.match_1 | unfold_matchers_aux
  rcases c with _ | ⟨_ | ⟨_ | ⟨p2, s2⟩ | ⟨p2, i2⟩, s1⟩ | ⟨p1, i1⟩, s0⟩ | ⟨p0, i0⟩
  all_goals try dsimp_sparse_aux
  all_goals (repeat' split)
  all_goals first
    | rfl
    | (subst_vars; rfl)
    | (exfalso; simp_all; done)
    | (subst_vars; exfalso; simp_all; done)
    | (simp only [armA]; simp_all; done)
    | (subst_vars; simp only [armA]; simp_all; done)
    | (exfalso; simp_all [Name.mkStr2]; done)

set_option maxHeartbeats 2000000 in
/-- Any argument list NOT of the first arm's shape, ANY constant head: `none`. -/
theorem stepOldP_none (r : Expr → Nat → List Nat → Nat → Option Nat) (c : Name)
    (us : List Level) (L : List Expr) (subj : Nat) (vars : List Nat) (depth : Nat)
    (hL : ¬ ∃ (a1 a2 a3 : Expr) (t : Nat) (n1 : Name) (t1 : Expr) (bi1 : BinderInfo) (n2 : Name)
      (t2 : Expr) (bi2 : BinderInfo) (rest : Expr),
      L = [a1, a2, a3, .bvar t, .lam n1 t1 (.lam n2 t2 rest bi2) bi1]) :
    stepOldP r (.const c us) L.toArray subj vars depth = none := by
  unfold stepOldP
  first | unfold stepOldP.match_1 | unfold_matchers_aux
  rcases c with _ | ⟨_ | ⟨_ | ⟨p2, s2⟩ | ⟨p2, i2⟩, s1⟩ | ⟨p1, i1⟩, s0⟩ | ⟨p0, i0⟩
  all_goals try dsimp_sparse_aux
  all_goals (repeat' split)
  -- every goal but the `Prod.casesOn`, `size = 5` one(s) closes here
  all_goals first
    | rfl
    | (exfalso; simp_all; done)
    | (subst_vars; exfalso; simp_all; done)
    | (simp_all; done)
    | (subst_vars; simp_all; done)
    | (exfalso; exact hL ⟨_, _, _, _, _, _, _, _, _, _, _, rfl⟩)
    | skip
  -- the `Prod.casesOn` branch with `size = 5`: the list has five elements,
  -- then the fourth, the fifth and its body into constructors (only the
  -- shape, excluded by `hL`, survives `rfl`)
  all_goals (
    rename_i _ _ hsz
    subst_vars
    obtain ⟨a1, a2, a3, a4, a5, rfl⟩ : ∃ a1 a2 a3 a4 a5 : Expr, L = [a1, a2, a3, a4, a5] := by
      rcases L with _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | ⟨a6, L'⟩⟩⟩⟩⟩⟩ <;> simp_all
    rcases a4 with ⟨t⟩ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ <;> try rfl
    all_goals (rcases a5 with _ | _ | _ | _ | _ | _ | ⟨n1, t1, b, bi1⟩ | _ | _ | _ | _ | _ <;> try rfl)
    all_goals (rcases b with _ | _ | _ | _ | _ | _ | ⟨n2, t2, rest, bi2⟩ | _ | _ | _ | _ | _ <;> try rfl)
    all_goals exact (hL ⟨_, _, _, _, _, _, _, _, _, _, _, rfl⟩).elim)

/-- `casesArm` refuses every term that is not of the first arm's shape (its
own matcher is split: its splitter is generated, as in `casesArm_congr`). -/
theorem casesArm_none_of_not (r : Expr → Nat → List Nat → Nat → Option Nat) (e : Expr)
    (subj : Nat) (vars : List Nat) (depth : Nat)
    (hs : ¬ ∃ (c : Name) (us : List Level) (a1 a2 a3 : Expr) (t : Nat) (n1 : Name) (t1 : Expr)
      (bi1 : BinderInfo) (n2 : Name) (t2 : Expr) (bi2 : BinderInfo) (rest : Expr),
      e = shapeE c us a1 a2 a3 t n1 t1 bi1 n2 t2 bi2 rest) :
    casesArm r e subj vars depth = none := by
  unfold casesArm
  split
  · exfalso
    apply hs
    first
      | exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
      | (subst_vars; exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩)
      | exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, by assumption⟩
  · rfl

/-- **The array form is the structural form**, for every recursive call. -/
theorem stepOldP_eq (r : Expr → Nat → List Nat → Nat → Option Nat) (e hd : Expr)
    (args : Array Expr) (subj : Nat) (vars : List Nat) (depth : Nat)
    (hh : headT e = hd) (ha : (argsT e).toArray = args) :
    stepOldP r hd args subj vars depth = step (leafT exprEqv) r e subj vars depth := by
  by_cases hs : ∃ (c : Name) (us : List Level) (a1 a2 a3 : Expr) (t : Nat) (n1 : Name)
      (t1 : Expr) (bi1 : BinderInfo) (n2 : Name) (t2 : Expr) (bi2 : BinderInfo) (rest : Expr),
      e = shapeE c us a1 a2 a3 t n1 t1 bi1 n2 t2 bi2 rest
  · -- the first arm's shape: both sides computed
    obtain ⟨c, us, a1, a2, a3, t, n1, t1, bi1, n2, t2, bi2, rest, rfl⟩ := hs
    subst hh
    subst ha
    exact (stepOldP_shape r c us a1 a2 a3 t n1 t1 bi1 n2 t2 bi2 rest subj vars depth).trans
      (step_shape (leafT exprEqv) r c us a1 a2 a3 t n1 t1 bi1 n2 t2 bi2 rest subj vars
        depth).symm
  · -- not the shape: `casesArm` refuses
    have hc : casesArm r e subj vars depth = none := casesArm_none_of_not r e subj vars depth hs
    have hrhs : ∀ hd' : Expr, headT e = hd' → (∀ i, hd' ≠ .bvar i) →
        step (leafT exprEqv) r e subj vars depth = none := by
      intro hd' h' hb
      unfold step
      rw [h']
      cases hd' with
      | bvar i => exact absurd rfl (hb i)
      | _ => exact hc
    cases hd with
    | bvar i =>
      exact (stepOldP_bvar r i args subj vars depth).trans (arm2 r e i args subj vars depth hh ha)
    | const c us =>
      subst ha
      have hnot : ¬ ∃ (a1 a2 a3 : Expr) (t : Nat) (n1 : Name) (t1 : Expr) (bi1 : BinderInfo)
          (n2 : Name) (t2 : Expr) (bi2 : BinderInfo) (rest : Expr),
          argsT e = [a1, a2, a3, .bvar t, .lam n1 t1 (.lam n2 t2 rest bi2) bi1] := by
        rintro ⟨a1, a2, a3, t, n1, t1, bi1, n2, t2, bi2, rest, hL⟩
        apply hs
        refine ⟨c, us, a1, a2, a3, t, n1, t1, bi1, n2, t2, bi2, rest, ?_⟩
        have hm := mkL_headT_argsT e
        rw [hh, hL] at hm
        exact hm.symm
      exact (stepOldP_none r c us (argsT e) subj vars depth hnot).trans
        (hrhs _ hh (fun _ h => by cases h)).symm
    | _ =>
      exact (stepOldP_other r _ args subj vars depth (fun _ _ h => by cases h)
        (fun _ h => by cases h)).trans (hrhs _ hh (fun _ h => by cases h)).symm

theorem stepOld_eq_step (r : Expr → Nat → List Nat → Nat → Option Nat) (e : Expr) (subj : Nat)
    (vars : List Nat) (depth : Nat) :
    stepOld r e subj vars depth = step (leafT exprEqv) r e subj vars depth :=
  stepOldP_eq r e e.getAppFn e.getAppArgs subj vars depth (headT_eq_getAppFn e)
    (getAppArgs_eq e).symm

theorem goEq_of_oldEq (g : Expr → Nat → List Nat → Nat → Option Nat) (h : OldEq g) :
    GoEq exprEqv g :=
  fun e subj vars depth => (h e subj vars depth).trans (stepOld_eq_step g e subj vars depth)

theorem oldEq_of_goEq (g : Expr → Nat → List Nat → Nat → Option Nat) (h : GoEq exprEqv g) :
    OldEq g :=
  fun e subj vars depth => (h e subj vars depth).trans (stepOld_eq_step g e subj vars depth).symm

/-- EXISTENCE: the total `go` solves the OLD (array-form) source equation. -/
theorem goT_oldSol : OldEq (goT exprEqv) :=
  oldEq_of_goEq (goT exprEqv) (goT_sol exprEqv)

/-- UNIQUENESS: every solution of the OLD source equation is `goT exprEqv`. -/
theorem old_unique (g : Expr → Nat → List Nat → Nat → Option Nat) (h : OldEq g) :
    ∀ (e : Expr) (subj : Nat) (vars : List Nat) (depth : Nat),
      g e subj vars depth = goT exprEqv e subj vars depth :=
  go_unique exprEqv g (goEq_of_oldEq g h)

/-- The OLD `prodMatcherArity?` text over a `go` (the outer `match` on
`env.find? n` and on the three leading lambdas is `infoArityOf`). -/
def prodMatcherArityOldOf (go : Expr → Nat → List Nat → Nat → Option Nat) (env : Environment)
    (n : Name) : Option Nat :=
  infoArityOf go (env.find? n)

/-- With a `go` that solves the OLD source equation, the OLD text is the
total `prodMatcherArityT`. -/
theorem oldArity_unique (go : Expr → Nat → List Nat → Nat → Option Nat) (h : OldEq go)
    (env : Environment) (n : Name) :
    prodMatcherArityOldOf go env n = prodMatcherArityT env n :=
  congrArg (fun g : Expr → Nat → List Nat → Nat → Option Nat => infoArityOf g (env.find? n))
    (funext fun e => funext fun s => funext fun v => funext fun d => old_unique go h e s v d)

end Tools.ShippingReaderMatcherArityArray
