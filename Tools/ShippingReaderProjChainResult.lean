import Tools.ShippingReaderProjChainReal

/-! # The exact result of the compiler's `projChain`, and where it has none

WRITTEN, NOT BUILT (branch `fix/projchain-total`; record:
`docs/parallel/L-projchain-switch.md`). No `sorry`, no axiom, no
`native_decide`. Nothing depends on this file (it is separate from
`Tools/ShippingReaderProjChainReal.lean` so that a proof that fails here
does not take the equation and the call-site theorem with it).

`projChain regs tys j last` is `regs.snd^j` (when `last`) or
`regs.snd^j.fst`, each projection carrying its two type arguments. Here the
result is written out as an expression, without `Option`:

* `pairTy a l`     — the right-nested pair type of the non-empty list
                     `a :: l` (`tailTy (a :: l) = some (pairTy a l)`);
* `sndsE ts j cur` — `cur` under `j` `snd`s over the component types `ts`.

About the compiler's function itself:

    projChain_last_eq     (h : j = 0 ∨ j + 1 ≤ tys.length) :
      projChain regs tys j true = some (sndsE tys j regs)
    projChain_notLast_eq  (h : tys.drop j = a :: b :: l) :
      projChain regs tys j false = some (fstE a (pairTy b l) (sndsE tys j regs))
    projChain_none        : ¬ Accepts last tys.length j → projChain regs tys j last = none
    projChain_isSome_iff  : (projChain regs tys j last).isSome = true ↔ Accepts last tys.length j

So `Accepts` (stated by READING the old text in the first unit) is exactly
the set of inputs on which the compiler's function now returns a result —
a theorem about the function the compiler runs, where before the grid of
the shadow comparison measured it (`isSome == acceptsB`).

PREDICTED axioms: `propext`, `Classical.choice`, `Quot.sound`
(`projChain_isSome_iff` uses `Classical.byContradiction`; the others inherit
those of `projChainW_eq_projChainT`). -/
namespace Tools.ShippingReaderProjChainResult
open Lean
open Tools.ShippingReaderProjChain
open Tools.ShippingReaderProjChainReal
open Sparkle.Compiler.MachRawSurface (projChain)

/-- The right-nested pair type of the non-empty list `a :: l`, as an
expression. -/
def pairTy : Expr → List Expr → Expr
  | a, [] => a
  | a, b :: l => prodE a (pairTy b l)

theorem pairTy_one (a : Expr) : pairTy a [] = a := rfl

theorem pairTy_cons (a b : Expr) (l : List Expr) :
    pairTy a (b :: l) = prodE a (pairTy b l) := rfl

/-- `tailTy` on a non-empty list is `pairTy`. -/
theorem tailTy_pairTy : ∀ (a : Expr) (l : List Expr), tailTy (a :: l) = some (pairTy a l)
  | a, [] => rfl
  | a, b :: l =>
    show tailTy (a :: b :: l) = some (prodE a (pairTy b l)) from
      (tailTy_cons a b l).trans (congrArg (Option.map (prodE a)) (tailTy_pairTy b l))

/-- `cur` under `j` `snd`s over the component types `ts` (as far as there
are two components left). -/
def sndsE : List Expr → Nat → Expr → Expr
  | [], _, cur => cur
  | _ :: _, 0, cur => cur
  | a :: rest, k + 1, cur =>
    match rest with
    | [] => cur
    | b :: l => sndsE rest k (sndE a (pairTy b l) cur)

theorem sndsE_zero (ts : List Expr) (cur : Expr) : sndsE ts 0 cur = cur := by
  cases ts <;> rfl

theorem sndsE_succ (a b : Expr) (l : List Expr) (k : Nat) (cur : Expr) :
    sndsE (a :: b :: l) (k + 1) cur = sndsE (b :: l) k (sndE a (pairTy b l) cur) := rfl

/-! ## The structural form: exact results -/

theorem chainGo_true_eq : ∀ (j : Nat) (ts : List Expr) (cur : Expr),
    (j = 0 ∨ j + 1 ≤ ts.length) → chainGo true cur ts j = some (sndsE ts j cur)
  | 0, ts, cur, _ =>
    (chainGo_zero_true cur ts).trans (congrArg some (sndsE_zero ts cur).symm)
  | k + 1, [], _, h => False.elim (by
      have h' : k + 1 = 0 ∨ k + 1 + 1 ≤ 0 := h
      omega)
  | k + 1, [_], _, h => False.elim (by
      have h' : k + 1 = 0 ∨ k + 1 + 1 ≤ 1 := h
      omega)
  | k + 1, a :: b :: l, cur, h =>
    (chainGo_step true cur a (pairTy b l) (b :: l) k (tailTy_pairTy b l)).trans
      ((chainGo_true_eq k (b :: l) (sndE a (pairTy b l) cur) (Or.inr (by
          have h' : k + 1 = 0 ∨ k + 1 + 1 ≤ l.length + 1 + 1 := h
          show k + 1 ≤ l.length + 1
          omega))).trans
        (congrArg some (sndsE_succ a b l k cur).symm))

theorem chainGo_false_eq : ∀ (j : Nat) (ts : List Expr) (cur a b : Expr) (l : List Expr),
    ts.drop j = a :: b :: l →
    chainGo false cur ts j = some (fstE a (pairTy b l) (sndsE ts j cur))
  | 0, ts, cur, a, b, l, h => by
    have h' : ts = a :: b :: l := by
      first
        | exact h
        | simpa using h
    subst h'
    exact (chainGo_zero_false_cons cur a (b :: l)).trans
      (congrArg (Option.map fun b' => fstE a b' cur) (tailTy_pairTy b l))
  | k + 1, [], _, a, b, l, h => by
    have h' : ([] : List Expr) = a :: b :: l := by
      first
        | exact h
        | simpa using h
    cases h'
  | k + 1, [_], _, a, b, l, h => by
    have h' : ([] : List Expr).drop k = a :: b :: l := h
    rw [List.drop_nil] at h'
    cases h'
  | k + 1, x :: y :: m, cur, a, b, l, h =>
    (chainGo_step false cur x (pairTy y m) (y :: m) k (tailTy_pairTy y m)).trans
      ((chainGo_false_eq k (y :: m) (sndE x (pairTy y m) cur) a b l h).trans
        (congrArg (fun c : Expr => some (fstE a (pairTy b l) c)) (sndsE_succ x y m k cur).symm))

/-! ## The structural form: where there is no result -/

theorem chainGo_true_none : ∀ (j : Nat) (ts : List Expr) (cur : Expr),
    ¬ (j = 0 ∨ j + 1 ≤ ts.length) → chainGo true cur ts j = none
  | 0, _, _, h => False.elim (h (Or.inl rfl))
  | k + 1, [], cur, _ => chainGo_succ_nil true cur k
  | k + 1, [a], cur, _ => by
    first
      | rfl
      | exact chainGo_succ_cons true cur a [] k
  | k + 1, a :: b :: l, cur, h =>
    (chainGo_step true cur a (pairTy b l) (b :: l) k (tailTy_pairTy b l)).trans
      (chainGo_true_none k (b :: l) (sndE a (pairTy b l) cur) (fun h' => h (Or.inr (by
        have h'' : k = 0 ∨ k + 1 ≤ l.length + 1 := h'
        show k + 1 + 1 ≤ l.length + 1 + 1
        omega))))

theorem chainGo_false_none : ∀ (j : Nat) (ts : List Expr) (cur : Expr),
    ¬ (j + 2 ≤ ts.length) → chainGo false cur ts j = none
  | 0, [], cur, _ => chainGo_zero_false_nil cur
  | 0, [a], cur, _ => by
    first
      | rfl
      | exact chainGo_zero_false_cons cur a []
  | 0, _ :: _ :: l, _, h => absurd (show 0 + 2 ≤ l.length + 1 + 1 by omega) h
  | k + 1, [], cur, _ => chainGo_succ_nil false cur k
  | k + 1, [a], cur, _ => by
    first
      | rfl
      | exact chainGo_succ_cons false cur a [] k
  | k + 1, a :: b :: l, cur, h =>
    (chainGo_step false cur a (pairTy b l) (b :: l) k (tailTy_pairTy b l)).trans
      (chainGo_false_none k (b :: l) (sndE a (pairTy b l) cur) (fun h' => h (by
        have h'' : k + 2 ≤ l.length + 1 := h'
        show k + 1 + 2 ≤ l.length + 1 + 1
        omega)))

/-! ## The compiler's function -/

/-- The last component: `regs` under `j` `snd`s. -/
theorem projChain_last_eq (regs : Expr) (tys : List Expr) (j : Nat)
    (h : j = 0 ∨ j + 1 ≤ tys.length) :
    projChain regs tys j true = some (sndsE tys j regs) :=
  (projChain_eq_projChainT regs tys j true).trans (chainGo_true_eq j tys regs h)

/-- A component that is not the last: `regs` under `j` `snd`s, then `fst`,
typed by component `j` and the pair type of the components after it. -/
theorem projChain_notLast_eq (regs : Expr) (tys : List Expr) (j : Nat) (a b : Expr)
    (l : List Expr) (h : tys.drop j = a :: b :: l) :
    projChain regs tys j false = some (fstE a (pairTy b l) (sndsE tys j regs)) :=
  (projChain_eq_projChainT regs tys j false).trans (chainGo_false_eq j tys regs a b l h)

/-- Outside `Accepts` the compiler's function returns nothing. -/
theorem projChain_none (regs : Expr) (tys : List Expr) (j : Nat) :
    ∀ (last : Bool), ¬ Accepts last tys.length j → projChain regs tys j last = none
  | true, h => (projChain_eq_projChainT regs tys j true).trans (chainGo_true_none j tys regs h)
  | false, h => (projChain_eq_projChainT regs tys j false).trans (chainGo_false_none j tys regs h)

/-- **`Accepts` is exactly where the compiler's function returns a result.** -/
theorem projChain_isSome_iff (regs : Expr) (tys : List Expr) (j : Nat) (last : Bool) :
    (projChain regs tys j last).isSome = true ↔ Accepts last tys.length j :=
  ⟨fun hs => Classical.byContradiction fun hn =>
      have e : (projChain regs tys j last).isSome = false :=
        (congrArg Option.isSome (projChain_none regs tys j last hn)).trans
          (show (none : Option Expr).isSome = false from rfl)
      absurd (e.symm.trans hs) (by decide),
    fun h =>
      match projChain_some regs tys j last h with
      | ⟨r, hr⟩ =>
        (congrArg Option.isSome hr).trans (show (some r).isSome = true from rfl)⟩

end Tools.ShippingReaderProjChainResult
