import Lean
import Sparkle.Compiler.MachRawSurface

/-! # The machine reader's `projChain`, total

SWITCHED OVER (branch `fix/projchain-total`, ruling of 2026-10-14, second
message, item 6; WRITTEN, NOT BUILT in this form). Record:
`docs/parallel/L-projchain-switch.md`; the earlier records
`docs/parallel/F-reader-unit.md` (the first unit, BUILT) and
`docs/parallel/H-reader-units.md`.

## What changed in this file at the switch

Before, this file DEFINED `prodE`, `tailTy`, `tailAt` and `projChainW` (a
second copy of the compiler's text) and the compiler did not use any of it.
Now the compiler uses them, so they live under `Sparkle/` and NOTHING is
defined twice:

* `prodE`, `tailTy`, `tailAt` are `Sparkle.Compiler.MachProjChain.prodE` /
  `tailTy` / `tailAt` — re-exported below under their old names (aliases:
  the SAME constants, not copies);
* `projChainW` is an abbreviation of the compiler's function itself,
  `Sparkle.Compiler.MachRawSurface.projChain` (no longer `partial`: its text
  is what `projChainW` was — the `do` block with the local `tail` replaced by
  `tailAt tys`);
* `sndE`, `fstE`, `TailEq`, `chainGo`, `projChainT`, `Accepts`, `acceptsB`
  stay here: the compiler does not use them (proof side).

Every theorem below has the statement text it had before the switch.

## The function, before the switch

`Sparkle.Compiler.MachRawSurface.projChain regs tys j last` was a `partial
def` that built the projection `regs.snd^j.fst` (or `regs.snd^j` when
`last`) with the pair types read from `tys`:

    let rec tail : Nat → Option Lean.Expr
      | i => if i + 1 == tys.length - 1 then tys[tys.length - 1]?
        else do
          let a ← tys[i + 1]?
          let b ← tail (i + 1)
          some (mkApp2 (.const ``Prod [.zero, .zero]) a b)
    let mut cur := regs
    for i in [0:j] do
      let a ← tys[i]?
      let b ← tail i
      cur := mkApp3 (.const ``Prod.snd [.zero, .zero]) a b cur
    if last then return cur
    let a ← tys[j]?
    let b ← tail j
    return mkApp3 (.const ``Prod.fst [.zero, .zero]) a b cur

The ONLY recursion was the local `tail` (the `for` is a fold over a range),
and it is why the definition was `partial`: `tail` recurses on `i + 1`, and
that it stops is the fact `tys[i + 1]? = some _` (so `i + 1 < tys.length`),
which the `do` block does not hand to the recursive call. No `Expr` is
inspected, no opaque function of `Lean.Expr` is called.

## What is here

* `tailTy`, `tailAt` (re-exported): the total `tail`.
* `chainGo` / `projChainT`, by structural recursion — the structural form of
  `projChain`. No fuel, no bound on `j` or on the length.
* `projChainW` — the compiler's function (see above).

## The correspondence with the OLD function, and its boundary

The old `partial def` was an opaque constant for the kernel: NO equation
between it and anything could be proved, and none is assumed (no axiom).
What IS proved:

* `tailAt_eq` — `tailAt tys` satisfies the recursion equation of the old
  `tail`, as written (`TailEq`);
* `tail_unique` — EVERY function satisfying that equation is `tailAt tys`.

So the unprovable part is exactly "the old compiled `tail` satisfied its own
source equation" (the meaning of `partial`). The agreement of the compiled
functions is MEASURED by the shadow comparison
(`Tools/ShippingReaderProjChainShadow.lean`, which keeps a verbatim copy of
the old function as `projChainOld`).

## Successful inputs are preserved

`projChainT_some` (a result on the whole range `Accepts`) and
`projChainT_callSite` (a result at every call the reader makes: `rawNode`
calls it with `j < tys.length` and `last = (j + 1 == tys.length)`). The
premise is a length fact only. The same statements about the compiler's
function itself: `Tools/ShippingReaderProjChainReal.lean`. -/
namespace Tools.ShippingReaderProjChain
open Lean

/-! ## The compiler's definitions, under their old names (the same constants) -/

export Sparkle.Compiler.MachProjChain (prodE tailTy tailAt)

/-- `Prod.snd a b cur`. -/
def sndE (a b cur : Expr) : Expr := mkApp3 (.const ``Prod.snd [.zero, .zero]) a b cur

/-- `Prod.fst a b cur`. -/
def fstE (a b cur : Expr) : Expr := mkApp3 (.const ``Prod.fst [.zero, .zero]) a b cur

/-! ## The total `tail` -/

theorem tailTy_nil : tailTy [] = none := rfl

theorem tailTy_one (a : Expr) : tailTy [a] = some a := rfl

theorem tailTy_cons (a b : Expr) (l : List Expr) :
    tailTy (a :: b :: l) = (tailTy (b :: l)).map (prodE a) := rfl

/-- `tailTy` refuses the empty list only. -/
theorem tailTy_cons_some : ∀ (a : Expr) (l : List Expr), ∃ r, tailTy (a :: l) = some r
  | a, [] => ⟨a, rfl⟩
  | a, b :: l =>
    match tailTy_cons_some b l with
    | ⟨r, hr⟩ =>
      ⟨prodE a r, (tailTy_cons a b l).trans (congrArg (Option.map (prodE a)) hr)⟩

/-- The recursion equation of the local `tail` of the compiler's OLD
`projChain` (MachRawSurface.lean 59–64 before the switch; the text is kept
in `Tools/ShippingReaderProjChainShadow.lean`, `projChainOld`), as a property
of a function. The `do` block of the source is these two binds of `Option`. -/
abbrev TailEq (tys : List Expr) (tail : Nat → Option Expr) : Prop :=
  ∀ i : Nat, tail i =
    if i + 1 == tys.length - 1 then tys[tys.length - 1]?
    else (tys[i + 1]?).bind fun a => (tail (i + 1)).bind fun b => some (prodE a b)

/-- What `drop` leaves at a position: nothing (the position is past the end),
or the element there and the rest. -/
theorem drop_cases : ∀ (l : List Expr) (n : Nat),
    (l.drop n = [] ∧ l[n]? = none ∧ l.length ≤ n) ∨
    (∃ a rest, l.drop n = a :: rest ∧ l[n]? = some a ∧ l.drop (n + 1) = rest ∧
      l.length = n + 1 + rest.length)
  | [], n => Or.inl ⟨List.drop_nil, rfl, Nat.zero_le n⟩
  | x :: xs, 0 =>
    Or.inr ⟨x, xs, rfl, rfl, rfl, by
      show xs.length + 1 = 0 + 1 + xs.length
      omega⟩
  | x :: xs, n + 1 =>
    match drop_cases xs n with
    | Or.inl ⟨h1, h2, h3⟩ =>
      Or.inl ⟨h1, h2, by
        show xs.length + 1 ≤ n + 1
        omega⟩
    | Or.inr ⟨a, rest, h1, h2, h3, h4⟩ =>
      Or.inr ⟨a, rest, h1, h2, h3, by
        show xs.length + 1 = n + 1 + 1 + rest.length
        omega⟩

/-- EXISTENCE: the total `tail` satisfies the compiler's equation. -/
theorem tailAt_eq (tys : List Expr) : TailEq tys (tailAt tys) := by
  intro i
  obtain ⟨hd, hg, hl⟩ | ⟨a, rest, hd, hg, hd2, hl⟩ := drop_cases tys (i + 1)
  · -- past the end: both sides are `none`
    have hneg : ¬ ((i + 1 == tys.length - 1) = true) :=
      fun hc => absurd (beq_iff_eq.mp hc) (by omega)
    have h1 : tailAt tys i = none := congrArg tailTy hd
    rw [if_neg hneg, hg]
    all_goals exact h1
  · cases rest with
    | nil =>
      -- the last component
      have hl' : tys.length = i + 1 + 1 + 0 := hl
      have hpos : (i + 1 == tys.length - 1) = true := beq_iff_eq.mpr (by omega)
      have he : tys.length - 1 = i + 1 := by omega
      have h1 : tailAt tys i = some a := congrArg tailTy hd
      rw [if_pos hpos, he, hg]
      all_goals exact h1
    | cons b l =>
      -- a component with more after it
      have hl' : tys.length = i + 1 + 1 + (l.length + 1) := hl
      have hneg : ¬ ((i + 1 == tys.length - 1) = true) :=
        fun hc => absurd (beq_iff_eq.mp hc) (by omega)
      obtain ⟨t, ht⟩ := tailTy_cons_some b l
      have h1 : tailAt tys i = some (prodE a t) :=
        ((congrArg tailTy hd).trans (tailTy_cons a b l)).trans
          (congrArg (Option.map (prodE a)) ht)
      have h2 : tailAt tys (i + 1) = some t := (congrArg tailTy hd2).trans ht
      rw [if_neg hneg, hg, h2]
      all_goals exact h1

/-- UNIQUENESS: a function satisfying the compiler's equation is the total
`tail`. (The equation's recursion is on `tys.length - i`.) -/
theorem tail_unique (tys : List Expr) (tail : Nat → Option Expr) (h : TailEq tys tail) :
    ∀ i : Nat, tail i = tailAt tys i := by
  have key : ∀ (n i : Nat), tys.length - i ≤ n → tail i = tailAt tys i := by
    intro n
    induction n with
    | zero =>
      intro i hn
      have hg : tys[i + 1]? = none := by
        obtain ⟨_, hg, _⟩ | ⟨a, rest, _, _, _, hl⟩ := drop_cases tys (i + 1)
        · exact hg
        · exact absurd hl (by omega)
      rw [h i, tailAt_eq tys i, hg]
      all_goals rfl
    | succ n ih =>
      intro i hn
      have hi : tail (i + 1) = tailAt tys (i + 1) := ih (i + 1) (by omega)
      rw [h i, tailAt_eq tys i, hi]
  intro i
  exact key (tys.length - i) i (Nat.le_refl _)

/-! ## The total `projChain` -/

/-- The loop and the end of `projChain`, on the components not yet passed:
`j` more `snd`s, then (unless `last`) one `fst`. Structural on `j`. -/
def chainGo (last : Bool) (cur : Expr) (ts : List Expr) (j : Nat) : Option Expr :=
  match j with
  | 0 =>
    match last with
    | true => some cur
    | false =>
      match ts with
      | [] => none
      | a :: rest => (tailTy rest).map fun b => fstE a b cur
  | k + 1 =>
    match ts with
    | [] => none
    | a :: rest => (tailTy rest).bind fun b => chainGo last (sndE a b cur) rest k

/-- `projChain` in structural form: structural recursion, no fuel. -/
def projChainT (regs : Expr) (tys : List Expr) (j : Nat) (last : Bool) : Option Expr :=
  chainGo last regs tys j

/-- The compiler's function ITSELF, under the name it had here before the
switch (then: a copy of the compiler's text with its local `tail` replaced
by `tailAt tys`; now the compiler's `projChain` is that text). -/
abbrev projChainW (regs : Lean.Expr) (tys : List Lean.Expr) (j : Nat) (last : Bool) :
    Option Lean.Expr :=
  Sparkle.Compiler.MachRawSurface.projChain regs tys j last

theorem chainGo_zero_true (cur : Expr) (ts : List Expr) :
    chainGo true cur ts 0 = some cur := by
  cases ts <;> rfl

theorem chainGo_zero_false_nil (cur : Expr) : chainGo false cur [] 0 = none := rfl

theorem chainGo_zero_false_cons (cur a : Expr) (rest : List Expr) :
    chainGo false cur (a :: rest) 0 = (tailTy rest).map fun b => fstE a b cur := rfl

theorem chainGo_succ_nil (last : Bool) (cur : Expr) (k : Nat) :
    chainGo last cur [] (k + 1) = none := rfl

theorem chainGo_succ_cons (last : Bool) (cur a : Expr) (rest : List Expr) (k : Nat) :
    chainGo last cur (a :: rest) (k + 1) =
      (tailTy rest).bind fun b => chainGo last (sndE a b cur) rest k := rfl

theorem bind_some' {α β : Type} (t : α) (F : α → Option β) : (some t).bind F = F t := rfl

/-- One step of the loop, when the pair type exists. -/
theorem chainGo_step (last : Bool) (cur a t : Expr) (rest : List Expr) (k : Nat)
    (ht : tailTy rest = some t) :
    chainGo last cur (a :: rest) (k + 1) = chainGo last (sndE a t cur) rest k :=
  (chainGo_succ_cons last cur a rest k).trans
    ((congrArg (fun o : Option Expr => o.bind fun b => chainGo last (sndE a b cur) rest k) ht).trans
      (bind_some' t fun b => chainGo last (sndE a b cur) rest k))

/-- The inputs on which `projChain` returns a result, by reading its text
(`n` the number of component types): with `last`, no projection at all or
`j` `snd`s over at least `j + 1` components; without, `j` `snd`s and a `fst`
over at least `j + 2`. -/
def Accepts : Bool → Nat → Nat → Prop
  | true, n, j => j = 0 ∨ j + 1 ≤ n
  | false, n, j => j + 2 ≤ n

/-- `Accepts`, decided (for the compiled comparison). -/
def acceptsB (last : Bool) (n j : Nat) : Bool :=
  match last with
  | true => j == 0 || decide (j + 1 ≤ n)
  | false => decide (j + 2 ≤ n)

theorem chainGo_true_some : ∀ (j : Nat) (ts : List Expr) (cur : Expr),
    (j = 0 ∨ j + 1 ≤ ts.length) → ∃ r, chainGo true cur ts j = some r
  | 0, ts, cur, _ => ⟨cur, chainGo_zero_true cur ts⟩
  | k + 1, [], _, h => False.elim (by
      have h' : k + 1 = 0 ∨ k + 1 + 1 ≤ 0 := h
      omega)
  | k + 1, [_], _, h => False.elim (by
      have h' : k + 1 = 0 ∨ k + 1 + 1 ≤ 1 := h
      omega)
  | k + 1, a :: b :: l, cur, h =>
    match tailTy_cons_some b l with
    | ⟨t, ht⟩ =>
      match chainGo_true_some k (b :: l) (sndE a t cur) (Or.inr (by
          have h' : k + 1 = 0 ∨ k + 1 + 1 ≤ l.length + 1 + 1 := h
          show k + 1 ≤ l.length + 1
          omega)) with
      | ⟨r, hr⟩ => ⟨r, (chainGo_step true cur a t (b :: l) k ht).trans hr⟩

theorem chainGo_false_some : ∀ (j : Nat) (ts : List Expr) (cur : Expr),
    j + 2 ≤ ts.length → ∃ r, chainGo false cur ts j = some r
  | 0, [], _, h => False.elim (by
      have h' : 0 + 2 ≤ 0 := h
      omega)
  | 0, [_], _, h => False.elim (by
      have h' : 0 + 2 ≤ 1 := h
      omega)
  | 0, a :: b :: l, cur, _ =>
    match tailTy_cons_some b l with
    | ⟨t, ht⟩ =>
      ⟨fstE a t cur, (chainGo_zero_false_cons cur a (b :: l)).trans
        (congrArg (Option.map fun b' => fstE a b' cur) ht)⟩
  | k + 1, [], _, h => False.elim (by
      have h' : k + 1 + 2 ≤ 0 := h
      omega)
  | k + 1, [_], _, h => False.elim (by
      have h' : k + 1 + 2 ≤ 1 := h
      omega)
  | k + 1, a :: b :: l, cur, h =>
    match tailTy_cons_some b l with
    | ⟨t, ht⟩ =>
      match chainGo_false_some k (b :: l) (sndE a t cur) (by
          have h' : k + 1 + 2 ≤ l.length + 1 + 1 := h
          show k + 2 ≤ l.length + 1
          omega) with
      | ⟨r, hr⟩ => ⟨r, (chainGo_step false cur a t (b :: l) k ht).trans hr⟩

/-- SUCCESSFUL INPUTS ARE PRESERVED: the total function returns a result on
the whole range `Accepts`. -/
theorem projChainT_some (regs : Expr) (tys : List Expr) (j : Nat) :
    ∀ (last : Bool), Accepts last tys.length j → ∃ r, projChainT regs tys j last = some r
  | true, h => chainGo_true_some j tys regs h
  | false, h => chainGo_false_some j tys regs h

/-- At every call the reader makes (`rawNode`: component `j` of the `k =
tys.length` a pair matcher binds, `last` for the final one) the total
function returns a result. -/
theorem projChainT_callSite (regs : Expr) (tys : List Expr) (j : Nat) (hj : j < tys.length) :
    ∃ r, projChainT regs tys j (j + 1 == tys.length) = some r := by
  cases hb : (j + 1 == tys.length) with
  | true =>
    exact projChainT_some regs tys j true
      (show j = 0 ∨ j + 1 ≤ tys.length from Or.inr (by omega))
  | false =>
    have hne : j + 1 ≠ tys.length := beq_eq_false_iff_ne.mp hb
    exact projChainT_some regs tys j false
      (show j + 2 ≤ tys.length by omega)

end Tools.ShippingReaderProjChain
