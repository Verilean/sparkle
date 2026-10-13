import Tools.ShippingReaderProjChain

/-! # `projChainW = projChainT`: the range fold of the compiler's text is the structural recursion

WRITTEN, NOT BUILT (par/h-1). NOT wired into the reader; no file under
`Sparkle/` is touched. Record: `docs/parallel/H-reader-units.md`.

Unit 1 (`Tools/ShippingReaderProjChain.lean`) left ONE provable statement
unproved: `projChainW` (the compiler's text of `projChain` with its local
`tail` replaced by the total `tailAt tys`) against `projChainT` (structural
recursion). Both are total definitions. This file proves it:

    projChainW_eq_projChainT :
      projChainW regs tys j last = projChainT regs tys j last

and, with `tail_unique`, the statement for the compiler's text over ANY
function satisfying the recursion equation of its local `tail`:

    projChainP_eq (h : TailEq tys tail) :
      projChainP tail regs tys j last = projChainT regs tys j last

(`projChainP` is the compiler's text with `tail` a parameter.) So the only
item that stays outside the kernel is: "the compiled `partial` `tail`
satisfies its own source equation".

## The route

1. `projChainW_form` — the `do` block is `forIn [0:j] regs (loopBody tys)`
   followed by `finStep`. This is the ONE step that depends on the shape the
   `do` elaborator produces (the new elaborator of this toolchain,
   `Lean/Elab/BuiltinDo/For.lean`: `forIn xs init (fun i s => let cur := s;
   …)` bound to `fun s => let cur := s; …`); it is closed by `rfl`, the
   alternatives after it are other ways to the same statement.
2. `forIn_range_list` — a loop over `[0:j]` is the loop over
   `List.range' 0 j 1` (`Std.Legacy.Range.forIn_eq_forIn_range'` of the core
   library; the range's size `(j - 0 + 1 - 1) / 1` is `j`).
3. `forIn_list_foldO` — a list loop in `Option` whose body always yields is
   the fold `foldO` (`List.forIn_cons`).
4. `loop_chain` — the fold over `range' s k`, followed by `finStep`, is
   `chainGo` on `tys.drop s`: induction on `k`, the case analysis of unit 1's
   `drop_cases` at position `s`.

No `sorry`, no axiom, no `native_decide`. PREDICTED axioms: `propext`,
`Quot.sound` (`omega`, `funext`). -/
namespace Tools.ShippingReaderProjChain
open Lean

/-! ## Small facts about `Option` -/

/-- Two binds, the result built by `g`: the shape of each step of the
compiler's text (`let a ← …; let b ← …; …`). -/
def pair2 {α : Type} (x y : Option Expr) (g : Expr → Expr → α) : Option α :=
  x.bind fun a => y.bind fun b => some (g a b)

theorem pair2_none {α : Type} (y : Option Expr) (g : Expr → Expr → α) :
    pair2 none y g = none := rfl

theorem pair2_some {α : Type} (a : Expr) (y : Option Expr) (g : Expr → Expr → α) :
    pair2 (some a) y g = y.bind fun b => some (g a b) := rfl

theorem pair2_map {α β : Type} (x y : Option Expr) (g : Expr → Expr → α) (k : α → β) :
    pair2 x y (fun a b => k (g a b)) = (pair2 x y g).map k := by
  cases x with
  | none => rfl
  | some a =>
    cases y with
    | none => rfl
    | some b => rfl

theorem bind_some_eq_map {α β : Type} (o : Option α) (g : α → β) :
    (o.bind fun b => some (g b)) = o.map g := by
  cases o with
  | none => rfl
  | some a => rfl

theorem bind_bind_none {α β γ : Type} (o : Option α) (G : α → Option β) (F : β → Option γ)
    (h : o = none) : (o.bind G).bind F = none := by
  subst h
  rfl

theorem bind_bind_some {α β γ : Type} (o : Option α) (c : α) (G : α → Option β)
    (F : β → Option γ) (h : o = some c) : (o.bind G).bind F = (G c).bind F := by
  subst h
  rfl

/-- A yielding step followed by the continuation of a `for` loop. -/
theorem map_yield_bind {β : Type} (o : Option β) (g : β → Option β)
    (k : ForInStep β → Option β) (hk : ∀ d, k (ForInStep.yield d) = g d) :
    ((o.map ForInStep.yield) >>= k) = o.bind g := by
  cases o with
  | none => rfl
  | some d => exact hk d

/-! ## The pieces of the compiler's text -/

/-- The pair at position `s` of the component types, when there is none. -/
theorem pair2_at_none {α : Type} (tys : List Expr) (s : Nat) (g : Expr → Expr → α)
    (hg : tys[s]? = none) : pair2 (tys[s]?) (tailAt tys s) g = none :=
  (congrArg (fun o : Option Expr => pair2 o (tailAt tys s) g) hg).trans
    (pair2_none (tailAt tys s) g)

/-- The pair at position `s` of the component types, when there is one. -/
theorem pair2_at_some {α : Type} (tys : List Expr) (s : Nat) (g : Expr → Expr → α)
    (a : Expr) (rest : List Expr) (hg : tys[s]? = some a) (hd2 : tys.drop (s + 1) = rest) :
    pair2 (tys[s]?) (tailAt tys s) g = (tailTy rest).bind fun b => some (g a b) :=
  ((congrArg (fun o : Option Expr => pair2 o (tailAt tys s) g) hg).trans
    (pair2_some a (tailAt tys s) g)).trans
    (congrArg (fun l : List Expr => (tailTy l).bind fun b => some (g a b)) hd2)

/-- One round of the loop of `projChain`: `cur := Prod.snd tys[i] (tail i) cur`. -/
def sndStep (tys : List Expr) (i : Nat) (cur : Expr) : Option Expr :=
  pair2 (tys[i]?) (tailAt tys i) fun x y => sndE x y cur

/-- The same round as the body of the `for` (it yields the new `cur`). -/
def loopBody (tys : List Expr) (i : Nat) (cur : Expr) : Option (ForInStep Expr) :=
  pair2 (tys[i]?) (tailAt tys i) fun x y => ForInStep.yield (sndE x y cur)

/-- What follows the loop: `cur` itself when `last`, else `Prod.fst tys[j]
(tail j) cur`. -/
def finStep (tys : List Expr) (last : Bool) (j : Nat) (cur : Expr) : Option Expr :=
  if last then some cur
  else pair2 (tys[j]?) (tailAt tys j) fun x y => fstE x y cur

theorem loopBody_eq (tys : List Expr) (i : Nat) (c : Expr) :
    loopBody tys i c = (sndStep tys i c).map ForInStep.yield :=
  pair2_map (tys[i]?) (tailAt tys i) (fun x y => sndE x y c) ForInStep.yield

theorem finStep_true (tys : List Expr) (j : Nat) (cur : Expr) :
    finStep tys true j cur = some cur := rfl

theorem finStep_false (tys : List Expr) (j : Nat) (cur : Expr) :
    finStep tys false j cur = pair2 (tys[j]?) (tailAt tys j) (fun x y => fstE x y cur) := rfl

/-- THE STEP THAT DEPENDS ON THE `do` ELABORATOR: the compiler's text (over
the total `tail`) is the range loop followed by `finStep`. -/
theorem projChainW_form (regs : Expr) (tys : List Expr) (j : Nat) (last : Bool) :
    projChainW regs tys j last =
      (forIn [0:j] regs (loopBody tys) : Option Expr).bind (finStep tys last j) := by
  first
    | rfl
    | (unfold projChainW loopBody finStep pair2 sndE fstE; rfl)
    | (simp only [projChainW, loopBody, finStep, pair2, sndE, fstE, bind, pure]; rfl)
    | (cases last <;> rfl)
    | (cases last <;> simp [projChainW, loopBody, finStep, pair2, sndE, fstE] <;> rfl)

/-! ## The loop is a fold -/

/-- A fold in `Option` over a list of indices: the loop without `forIn`. -/
def foldO {β : Type} (step : Nat → β → Option β) : List Nat → β → Option β
  | [], c => some c
  | i :: is, c => (step i c).bind (foldO step is)

theorem foldO_nil {β : Type} (step : Nat → β → Option β) (c : β) :
    foldO step [] c = some c := rfl

theorem foldO_cons {β : Type} (step : Nat → β → Option β) (i : Nat) (is : List Nat) (c : β) :
    foldO step (i :: is) c = (step i c).bind (foldO step is) := rfl

/-- A loop over `[0:j]` is the loop over the list `range' 0 j`. -/
theorem forIn_range_list {β : Type} (j : Nat) (init : β)
    (f : Nat → β → Option (ForInStep β)) :
    (forIn [0:j] init f : Option β) = forIn (List.range' 0 j 1) init f := by
  have h := Std.Legacy.Range.forIn_eq_forIn_range' [0:j] init f
  have hs : (j - 0 + 1 - 1) / 1 = j := by omega
  first
    | exact h.trans (congrArg (fun n => (forIn (List.range' 0 n 1) init f : Option β)) hs)
    | (simp only [Std.Legacy.Range.size] at h; rw [hs] at h; exact h)
    | (simp at h; exact h)
    | (simpa using h)

/-- A list loop in `Option` whose body always yields is the fold. -/
theorem forIn_list_foldO {β : Type} (step : Nat → β → Option β)
    (f : Nat → β → Option (ForInStep β))
    (hf : ∀ i c, f i c = (step i c).map ForInStep.yield) :
    ∀ (l : List Nat) (c : β), (forIn l c f : Option β) = foldO step l c
  | [], c => by
    first
      | rfl
      | exact List.forIn_nil
      | simp [foldO]
  | i :: is, c => by
    have ih := forIn_list_foldO step f hf is
    first
      | (rw [List.forIn_cons, hf i c, foldO_cons]
         apply map_yield_bind (step i c) (foldO step is)
         intro d
         exact ih d)
      | (simp only [List.forIn_cons, hf i c, foldO_cons]
         apply map_yield_bind (step i c) (foldO step is)
         intro d
         exact ih d)
      | (rw [List.forIn_cons, hf i c, foldO_cons]
         cases step i c with
         | none => rfl
         | some d => exact ih d)

/-! ## The fold is the structural recursion -/

theorem range'_succ1 (s k : Nat) :
    List.range' s (k + 1) 1 = s :: List.range' (s + 1) k 1 := by
  first
    | rfl
    | exact List.range'_succ

/-- After the loop: `finStep` at position `s` is `chainGo` with no round left. -/
theorem finStep_chain (tys : List Expr) (last : Bool) (s : Nat) (cur : Expr) :
    finStep tys last s cur = chainGo last cur (tys.drop s) 0 := by
  cases last with
  | true => exact (finStep_true tys s cur).trans (chainGo_zero_true cur (tys.drop s)).symm
  | false =>
    obtain ⟨hd, hg, _⟩ | ⟨a, rest, hd, hg, hd2, _⟩ := drop_cases tys s
    · have l : finStep tys false s cur = none :=
        (finStep_false tys s cur).trans
          (pair2_at_none tys s (fun x y => fstE x y cur) hg)
      have r : chainGo false cur (tys.drop s) 0 = none :=
        (congrArg (fun l : List Expr => chainGo false cur l 0) hd).trans
          (chainGo_zero_false_nil cur)
      exact l.trans r.symm
    · have l : finStep tys false s cur = (tailTy rest).bind fun b => some (fstE a b cur) :=
        (finStep_false tys s cur).trans
          (pair2_at_some tys s (fun x y => fstE x y cur) a rest hg hd2)
      have r : chainGo false cur (tys.drop s) 0 = (tailTy rest).map fun b => fstE a b cur :=
        (congrArg (fun l : List Expr => chainGo false cur l 0) hd).trans
          (chainGo_zero_false_cons cur a rest)
      exact l.trans ((bind_some_eq_map (tailTy rest) (fun b => fstE a b cur)).trans r.symm)

/-- The fold over the positions `s, s + 1, …, s + k - 1`, then `finStep` at
`s + k`, is `chainGo` on the component types from position `s`. -/
theorem loop_chain (tys : List Expr) (last : Bool) :
    ∀ (k s : Nat) (cur : Expr),
      (foldO (sndStep tys) (List.range' s k 1) cur).bind (finStep tys last (s + k)) =
        chainGo last cur (tys.drop s) k
  | 0, s, cur =>
    (show (foldO (sndStep tys) (List.range' s 0 1) cur).bind (finStep tys last (s + 0)) =
        finStep tys last s cur from rfl).trans (finStep_chain tys last s cur)
  | k + 1, s, cur => by
    have ih := loop_chain tys last k (s + 1)
    have hn : s + 1 + k = s + (k + 1) := by omega
    rw [hn] at ih
    have hfold : foldO (sndStep tys) (List.range' s (k + 1) 1) cur =
        (sndStep tys s cur).bind (foldO (sndStep tys) (List.range' (s + 1) k 1)) :=
      (congrArg (fun l : List Nat => foldO (sndStep tys) l cur) (range'_succ1 s k)).trans
        (foldO_cons (sndStep tys) s (List.range' (s + 1) k 1) cur)
    obtain ⟨hd, hg, _⟩ | ⟨a, rest, hd, hg, hd2, _⟩ := drop_cases tys s
    · -- no component at position `s`: both sides are `none`
      have e1 : sndStep tys s cur = none :=
        pair2_at_none tys s (fun x y => sndE x y cur) hg
      have l : (foldO (sndStep tys) (List.range' s (k + 1) 1) cur).bind
            (finStep tys last (s + (k + 1))) = none :=
        (congrArg (fun o : Option Expr => o.bind (finStep tys last (s + (k + 1)))) hfold).trans
          (bind_bind_none (sndStep tys s cur) (foldO (sndStep tys) (List.range' (s + 1) k 1))
            (finStep tys last (s + (k + 1))) e1)
      have r : chainGo last cur (tys.drop s) (k + 1) = none :=
        (congrArg (fun l : List Expr => chainGo last cur l (k + 1)) hd).trans
          (chainGo_succ_nil last cur k)
      exact l.trans r.symm
    · have e1 : sndStep tys s cur = (tailTy rest).bind fun b => some (sndE a b cur) :=
        pair2_at_some tys s (fun x y => sndE x y cur) a rest hg hd2
      have r0 : chainGo last cur (tys.drop s) (k + 1) =
          (tailTy rest).bind fun b => chainGo last (sndE a b cur) rest k :=
        (congrArg (fun l : List Expr => chainGo last cur l (k + 1)) hd).trans
          (chainGo_succ_cons last cur a rest k)
      cases ht : tailTy rest with
      | none =>
        -- the pair type does not exist: both sides are `none`
        have e2 : sndStep tys s cur = none :=
          e1.trans (congrArg (fun o : Option Expr => o.bind fun b => some (sndE a b cur)) ht)
        have l : (foldO (sndStep tys) (List.range' s (k + 1) 1) cur).bind
              (finStep tys last (s + (k + 1))) = none :=
          (congrArg (fun o : Option Expr => o.bind (finStep tys last (s + (k + 1)))) hfold).trans
            (bind_bind_none (sndStep tys s cur) (foldO (sndStep tys) (List.range' (s + 1) k 1))
              (finStep tys last (s + (k + 1))) e2)
        have r : chainGo last cur (tys.drop s) (k + 1) = none :=
          r0.trans (congrArg
            (fun o : Option Expr => o.bind fun b => chainGo last (sndE a b cur) rest k) ht)
        exact l.trans r.symm
      | some t =>
        -- one round on both sides, then the induction hypothesis at `s + 1`
        have e2 : sndStep tys s cur = some (sndE a t cur) :=
          e1.trans (congrArg (fun o : Option Expr => o.bind fun b => some (sndE a b cur)) ht)
        have l : (foldO (sndStep tys) (List.range' s (k + 1) 1) cur).bind
              (finStep tys last (s + (k + 1))) =
            (foldO (sndStep tys) (List.range' (s + 1) k 1) (sndE a t cur)).bind
              (finStep tys last (s + (k + 1))) :=
          (congrArg (fun o : Option Expr => o.bind (finStep tys last (s + (k + 1)))) hfold).trans
            (bind_bind_some (sndStep tys s cur) (sndE a t cur)
              (foldO (sndStep tys) (List.range' (s + 1) k 1))
              (finStep tys last (s + (k + 1))) e2)
        have r : chainGo last cur (tys.drop s) (k + 1) = chainGo last (sndE a t cur) rest k :=
          r0.trans (congrArg
            (fun o : Option Expr => o.bind fun b => chainGo last (sndE a b cur) rest k) ht)
        have ih' := ih (sndE a t cur)
        rw [hd2] at ih'
        exact l.trans (ih'.trans r.symm)

/-! ## The statements -/

/-- **The compiler's text over the total `tail` is the structural
definition.** Both sides are total; this is a kernel equation. -/
theorem projChainW_eq_projChainT (regs : Expr) (tys : List Expr) (j : Nat) (last : Bool) :
    projChainW regs tys j last = projChainT regs tys j last := by
  have h1 := projChainW_form regs tys j last
  have h2 : (forIn [0:j] regs (loopBody tys) : Option Expr) =
      foldO (sndStep tys) (List.range' 0 j 1) regs :=
    (forIn_range_list j regs (loopBody tys)).trans
      (forIn_list_foldO (sndStep tys) (loopBody tys) (loopBody_eq tys) (List.range' 0 j 1) regs)
  have h3 := loop_chain tys last j 0 regs
  have h0 : 0 + j = j := Nat.zero_add j
  rw [h0] at h3
  have h4 : chainGo last regs (tys.drop 0) j = projChainT regs tys j last := rfl
  exact h1.trans
    ((congrArg (fun o : Option Expr => o.bind (finStep tys last j)) h2).trans (h3.trans h4))

/-- The compiler's text of `projChain` with its local `tail` a PARAMETER
(MachRawSurface.lean 65–73; nothing else changed). -/
def projChainP (tail : Nat → Option Lean.Expr) (regs : Lean.Expr) (tys : List Lean.Expr)
    (j : Nat) (last : Bool) : Option Lean.Expr := do
  let mut cur := regs
  for i in [0:j] do
    let a ← tys[i]?
    let b ← tail i
    cur := mkApp3 (.const ``Prod.snd [.zero, .zero]) a b cur
  if last then return cur
  let a ← tys[j]?
  let b ← tail j
  return mkApp3 (.const ``Prod.fst [.zero, .zero]) a b cur

theorem projChainP_tailAt (regs : Expr) (tys : List Expr) (j : Nat) (last : Bool) :
    projChainP (tailAt tys) regs tys j last = projChainW regs tys j last := by
  first
    | rfl
    | (unfold projChainP projChainW; rfl)

/-- **The compiler's text over ANY solution of its `tail` equation is the
structural definition.** What is left outside the kernel is exactly the
premise at the compiled `partial` `tail`: that it satisfies its own source
equation (`TailEq`). -/
theorem projChainP_eq (tail : Nat → Option Expr) (regs : Expr) (tys : List Expr) (j : Nat)
    (last : Bool) (h : TailEq tys tail) :
    projChainP tail regs tys j last = projChainT regs tys j last :=
  (congrArg (fun tl : Nat → Option Expr => projChainP tl regs tys j last)
    (funext (tail_unique tys tail h))).trans
    ((projChainP_tailAt regs tys j last).trans (projChainW_eq_projChainT regs tys j last))

/-- Success at every call the reader makes, for the compiler's text over any
solution of the `tail` equation. -/
theorem projChainP_callSite (tail : Nat → Option Expr) (regs : Expr) (tys : List Expr)
    (j : Nat) (h : TailEq tys tail) (hj : j < tys.length) :
    ∃ r, projChainP tail regs tys j (j + 1 == tys.length) = some r :=
  match projChainT_callSite regs tys j hj with
  | ⟨r, hr⟩ => ⟨r, (projChainP_eq tail regs tys j (j + 1 == tys.length) h).trans hr⟩

end Tools.ShippingReaderProjChain
