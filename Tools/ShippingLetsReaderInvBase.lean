import Tools.ShippingLetsAliasInv
import Tools.ShippingReaderFuelR1
import Tools.ShippingReaderMatcherArityArray

/-! # Unit LC3 (base): the range predicate `LetOk`, the let-binder range lemmas, the hypotheses

BUILT: lc3a3 exit 0 (Tools.ShippingLetsReaderInvBase); audit lc3g1 exit 0. No `sorry`, no axiom, no `native_decide`.

`LetOk n e`: every `_machLet j` placeholder that OCCURS in `e` has `j < n`. This is the deep form of the
range condition (not only the head of `e`): a reader result is a compound expression, and a projection /
`bundleIota` can return one of its components, so the head-only form is not inductive.

This file holds what the joint invariant of the reader twin (`Tools/ShippingLetsReaderInv.lean`) is built
from: the predicate and its closure lemmas, the range behaviour of `machBindLet` / `machBindLetNamed` /
`machBindLetAlias` / `machLetIndex` (new size ≥ old size; the returned placeholder is `v'` or
`machLet j` with `j` below the NEW size), the state invariant `RdOk`, and the record `PureFacts` of the
facts about functions the twin calls but which are `partial` / `extern` (so they cannot be unfolded).

The record `PureFacts` is a HYPOTHESIS of the joint theorem, never an axiom; each field is a statement
that the function does not invent a `_machLet j` placeholder. -/
namespace Tools.ShippingLetsReaderInv
open Lean Sparkle.Compiler.Elab
open Tools.ShippingLetsAliasInv Tools.ShippingReaderFuel
open Tools.ShippingReaderMatcherArity Tools.ShippingReaderMatcherArityArray

/-! ## The range predicate -/

/-- The index of a `_machLet` placeholder. -/
def letFv : FVarId → Option Nat
  | ⟨.num (.str .anonymous "_machLet") j⟩ => some j
  | _ => none

/-- Every `_machLet j` occurring in `e` has `j < n`. -/
def LetOk (n : Nat) : Lean.Expr → Bool
  | .fvar id => match letFv id with
    | some j => decide (j < n)
    | none => true
  | .app f a => LetOk n f && LetOk n a
  | .lam _ t b _ => LetOk n t && LetOk n b
  | .forallE _ t b _ => LetOk n t && LetOk n b
  | .letE _ t v b _ => LetOk n t && LetOk n v && LetOk n b
  | .mdata _ e => LetOk n e
  | .proj _ _ e => LetOk n e
  | _ => true

theorem letOk_machLet (n j : Nat) : LetOk n (machLet j) = decide (j < n) := rfl

theorem letOk_lt {n j : Nat} {e : Lean.Expr} (h : LetOk n e = true) (he : e = machLet j) : j < n := by
  subst he
  rw [letOk_machLet] at h
  exact of_decide_eq_true h

theorem letOk_app {n : Nat} {f a : Lean.Expr} :
    LetOk n (.app f a) = true ↔ LetOk n f = true ∧ LetOk n a = true := by
  simp [LetOk]

theorem letOk_mono {n m : Nat} (h : n ≤ m) : ∀ e : Lean.Expr, LetOk n e = true → LetOk m e = true
  | .bvar _, _ => rfl
  | .fvar id, he => by
    cases hl : letFv id with
    | none => simp [LetOk, hl]
    | some j =>
      simp [LetOk, hl] at he ⊢
      omega
  | .mvar _, _ => rfl
  | .sort _, _ => rfl
  | .const _ _, _ => rfl
  | .lit _, _ => rfl
  | .app f a, he => by
    simp only [LetOk, Bool.and_eq_true] at he ⊢
    exact ⟨letOk_mono h f he.1, letOk_mono h a he.2⟩
  | .lam _ t b _, he => by
    simp only [LetOk, Bool.and_eq_true] at he ⊢
    exact ⟨letOk_mono h t he.1, letOk_mono h b he.2⟩
  | .forallE _ t b _, he => by
    simp only [LetOk, Bool.and_eq_true] at he ⊢
    exact ⟨letOk_mono h t he.1, letOk_mono h b he.2⟩
  | .letE _ t v b _, he => by
    simp only [LetOk, Bool.and_eq_true] at he ⊢
    exact ⟨⟨letOk_mono h t he.1.1, letOk_mono h v he.1.2⟩, letOk_mono h b he.2⟩
  | .mdata _ e, he => by
    simp only [LetOk] at he ⊢
    exact letOk_mono h e he
  | .proj _ _ e, he => by
    simp only [LetOk] at he ⊢
    exact letOk_mono h e he

theorem letOk_zero {n : Nat} {e : Lean.Expr} (h : LetOk 0 e = true) : LetOk n e = true :=
  letOk_mono (Nat.zero_le n) e h

/-- Placeholders other than `_machLet` are not constrained. -/
theorem letOk_slot (n i : Nat) : LetOk n (machSlot i) = true := by
  simp [LetOk, machSlot, letFv]

theorem letOk_in (n i : Nat) : LetOk n (machIn i) = true := by
  simp [LetOk, machIn, letFv]

theorem letOk_inst (n i : Nat) : LetOk n (machInstOut i) = true := by
  simp [LetOk, machInstOut, letFv]

theorem letOk_natLit (n k : Nat) : LetOk n (inlNatLit k) = true := by
  simp [LetOk, inlNatLit, mkApp3, mkApp, mkAppB]

/-! ## Spines and arrays -/

theorem ok_spine (n : Nat) (e : Lean.Expr) : ∀ (acc : List Lean.Expr), LetOk n e = true →
    (∀ a ∈ acc, LetOk n a = true) →
    LetOk n (inlSpine e acc).1 = true ∧ ∀ a ∈ (inlSpine e acc).2, LetOk n a = true := by
  induction e with
  | app f a ihf iha =>
    intro acc he hacc
    simp only [LetOk, Bool.and_eq_true] at he
    have := ihf (a :: acc) he.1 (by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact he.2
      · exact hacc x hx)
    simpa only [inlSpine] using this
  | _ =>
    intro acc he hacc
    simp only [inlSpine]
    exact ⟨he, hacc⟩

theorem ok_headT (n : Nat) : ∀ e : Lean.Expr, LetOk n e = true → LetOk n (headT e) = true
  | .app f a, he => by
    simp only [LetOk, Bool.and_eq_true] at he
    simpa only [headT] using ok_headT n f he.1
  | .bvar _, he => he
  | .fvar _, he => he
  | .mvar _, he => he
  | .sort _, he => he
  | .const _ _, he => he
  | .lit _, he => he
  | .lam _ _ _ _, he => he
  | .forallE _ _ _ _, he => he
  | .letE _ _ _ _ _, he => he
  | .mdata _ _, he => he
  | .proj _ _ _, he => he

theorem ok_argsAcc (n : Nat) : ∀ (e : Lean.Expr) (acc : List Lean.Expr), LetOk n e = true →
    (∀ a ∈ acc, LetOk n a = true) → ∀ a ∈ argsAcc e acc, LetOk n a = true
  | .app f a, acc, he, hacc => by
    simp only [LetOk, Bool.and_eq_true] at he
    refine ok_argsAcc n f (a :: acc) he.1 ?_
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact he.2
    · exact hacc x hx
  | .bvar _, _, _, hacc => hacc
  | .fvar _, _, _, hacc => hacc
  | .mvar _, _, _, hacc => hacc
  | .sort _, _, _, hacc => hacc
  | .const _ _, _, _, hacc => hacc
  | .lit _, _, _, hacc => hacc
  | .lam _ _ _ _, _, _, hacc => hacc
  | .forallE _ _ _ _, _, _, hacc => hacc
  | .letE _ _ _ _ _, _, _, hacc => hacc
  | .mdata _ _, _, _, hacc => hacc
  | .proj _ _ _, _, _, hacc => hacc

theorem ok_getAppFn {n : Nat} {e : Lean.Expr} (he : LetOk n e = true) :
    LetOk n e.getAppFn = true := by
  rw [← headT_eq_getAppFn]
  exact ok_headT n e he

theorem ok_getAppArgs {n : Nat} {e : Lean.Expr} (he : LetOk n e = true) :
    ∀ a ∈ e.getAppArgs, LetOk n a = true := by
  intro a ha
  rw [getAppArgs_eq] at ha
  exact ok_argsAcc n e [] he (by simp) a (Array.mem_toArray.mp ha)

theorem ok_foldl_app {n : Nat} : ∀ (l : List Lean.Expr) (f : Lean.Expr), LetOk n f = true →
    (∀ a ∈ l, LetOk n a = true) → LetOk n (l.foldl Lean.Expr.app f) = true
  | [], _, hf, _ => hf
  | a :: l, f, hf, hl => by
    refine ok_foldl_app l (.app f a) ?_ (fun x hx => hl x (List.mem_cons_of_mem _ hx))
    simp only [LetOk, Bool.and_eq_true]
    exact ⟨hf, hl a List.mem_cons_self⟩

theorem ok_mkAppN {n : Nat} {f : Lean.Expr} {as : Array Lean.Expr} (hf : LetOk n f = true)
    (has : ∀ a ∈ as, LetOk n a = true) : LetOk n (mkAppN f as) = true := by
  unfold mkAppN
  rw [← Array.foldl_toList]
  exact ok_foldl_app as.toList f hf (fun a ha => has a (Array.mem_toList_iff.mp ha))

/-- The out-of-range default of `a[i]!`. -/
theorem ok_getElem! {n : Nat} {a : Array Lean.Expr} (h : ∀ x ∈ a, LetOk n x = true) (i : Nat) :
    LetOk n a[i]! = true := by
  by_cases hi : i < a.size
  · rw [getElem!_pos a i hi]
    exact h _ (Array.getElem_mem hi)
  · rw [getElem!_neg a i hi]
    rfl

/-! ## Environments and the reader state -/

/-- Every converted value the environment holds is in range. -/
def EnvOk (n : Nat) (env : List MachVal) : Prop :=
  ∀ v, MachVal.val v ∈ env → LetOk n v = true

theorem envOk_mono {n m : Nat} (h : n ≤ m) {env : List MachVal} (H : EnvOk n env) : EnvOk m env :=
  fun v hv => letOk_mono h v (H v hv)

theorem envOk_cons {n : Nat} {env : List MachVal} {x : MachVal} (H : EnvOk n env)
    (hx : ∀ v, x = MachVal.val v → LetOk n v = true) : EnvOk n (x :: env) := by
  intro v hv
  rcases List.mem_cons.mp hv with h | h
  · exact hx v h.symm
  · exact H v h

/-- A machine value is in range. -/
def MvOk (n : Nat) : MachVal → Prop
  | .val e => LetOk n e = true
  | _ => True

/-- **The state invariant**: the `let`s have no `let` as a value (`NoLetAlias`), and the converted
expressions the state keeps (the nested machines' results, the domain) are in range. -/
def RdOk (st : MachRead) : Prop :=
  NoLetAlias st.lets ∧
  (∀ x ∈ st.nested.toList, LetOk st.lets.size x.2.2.2.2.2 = true) ∧
  (∀ d, st.dom = some d → LetOk st.lets.size d = true)

/-- A step from `st` to `st'`: the invariant holds again and the `let` table did not shrink. -/
def Adv (st st' : MachRead) : Prop := RdOk st' ∧ st.lets.size ≤ st'.lets.size

theorem rdOk_init : RdOk ({} : MachRead) := by
  refine ⟨noLetAlias_empty, ?_, ?_⟩
  · intro x hx
    simp at hx
  · intro d hd
    cases hd

theorem adv_refl {st : MachRead} (h : RdOk st) : Adv st st := ⟨h, Nat.le_refl _⟩

theorem adv_trans {a b c : MachRead} (h1 : Adv a b) (h2 : Adv b c) : Adv a c :=
  ⟨h2.1, Nat.le_trans h1.2 h2.2⟩

theorem rdOk_congr {st st' : MachRead} (H : RdOk st) (h1 : st'.lets = st.lets)
    (h2 : st'.nested = st.nested) (h3 : st'.dom = st.dom) : RdOk st' := by
  obtain ⟨a, b, c⟩ := H
  refine ⟨?_, ?_, ?_⟩
  · rw [h1]; exact a
  · rw [h1, h2]; exact b
  · rw [h1, h3]; exact c

theorem adv_congr {s0 st st' : MachRead} (H : Adv s0 st) (h1 : st'.lets = st.lets)
    (h2 : st'.nested = st.nested) (h3 : st'.dom = st.dom) : Adv s0 st' := by
  refine ⟨rdOk_congr H.1 h1 h2 h3, ?_⟩
  rw [h1]; exact H.2

/-- A different table: still alias-free and not shorter. -/
theorem rdOk_lets {st st' : MachRead} (H : RdOk st) (hn : NoLetAlias st'.lets)
    (hs : st.lets.size ≤ st'.lets.size) (h2 : st'.nested = st.nested) (h3 : st'.dom = st.dom) :
    RdOk st' := by
  obtain ⟨_, b, c⟩ := H
  refine ⟨hn, ?_, ?_⟩
  · rw [h2]; intro x hx; exact letOk_mono hs _ (b x hx)
  · rw [h3]; intro d hd; exact letOk_mono hs _ (c d hd)

theorem adv_lets {s0 st st' : MachRead} (H : Adv s0 st) (hn : NoLetAlias st'.lets)
    (hs : st.lets.size ≤ st'.lets.size) (h2 : st'.nested = st.nested) (h3 : st'.dom = st.dom) :
    Adv s0 st' :=
  ⟨rdOk_lets H.1 hn hs h2 h3, Nat.le_trans H.2 hs⟩

/-- Setting the domain to an in-range expression. -/
theorem rdOk_dom {st st' : MachRead} (H : RdOk st) (h1 : st'.lets = st.lets)
    (h2 : st'.nested = st.nested) {d : Lean.Expr} (h3 : st'.dom = some d)
    (hd : LetOk st.lets.size d = true) : RdOk st' := by
  obtain ⟨a, b, _⟩ := H
  refine ⟨?_, ?_, ?_⟩
  · rw [h1]; exact a
  · rw [h1, h2]; exact b
  · rw [h1, h3]
    intro d' hd'
    cases hd'
    exact hd

theorem adv_dom {s0 st st' : MachRead} (H : Adv s0 st) (h1 : st'.lets = st.lets)
    (h2 : st'.nested = st.nested) {d : Lean.Expr} (h3 : st'.dom = some d)
    (hd : LetOk st.lets.size d = true) : Adv s0 st' := by
  refine ⟨rdOk_dom H.1 h1 h2 h3 hd, ?_⟩
  rw [h1]; exact H.2

/-- Pushing a nested machine whose result is in range. -/
theorem rdOk_nested {st st' : MachRead} (H : RdOk st) (h1 : st'.lets = st.lets)
    (h3 : st'.dom = st.dom)
    {e : Nat × Lean.Expr × Lean.Expr × Lean.Expr × List (Nat × Lean.Expr) × Lean.Expr}
    (h2 : st'.nested = st.nested.push e) (he : LetOk st.lets.size e.2.2.2.2.2 = true) :
    RdOk st' := by
  obtain ⟨a, b, c⟩ := H
  refine ⟨?_, ?_, ?_⟩
  · rw [h1]; exact a
  · rw [h1, h2, Array.toList_push]
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact b x hx
    · rw [List.mem_singleton.mp hx]; exact he
  · rw [h1, h3]; exact c

theorem adv_nested {s0 st st' : MachRead} (H : Adv s0 st) (h1 : st'.lets = st.lets)
    (h3 : st'.dom = st.dom)
    {e : Nat × Lean.Expr × Lean.Expr × Lean.Expr × List (Nat × Lean.Expr) × Lean.Expr}
    (h2 : st'.nested = st.nested.push e) (he : LetOk st.lets.size e.2.2.2.2.2 = true) :
    Adv s0 st' := by
  refine ⟨rdOk_nested H.1 h1 h3 h2 he, ?_⟩
  rw [h1]; exact H.2

/-! ## The let-binding helpers: range -/

private theorem findIdx_lt {lets : MachLets} {p : Name × MixedGateBinder × Lean.Expr → Bool}
    {j : Nat} (h : lets.findIdx? p = some j) : j < lets.size := by
  obtain ⟨hlt, _⟩ := Array.findIdx?_eq_some_iff_getElem.mp h
  exact hlt

private theorem letOk_machLet_lt {n j : Nat} (h : j < n) : LetOk n (machLet j) = true := by
  rw [letOk_machLet]; exact decide_eq_true h

theorem machBindLetNamed_range {nm : Name} {ty v' : Lean.Expr} {lets : MachLets}
    (hv : LetOk lets.size v' = true) :
    lets.size ≤ (machBindLetNamed nm ty v' lets).2.size ∧
    LetOk (machBindLetNamed nm ty v' lets).2.size (machBindLetNamed nm ty v' lets).1 = true := by
  unfold machBindLetNamed
  split
  · exact ⟨Nat.le_refl _, hv⟩
  · exact ⟨Nat.le_refl _, hv⟩
  · split
    · next j hj => exact ⟨Nat.le_refl _, letOk_machLet_lt (findIdx_lt hj)⟩
    · refine ⟨?_, ?_⟩
      · simp
      · simp only [Array.size_push]
        exact letOk_machLet_lt (Nat.lt_succ_self _)

theorem machBindLet_range {nm : Name} {ty v' : Lean.Expr} {lets : MachLets}
    (hv : LetOk lets.size v' = true) :
    lets.size ≤ (machBindLet nm ty v' lets).2.size ∧
    LetOk (machBindLet nm ty v' lets).2.size (machBindLet nm ty v' lets).1 = true := by
  unfold machBindLet
  split
  · exact ⟨Nat.le_refl _, hv⟩
  · exact ⟨Nat.le_refl _, hv⟩
  · split
    · exact ⟨Nat.le_refl _, hv⟩
    · split
      · next j hj => exact ⟨Nat.le_refl _, letOk_machLet_lt (findIdx_lt hj)⟩
      · refine ⟨?_, ?_⟩
        · simp
        · simp only [Array.size_push]
          exact letOk_machLet_lt (Nat.lt_succ_self _)

theorem machBindLetAlias_range {nm : Name} {ty v' : Lean.Expr} {lets : MachLets}
    (hv : LetOk lets.size v' = true) :
    lets.size ≤ (machBindLetAlias nm ty v' lets).2.size ∧
    LetOk (machBindLetAlias nm ty v' lets).2.size (machBindLetAlias nm ty v' lets).1 = true := by
  unfold machBindLetAlias
  by_cases hc : machIsLetVar (machBindLetAlias.resolve lets lets.size v') = true
  · rw [if_pos hc]
    exact machBindLetNamed_range hv
  · rw [if_neg hc]
    split
    · exact ⟨Nat.le_refl _, hv⟩
    · exact ⟨Nat.le_refl _, hv⟩
    · dsimp only
      split
      · next j hj => exact ⟨Nat.le_refl _, letOk_machLet_lt (findIdx_lt hj)⟩
      · refine ⟨?_, ?_⟩
        · simp
        · simp only [Array.size_push]
          exact letOk_machLet_lt (Nat.lt_succ_self _)

theorem machLetIndex_size {nm : Name} {k : MixedGateBinder} {v' : Lean.Expr} {lets : MachLets} :
    lets.size ≤ (machLetIndex nm k v' lets).2.size := by
  unfold machLetIndex
  split
  · exact Nat.le_refl _
  · split
    · exact Nat.le_refl _
    · simp

/-- The `Alias` premise of `machBindLetAlias_noAlias` from the range of the value. -/
theorem alias_premise {n : Nat} {lets : MachLets} {v' : Lean.Expr} (hn : n = lets.size)
    (hv : LetOk n v' = true) : ∀ j, v' = machLet j → j < lets.size := by
  intro j hj
  subst hn
  exact letOk_lt hv hj

/-! ## What the twin calls but cannot unfold -/

/-- **The facts the induction uses about the functions and the environment the twin consults.**
An INTERMEDIATE bundle (the final theorems of `Tools/ShippingLetsReaderInvMain.lean` take the five unproved
ones as individually named premises, not this record). Not axioms. Every field, with its status:

| field | status | note |
|---|---|---|
| `rootFloat` | NOT PROVED (cannot unfold) | `partial def`, opaque to the kernel |
| `lift` | NOT PROVED (cannot unfold) | `Expr.liftLooseBVars`, `extern` |
| `inst1` | NOT PROVED (cannot unfold) | `Expr.instantiate1`, `extern` |
| `sigTy` | NOT PROVED — ENVIRONMENT INPUT CONDITION | not a fact about a function: the types stored in `senv.instS` mention no `_machLet`; to be derived from the real `structEnv env` (declared types of constants); NOT shown here |
| `bundleIota` | NOT PROVED (total function; the proof needs a nested name/array-literal case split) | used at the `.app` arm of `machConv` |
| `projIota`, `regView`, `runApp`, `instCall`, `instCallS`, `memCall`, `loopView`, `letTail`, `loopRegs` | PROVED (`…InvPure.lean`, `…InvPure2.lean`) | pattern extractors / rewriters, by unfolding |
-/
structure PureFacts (senv : StructEnv) : Prop where
  rootFloat : ∀ n v, LetOk n v = true →
    LetOk n (Sparkle.Compiler.MachRawSurface.rootFloat v) = true
  lift : ∀ n e k m, LetOk n e = true → LetOk n (e.liftLooseBVars k m) = true
  inst1 : ∀ n b a, LetOk n b = true → LetOk n a = true → LetOk n (b.instantiate1 a) = true
  sigTy : ∀ c kinds ty, senv.instS c = some (kinds, ty) → ∀ n, LetOk n ty = true
  bundleIota : ∀ n e, LetOk n e = true →
    LetOk n (Sparkle.Compiler.MachRawSurface.bundleIota e) = true
  projIota : ∀ n e, LetOk n e = true → LetOk n (machProjIota senv.proj e) = true
  regView : ∀ n fn args d α i x, (∀ a ∈ args, LetOk n a = true) →
    regView? fn args = some (d, α, i, x) → LetOk n d = true ∧ LetOk n x = true
  runApp : ∀ n e dom αs inits body, LetOk n e = true →
    machRunApp? e = some (dom, αs, inits, body) → LetOk n dom = true ∧ LetOk n body = true
  instCall : ∀ n e c kinds res args, LetOk n e = true →
    machInstCall? senv e = some (c, kinds, res, args) → ∀ a ∈ args, LetOk n a = true
  instCallS : ∀ n e c kinds ty args, LetOk n e = true →
    machInstCallS? senv e = some (c, kinds, ty, args) → ∀ a ∈ args, LetOk n a = true
  memCall : ∀ n e combo aw dw dom ops, LetOk n e = true →
    Sparkle.Compiler.MachMemory.memCall? (fun e => canonicalNatLitValue? e <|> senv.natOf e) e =
      some (combo, aw, dw, dom, ops) → LetOk n dom = true ∧ ∀ o ∈ ops, LetOk n o = true
  loopView : ∀ n e dom body, LetOk n e = true → loopView? e = some (dom, body) →
    LetOk n dom = true ∧ LetOk n body = true
  letTail : ∀ n e, LetOk n e = true → LetOk n (machLetTail e) = true
  loopRegs : ∀ n e regs, LetOk n e = true → machLoopRegs e = some regs →
    ∀ r ∈ regs, LetOk n r.2.2 = true

end Tools.ShippingLetsReaderInv
