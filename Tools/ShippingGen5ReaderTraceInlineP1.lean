import Tools.ShippingGen5ReaderTraceDirect
set_option autoImplicit false
-- Built in Pod (kjob lake build Tools.ShippingGen5ReaderTraceInlineP1, exit 0) on the tree of 72ba7d9c18241faa708b3e6037be8ff9144860cb (Lean content identical; this header is comment-only). Clean build is the coder's. Written against `scripts/gen5/RT_INLINE_P1_FREEZE.md` (types copied from its #check output). No sorry / axiom / native_decide in source.

/-! # RT inline P1: `inlineDefs` and its parts preserve `NoPh ∧ BvarLt` (freeze `scripts/gen5/RT_INLINE_P1_FREEZE.md`)

Structural lemmas about `inlLift` / `inlSubst` / `inlBeta` / `inlSpine` / `inlMap` / `inlDropBinder` / `inlCanonLam` / `inlCanonPi` / `inlSignalMapOfFunctor` /
`inlSignalApplicative` / `inlHeadCtor` / `inlineDefs` (all from `Sparkle/Compiler/Elab.lean`, read only).
The only environment hypothesis is `Tools.Assume.EnvDeclValue.DeclValuePh env` (N1-a, defined in `Tools/ShippingGen5ReaderTraceDirect.lean`, NOT registered in `Tools/Assume/`),
used by `userDefinition?_ph` and `inlineDefs_user_ph`; `inlineDefs_ph` itself takes only `hd` (`defs n = some v → NoPh v ∧ BvarLt 0 v`). No new ledger premise.
Not supplied: `relevantClosure`'s true arm (`rounds` / `MachRecUnfold.pass`), `inlAbbrevs` (`Expr.replace` / `headBeta`), the composition of `userInliner`.
Conditional (intermediate) result: `DeclValuePh env` is not shown to hold for accepted sources. -/

namespace Tools.ShippingGen5ReaderTrace
open Lean Sparkle.Compiler.Elab

theorem foldl_app_ph (L : Nat) (h : Lean.Expr) (args : List Lean.Expr)
    (hh : NoPh h = true ∧ BvarLt L h = true) (ha : ∀ a ∈ args, NoPh a = true ∧ BvarLt L a = true) :
    NoPh (args.foldl Lean.Expr.app h) = true ∧ BvarLt L (args.foldl Lean.Expr.app h) = true := by
  induction args generalizing h with
  | nil => exact hh
  | cons a rest ih =>
    apply ih
    · have := ha a (List.mem_cons_self ..)
      simp only [NoPh, BvarLt, Bool.and_eq_true]
      exact ⟨⟨hh.1, this.1⟩, ⟨hh.2, this.2⟩⟩
    · intro x hx; exact ha x (List.mem_cons_of_mem _ hx)

theorem inlLift_ph (k : Nat) : ∀ (c : Nat) (e : Lean.Expr) (b L : Nat) (e' : Lean.Expr) (b' : Nat),
    NoPh e = true → BvarLt L e = true → inlLift k c e b = some (e', b') →
    NoPh e' = true ∧ BvarLt (L + k) e' = true := by
  intro c e
  induction e generalizing c with
  | bvar i =>
    intro b L e' b' hn hb h
    cases b with
    | zero => simp [inlLift] at h
    | succ b =>
      simp only [inlLift, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      simp only [BvarLt, decide_eq_true_eq] at hb
      split <;> exact ⟨rfl, by simp only [BvarLt, decide_eq_true_eq]; omega⟩
  | app f a ihf iha =>
    intro b L e' b' hn hb h
    cases b with
    | zero => simp [inlLift] at h
    | succ b =>
      simp only [NoPh, BvarLt, Bool.and_eq_true] at hn hb
      simp only [inlLift] at h
      split at h
      · rename_i f' b1 hf
        split at h
        · rename_i a' b2 ha
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, -⟩ := h
          have h1 := ihf c b L f' b1 hn.1 hb.1 hf
          have h2 := iha c b1 L a' b2 hn.2 hb.2 ha
          simp only [NoPh, BvarLt, Bool.and_eq_true]
          exact ⟨⟨h1.1, h2.1⟩, ⟨h1.2, h2.2⟩⟩
        · simp at h
      · simp at h
  | lam n t body bi iht ihb =>
    intro b L e' b' hn hb h
    cases b with
    | zero => simp [inlLift] at h
    | succ b =>
      simp only [NoPh, BvarLt, Bool.and_eq_true] at hn hb
      simp only [inlLift] at h
      split at h
      · rename_i t' b1 ht
        split at h
        · rename_i body' b2 hbd
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, -⟩ := h
          have h1 := iht c b L t' b1 hn.1 hb.1 ht
          have h2 := ihb (c + 1) b1 (L + 1) body' b2 hn.2 hb.2 hbd
          simp only [NoPh, BvarLt, Bool.and_eq_true]
          refine ⟨⟨h1.1, h2.1⟩, h1.2, ?_⟩
          have h2' := h2.2; rwa [show L + 1 + k = L + k + 1 by omega] at h2'
        · simp at h
      · simp at h
  | forallE n t body bi iht ihb =>
    intro b L e' b' hn hb h
    cases b with
    | zero => simp [inlLift] at h
    | succ b =>
      simp only [NoPh, BvarLt, Bool.and_eq_true] at hn hb
      simp only [inlLift] at h
      split at h
      · rename_i t' b1 ht
        split at h
        · rename_i body' b2 hbd
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, -⟩ := h
          have h1 := iht c b L t' b1 hn.1 hb.1 ht
          have h2 := ihb (c + 1) b1 (L + 1) body' b2 hn.2 hb.2 hbd
          simp only [NoPh, BvarLt, Bool.and_eq_true]
          refine ⟨⟨h1.1, h2.1⟩, h1.2, ?_⟩
          have h2' := h2.2; rwa [show L + 1 + k = L + k + 1 by omega] at h2'
        · simp at h
      · simp at h
  | letE n t v body nd iht ihv ihb =>
    intro b L e' b' hn hb h
    cases b with
    | zero => simp [inlLift] at h
    | succ b =>
      simp only [NoPh, BvarLt, Bool.and_eq_true] at hn hb
      simp only [inlLift] at h
      split at h
      · rename_i t' b1 ht
        split at h
        · rename_i v' b2 hv
          split at h
          · rename_i body' b3 hbd
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, -⟩ := h
            have h1 := iht c b L t' b1 hn.1.1 hb.1.1 ht
            have h2 := ihv c b1 L v' b2 hn.1.2 hb.1.2 hv
            have h3 := ihb (c + 1) b2 (L + 1) body' b3 hn.2 hb.2 hbd
            simp only [NoPh, BvarLt, Bool.and_eq_true]
            refine ⟨⟨⟨h1.1, h2.1⟩, h3.1⟩, ⟨h1.2, h2.2⟩, ?_⟩
            have h3' := h3.2; rwa [show L + 1 + k = L + k + 1 by omega] at h3'
          · simp at h
        · simp at h
      · simp at h
  | mdata d e ih =>
    intro b L e' b' hn hb h
    cases b with
    | zero => simp [inlLift] at h
    | succ b => simp [inlLift] at h
  | proj s i e ih =>
    intro b L e' b' hn hb h
    cases b with
    | zero => simp [inlLift] at h
    | succ b => simp [inlLift] at h
  | fvar _ | mvar _ | sort _ | const _ _ | lit _ =>
    all_goals
      intro b L e' b' hn hb h
      cases b with
      | zero => simp [inlLift] at h
      | succ b =>
        simp only [inlLift, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact ⟨hn, bvarLt_mono (Nat.le_add_right _ _) hb⟩

theorem inlSubst_ph (xs : Array Lean.Expr) (L : Nat) (hxs : ∀ x ∈ xs, NoPh x = true ∧ BvarLt L x = true) :
    ∀ (d : Nat) (e : Lean.Expr) (b : Nat) (e' : Lean.Expr) (b' : Nat),
    NoPh e = true → BvarLt (d + xs.size + L) e = true → inlSubst xs d e b = some (e', b') →
    NoPh e' = true ∧ BvarLt (d + L) e' = true := by
  intro d e
  induction e generalizing d with
  | bvar i =>
    intro b e' b' hn hb h
    cases b with
    | zero => simp [inlSubst] at h
    | succ b =>
      simp only [BvarLt, decide_eq_true_eq] at hb
      simp only [inlSubst] at h
      by_cases h1 : i < d
      · simp only [h1, if_true, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact ⟨rfl, by simp only [BvarLt, decide_eq_true_eq]; omega⟩
      · by_cases h2 : i - d < xs.size
        · simp only [h1, h2, if_true, if_false] at h
          have hmem : xs[xs.size - 1 - (i - d)]! ∈ xs := by
            rw [getElem!_pos xs _ (by omega)]
            exact Array.getElem_mem _
          have hx := hxs _ hmem
          by_cases h3 : d = 0
          · simp only [h3, if_true, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, -⟩ := h
            subst h3
            exact ⟨hx.1, by rw [Nat.zero_add]; exact hx.2⟩
          · simp only [h3, if_false] at h
            have := inlLift_ph d 0 _ b L e' b' hx.1 hx.2 h
            exact ⟨this.1, by rw [Nat.add_comm]; exact this.2⟩
        · simp only [h1, h2, if_false, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, -⟩ := h
          exact ⟨rfl, by simp only [BvarLt, decide_eq_true_eq]; omega⟩
  | app f a ihf iha =>
    intro b e' b' hn hb h
    cases b with
    | zero => simp [inlSubst] at h
    | succ b =>
      simp only [NoPh, BvarLt, Bool.and_eq_true] at hn hb
      simp only [inlSubst] at h
      split at h
      · rename_i f' b1 hf
        split at h
        · rename_i a' b2 ha
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, -⟩ := h
          have h1 := ihf d b f' b1 hn.1 hb.1 hf
          have h2 := iha d b1 a' b2 hn.2 hb.2 ha
          simp only [NoPh, BvarLt, Bool.and_eq_true]
          exact ⟨⟨h1.1, h2.1⟩, ⟨h1.2, h2.2⟩⟩
        · simp at h
      · simp at h
  | lam n t body bi iht ihb =>
    intro b e' b' hn hb h
    cases b with
    | zero => simp [inlSubst] at h
    | succ b =>
      simp only [NoPh, BvarLt, Bool.and_eq_true] at hn hb
      simp only [inlSubst] at h
      split at h
      · rename_i t' b1 ht
        split at h
        · rename_i body' b2 hbd
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, -⟩ := h
          have hb2 : BvarLt (d + 1 + xs.size + L) body = true := by
            have := hb.2; rwa [show d + xs.size + L + 1 = d + 1 + xs.size + L by omega] at this
          have h1 := iht d b t' b1 hn.1 hb.1 ht
          have h2 := ihb (d + 1) b1 body' b2 hn.2 hb2 hbd
          simp only [NoPh, BvarLt, Bool.and_eq_true]
          refine ⟨⟨h1.1, h2.1⟩, h1.2, ?_⟩
          have h2' := h2.2; rwa [show d + 1 + L = d + L + 1 by omega] at h2'
        · simp at h
      · simp at h
  | forallE n t body bi iht ihb =>
    intro b e' b' hn hb h
    cases b with
    | zero => simp [inlSubst] at h
    | succ b =>
      simp only [NoPh, BvarLt, Bool.and_eq_true] at hn hb
      simp only [inlSubst] at h
      split at h
      · rename_i t' b1 ht
        split at h
        · rename_i body' b2 hbd
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, -⟩ := h
          have hb2 : BvarLt (d + 1 + xs.size + L) body = true := by
            have := hb.2; rwa [show d + xs.size + L + 1 = d + 1 + xs.size + L by omega] at this
          have h1 := iht d b t' b1 hn.1 hb.1 ht
          have h2 := ihb (d + 1) b1 body' b2 hn.2 hb2 hbd
          simp only [NoPh, BvarLt, Bool.and_eq_true]
          refine ⟨⟨h1.1, h2.1⟩, h1.2, ?_⟩
          have h2' := h2.2; rwa [show d + 1 + L = d + L + 1 by omega] at h2'
        · simp at h
      · simp at h
  | letE n t v body nd iht ihv ihb =>
    intro b e' b' hn hb h
    cases b with
    | zero => simp [inlSubst] at h
    | succ b =>
      simp only [NoPh, BvarLt, Bool.and_eq_true] at hn hb
      simp only [inlSubst] at h
      split at h
      · rename_i t' b1 ht
        split at h
        · rename_i v' b2 hv
          split at h
          · rename_i body' b3 hbd
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, -⟩ := h
            have hb2 : BvarLt (d + 1 + xs.size + L) body = true := by
              have := hb.2; rwa [show d + xs.size + L + 1 = d + 1 + xs.size + L by omega] at this
            have h1 := iht d b t' b1 hn.1.1 hb.1.1 ht
            have h2 := ihv d b1 v' b2 hn.1.2 hb.1.2 hv
            have h3 := ihb (d + 1) b2 body' b3 hn.2 hb2 hbd
            simp only [NoPh, BvarLt, Bool.and_eq_true]
            refine ⟨⟨⟨h1.1, h2.1⟩, h3.1⟩, ⟨h1.2, h2.2⟩, ?_⟩
            have h3' := h3.2; rwa [show d + 1 + L = d + L + 1 by omega] at h3'
          · simp at h
        · simp at h
      · simp at h
  | mdata dd e ih =>
    intro b e' b' hn hb h
    cases b with
    | zero => simp [inlSubst] at h
    | succ b => simp [inlSubst] at h
  | proj s i e ih =>
    intro b e' b' hn hb h
    cases b with
    | zero => simp [inlSubst] at h
    | succ b => simp [inlSubst] at h
  | fvar _ | mvar _ | sort _ | const _ _ | lit _ =>
    all_goals
      intro b e' b' hn hb h
      cases b with
      | zero => simp [inlSubst] at h
      | succ b =>
        simp only [inlSubst, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact ⟨hn, rfl⟩

theorem inlBeta_ph (L : Nat) : ∀ (v : Lean.Expr) (acc : Array Lean.Expr) (args : List Lean.Expr) (b : Nat)
    (e' : Lean.Expr) (b' : Nat),
    (∀ x ∈ acc, NoPh x = true ∧ BvarLt L x = true) → (∀ a ∈ args, NoPh a = true ∧ BvarLt L a = true) →
    NoPh v = true → BvarLt (acc.size + L) v = true → inlBeta acc v args b = some (e', b') →
    NoPh e' = true ∧ BvarLt L e' = true := by
  intro v acc args
  induction args generalizing v acc with
  | nil =>
    intro b e' b' hacc hargs hn hb h
    have hq : inlBeta acc v [] b = (match inlSubst acc 0 v b with
        | some (f', b) => some ([].foldl Lean.Expr.app f', b)
        | none => none) := by cases v <;> rfl
    rw [hq] at h
    split at h
    · rename_i f' b1 hs
      simp only [List.foldl_nil, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      have := inlSubst_ph acc L hacc 0 v b f' b1 hn (by rwa [Nat.zero_add]) hs
      exact ⟨this.1, by rw [Nat.zero_add] at this; exact this.2⟩
    · simp at h
  | cons a rest ih =>
    intro b e' b' hacc hargs hn hb h
    by_cases hl : ∃ n t body bi, v = Lean.Expr.lam n t body bi
    · obtain ⟨n, t, body, bi, rfl⟩ := hl
      have hq : inlBeta acc (Lean.Expr.lam n t body bi) (a :: rest) b = inlBeta (acc.push a) body rest b := rfl
      rw [hq] at h
      simp only [NoPh, BvarLt, Bool.and_eq_true] at hn hb
      apply ih body (acc.push a) b e' b' _ (fun x hx => hargs x (List.mem_cons_of_mem _ hx)) hn.2 _ h
      · intro x hx
        rcases Array.mem_push.mp hx with hx | rfl
        · exact hacc x hx
        · exact hargs x (List.mem_cons_self ..)
      · rw [Array.size_push, show acc.size + 1 + L = acc.size + L + 1 by omega]; exact hb.2
    · have hq : inlBeta acc v (a :: rest) b = (match inlSubst acc 0 v b with
          | some (f', b) => some ((a :: rest).foldl Lean.Expr.app f', b)
          | none => none) := by
        cases v <;> first | rfl | (exfalso; exact hl ⟨_, _, _, _, rfl⟩)
      rw [hq] at h
      split at h
      · rename_i f' b1 hs
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        have := inlSubst_ph acc L hacc 0 v b f' b1 hn (by rwa [Nat.zero_add]) hs
        rw [Nat.zero_add] at this
        exact foldl_app_ph L f' _ this hargs
      · simp at h

theorem inlSpineAll_ph (L : Nat) : ∀ (e : Lean.Expr) (acc : List Lean.Expr) (h : Lean.Expr) (args : List Lean.Expr),
    NoPh e = true → BvarLt L e = true → (∀ a ∈ acc, NoPh a = true ∧ BvarLt L a = true) →
    inlSpine e acc = (h, args) →
    (NoPh h = true ∧ BvarLt L h = true) ∧ ∀ a ∈ args, NoPh a = true ∧ BvarLt L a = true := by
  intro e
  induction e <;> intro acc h args hn hb hacc hs
  case app f a ihf iha =>
    simp only [NoPh, BvarLt, Bool.and_eq_true] at hn hb
    simp only [inlSpine] at hs
    refine ihf (a :: acc) h args hn.1 hb.1 ?_ hs
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨hn.2, hb.2⟩
    · exact hacc x hx
  all_goals
    simp only [inlSpine, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    exact ⟨⟨hn, hb⟩, hacc⟩

theorem inlMap_ph (f : Lean.Expr → Nat → Option (Lean.Expr × Nat)) (L : Nat)
    (hf : ∀ (a : Lean.Expr) (b : Nat) (a' : Lean.Expr) (b' : Nat),
      NoPh a = true → BvarLt L a = true → f a b = some (a', b') → NoPh a' = true ∧ BvarLt L a' = true) :
    ∀ (xs : List Lean.Expr) (b : Nat) (xs' : List Lean.Expr) (b' : Nat),
    (∀ x ∈ xs, NoPh x = true ∧ BvarLt L x = true) → inlMap f xs b = some (xs', b') →
    ∀ x ∈ xs', NoPh x = true ∧ BvarLt L x = true := by
  intro xs
  induction xs with
  | nil =>
    intro b xs' b' _ h
    simp only [inlMap, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    intro x hx; simp at hx
  | cons a rest ih =>
    intro b xs' b' hxs h
    simp only [inlMap] at h
    split at h
    · rename_i a' b1 ha
      split at h
      · rename_i rest' b2 hr
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hf a b x b1 (hxs a (List.mem_cons_self ..)).1 (hxs a (List.mem_cons_self ..)).2 ha
        · exact ih b1 rest' b2 (fun y hy => hxs y (List.mem_cons_of_mem _ hy)) hr x hx
      · simp at h
    · simp at h

theorem inlDropBinder_ph : ∀ (e : Lean.Expr) (c M : Nat) (e' : Lean.Expr),
    c ≤ M → NoPh e = true → BvarLt (M + 1) e = true → inlDropBinder c e = some e' →
    NoPh e' = true ∧ BvarLt M e' = true := by
  intro e
  induction e with
  | bvar i =>
    intro c M e' hc hn hb h
    simp only [BvarLt, decide_eq_true_eq] at hb
    simp only [inlDropBinder] at h
    by_cases h1 : i < c
    · simp only [h1, if_true, Option.some.injEq] at h
      subst h
      exact ⟨rfl, by simp only [BvarLt, decide_eq_true_eq]; omega⟩
    · by_cases h2 : i = c
      · simp [h2] at h
      · simp only [h1, h2, if_false, Option.some.injEq] at h
        subst h
        exact ⟨rfl, by simp only [BvarLt, decide_eq_true_eq]; omega⟩
  | app f a ihf iha =>
    intro c M e' hc hn hb h
    simp only [NoPh, BvarLt, Bool.and_eq_true] at hn hb
    simp only [inlDropBinder] at h
    split at h
    · rename_i f' a' hf ha
      simp only [Option.some.injEq] at h
      subst h
      have h1 := ihf c M f' hc hn.1 hb.1 hf
      have h2 := iha c M a' hc hn.2 hb.2 ha
      simp only [NoPh, BvarLt, Bool.and_eq_true]
      exact ⟨⟨h1.1, h2.1⟩, ⟨h1.2, h2.2⟩⟩
    · simp at h
  | lam n t body bi iht ihb =>
    intro c M e' hc hn hb h
    simp only [NoPh, BvarLt, Bool.and_eq_true] at hn hb
    simp only [inlDropBinder] at h
    split at h
    · rename_i t' body' ht hbd
      simp only [Option.some.injEq] at h
      subst h
      have h1 := iht c M t' hc hn.1 hb.1 ht
      have h2 := ihb (c + 1) (M + 1) body' (by omega) hn.2 hb.2 hbd
      simp only [NoPh, BvarLt, Bool.and_eq_true]
      exact ⟨⟨h1.1, h2.1⟩, h1.2, h2.2⟩
    · simp at h
  | forallE n t body bi iht ihb =>
    intro c M e' hc hn hb h
    simp only [NoPh, BvarLt, Bool.and_eq_true] at hn hb
    simp only [inlDropBinder] at h
    split at h
    · rename_i t' body' ht hbd
      simp only [Option.some.injEq] at h
      subst h
      have h1 := iht c M t' hc hn.1 hb.1 ht
      have h2 := ihb (c + 1) (M + 1) body' (by omega) hn.2 hb.2 hbd
      simp only [NoPh, BvarLt, Bool.and_eq_true]
      exact ⟨⟨h1.1, h2.1⟩, h1.2, h2.2⟩
    · simp at h
  | letE _ _ _ _ _ _ _ _ => intro c M e' hc hn hb h; simp [inlDropBinder] at h
  | mdata _ _ _ => intro c M e' hc hn hb h; simp [inlDropBinder] at h
  | proj _ _ _ _ => intro c M e' hc hn hb h; simp [inlDropBinder] at h
  | fvar _ | mvar _ | sort _ | const _ _ | lit _ =>
    all_goals
      intro c M e' hc hn hb h
      simp only [inlDropBinder, Option.some.injEq] at h
      subst h
      exact ⟨hn, rfl⟩

theorem inlCanonLam_ph : ∀ (e : Lean.Expr) (k L : Nat),
    NoPh e = true → BvarLt L e = true →
    NoPh (inlCanonLam k e) = true ∧ BvarLt L (inlCanonLam k e) = true := by
  intro e
  induction e with
  | lam n t body bi iht ihb =>
    intro k L hn hb
    simp only [NoPh, BvarLt, Bool.and_eq_true] at hn hb
    have h2 := ihb (k + 1) (L + 1) hn.2 hb.2
    simp only [inlCanonLam, NoPh, BvarLt, Bool.and_eq_true]
    exact ⟨⟨hn.1, h2.1⟩, hb.1, h2.2⟩
  | _ => intro k L hn hb; exact ⟨hn, hb⟩

theorem inlCanonPi_ph : ∀ (e : Lean.Expr) (L : Nat),
    NoPh e = true → BvarLt L e = true →
    NoPh (inlCanonPi e) = true ∧ BvarLt L (inlCanonPi e) = true := by
  intro e
  induction e with
  | forallE n t body bi iht ihb =>
    intro L hn hb
    simp only [NoPh, BvarLt, Bool.and_eq_true] at hn hb
    have h2 := ihb (L + 1) hn.2 hb.2
    simp only [inlCanonPi, NoPh, BvarLt, Bool.and_eq_true]
    exact ⟨⟨hn.1, h2.1⟩, hb.1, h2.2⟩
  | _ => intro L hn hb; exact ⟨hn, hb⟩

theorem inlSignalMapOfFunctor_ph (L : Nat) (e e' : Lean.Expr) :
    NoPh e = true → BvarLt L e = true → inlSignalMapOfFunctor e = some e' →
    NoPh e' = true ∧ BvarLt L e' = true := by
  intro hn hb h
  unfold inlSignalMapOfFunctor at h
  split at h
  · split at h
    · simp only [Option.some.injEq] at h
      subst h
      rename_i _ u tl us1 dom us dom' α β f a _
      simp only [NoPh, BvarLt, Bool.and_eq_true] at hn hb ⊢
      obtain ⟨⟨⟨⟨⟨⟨_, _, hnd⟩, _, hnd'⟩, hnα⟩, hnβ⟩, hnf⟩, hna⟩ := hn
      obtain ⟨⟨⟨⟨⟨⟨_, _, hbd⟩, _, hbd'⟩, hbα⟩, hbβ⟩, hbf⟩, hba⟩ := hb
      have hp := inlCanonPi_ph β L hnβ hbβ
      have hl := inlCanonLam_ph f 0 L hnf hbf
      exact ⟨⟨⟨⟨⟨⟨trivial, hnd⟩, hnα⟩, hp.1⟩, hl.1⟩, hna⟩, ⟨⟨⟨⟨⟨trivial, hbd⟩, hbα⟩, hp.2⟩, hl.2⟩, hba⟩⟩
    · simp at h
  · simp at h

theorem inlSignalApplicative_ph (L : Nat) (n : Lean.Name) (ls : List Lean.Level) (args : List Lean.Expr)
    (e' : Lean.Expr) :
    (∀ a ∈ args, NoPh a = true ∧ BvarLt L a = true) → inlSignalApplicative n ls args = some e' →
    NoPh e' = true ∧ BvarLt L e' = true := by
  intro ha h
  unfold inlSignalApplicative at h
  split at h
  · split at h
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨mx', hmx, rfl⟩ := h
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, NoPh, BvarLt,
        Bool.and_eq_true] at ha
      rename_i ls0 args0 u tl us3 dom us2 us1 dom'' us dom' α β mf bn bt mx bi _
      obtain ⟨⟨⟨_, hnd⟩, _, hbd⟩, _, ⟨hnα, hbα⟩, ⟨hnβ, hbβ⟩, ⟨hnmf, hbmf⟩, ⟨_, hnmx⟩, _, hbmx⟩ := ha
      have hm := inlDropBinder_ph mx 0 L mx' (Nat.zero_le _) hnmx hbmx hmx
      have hmf : NoPh ((inlSignalMapOfFunctor mf).getD mf) = true ∧
          BvarLt L ((inlSignalMapOfFunctor mf).getD mf) = true := by
        cases hq : inlSignalMapOfFunctor mf with
        | none => simp only [Option.getD_none]; exact ⟨hnmf, hbmf⟩
        | some r => simp only [Option.getD_some]; exact inlSignalMapOfFunctor_ph L mf r hnmf hbmf hq
      simp only [NoPh, BvarLt, Bool.and_eq_true]
      exact ⟨⟨⟨⟨⟨⟨trivial, hnd⟩, hnα⟩, hnβ⟩, hmf.1⟩, hm.1⟩, ⟨⟨⟨⟨⟨trivial, hbd⟩, hbα⟩, hbβ⟩, hmf.2⟩, hm.2⟩⟩
    · simp at h
  · simp at h

theorem inlHeadCtor_ph (defs : Lean.Name → Option Lean.Expr)
    (hd : ∀ (n : Lean.Name) (v : Lean.Expr), defs n = some v → NoPh v = true ∧ BvarLt 0 v = true)
    (ctor : Lean.Name) : ∀ (fuel : Nat) (e : Lean.Expr) (b L : Nat) (as : List Lean.Expr) (b' : Nat),
    NoPh e = true → BvarLt L e = true → inlHeadCtor defs ctor fuel e b = some (as, b') →
    ∀ a ∈ as, NoPh a = true ∧ BvarLt L a = true := by
  intro fuel
  induction fuel with
  | zero => intro e b L as b' _ _ h; simp [inlHeadCtor] at h
  | succ fuel ih =>
    intro e b L as b' hn hb h
    cases b with
    | zero =>
      have hq : inlHeadCtor defs ctor (fuel + 1) e 0 = none := by cases e <;> rfl
      rw [hq] at h; simp at h
    | succ b =>
      by_cases hl : ∃ n t v body nd, e = Lean.Expr.letE n t v body nd
      · obtain ⟨n, t, v, body, nd, rfl⟩ := hl
        have hq : inlHeadCtor defs ctor (fuel + 1) (Lean.Expr.letE n t v body nd) (b + 1) =
            (match inlSubst #[v] 0 body b with
             | some (e', b) => inlHeadCtor defs ctor fuel e' b
             | none => none) := rfl
        rw [hq] at h
        simp only [NoPh, BvarLt, Bool.and_eq_true] at hn hb
        split at h
        · rename_i e1 b1 hs
          have hsz : (0 + (#[v] : Array Lean.Expr).size + L) = L + 1 := by
            show 0 + 1 + L = L + 1; omega
          have hx : ∀ x ∈ (#[v] : Array Lean.Expr), NoPh x = true ∧ BvarLt L x = true := by
            intro x hx
            have : x = v := by simpa using hx
            subst this; exact ⟨hn.1.2, hb.1.2⟩
          have := inlSubst_ph #[v] L hx 0 body b e1 b1 hn.2 (by rw [hsz]; exact hb.2) hs
          rw [Nat.zero_add] at this
          exact ih e1 b1 L as b' this.1 this.2 h
        · simp at h
      · have hq : inlHeadCtor defs ctor (fuel + 1) e (b + 1) =
            (match inlSpine e [] with
             | (.const n ls, args) =>
               if n == ctor then some (args, b)
               else match (if ls.isEmpty then defs n else none) with
                 | some v =>
                   match inlBeta #[] v args b with
                   | some (e', b) => inlHeadCtor defs ctor fuel e' b
                   | none => none
                 | none => none
             | (.lam n t body bi, a :: rest) =>
               match inlBeta #[] (.lam n t body bi) (a :: rest) b with
               | some (e', b) => inlHeadCtor defs ctor fuel e' b
               | none => none
             | _ => none) := by
          cases e <;> first | rfl | (exfalso; exact hl ⟨_, _, _, _, _, rfl⟩)
        rw [hq] at h
        split at h
        · rename_i n ls args hs
          have hsp := inlSpineAll_ph L e [] _ _ hn hb (by simp) hs
          split at h
          · simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, -⟩ := h
            exact hsp.2
          · split at h
            · rename_i v hv
              split at h
              · rename_i e1 b1 hbeta
                have hdv : defs n = some v := by
                  split at hv
                  · exact hv
                  · simp at hv
                have hv0 := hd n v hdv
                have := inlBeta_ph L v #[] args b e1 b1 (by simp) hsp.2 hv0.1
                  (by rw [show (#[] : Array Lean.Expr).size + L = 0 + L by simp]
                      exact bvarLt_mono (Nat.zero_le _) hv0.2) hbeta
                exact ih e1 b1 L as b' this.1 this.2 h
              · simp at h
            · simp at h
        · rename_i n t body bi a rest hs
          have hsp := inlSpineAll_ph L e [] _ _ hn hb (by simp) hs
          split at h
          · rename_i e1 b1 hbeta
            have := inlBeta_ph L (.lam n t body bi) #[] (a :: rest) b e1 b1 (by simp) hsp.2 hsp.1.1
              (by rw [show (#[] : Array Lean.Expr).size + L = 0 + L by simp, Nat.zero_add]; exact hsp.1.2) hbeta
            exact ih e1 b1 L as b' this.1 this.2 h
          · simp at h
        · simp at h

theorem inlineDefs_ph (defs : Lean.Name → Option Lean.Expr)
    (projs : Lean.Name → Option (Lean.Name × Nat × Nat))
    (hd : ∀ (n : Lean.Name) (v : Lean.Expr), defs n = some v → NoPh v = true ∧ BvarLt 0 v = true) :
    ∀ (fuel : Nat) (e : Lean.Expr) (b L : Nat) (e' : Lean.Expr) (b' : Nat),
    NoPh e = true → BvarLt L e = true → inlineDefs defs projs fuel e b = some (e', b') →
    NoPh e' = true ∧ BvarLt L e' = true := by
  intro fuel
  induction fuel with
  | zero => intro e b L e' b' _ _ h; simp [inlineDefs] at h
  | succ fuel ih =>
    intro e b L e' b' hn hb h
    cases b with
    | zero =>
      have hq : inlineDefs defs projs (fuel + 1) e 0 = none := by cases e <;> rfl
      rw [hq] at h; simp at h
    | succ b =>
      by_cases hlam : ∃ n t body bi, e = Lean.Expr.lam n t body bi
      · obtain ⟨n, t, body, bi, rfl⟩ := hlam
        have hq : inlineDefs defs projs (fuel + 1) (Lean.Expr.lam n t body bi) (b + 1) =
            (match inlineDefs defs projs fuel body b with
             | some (body', b) => some (.lam n t body' bi, b)
             | none => none) := rfl
        rw [hq] at h
        simp only [NoPh, BvarLt, Bool.and_eq_true] at hn hb
        split at h
        · rename_i body' b1 hs
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, -⟩ := h
          have := ih body b (L + 1) body' b1 hn.2 hb.2 hs
          simp only [NoPh, BvarLt, Bool.and_eq_true]
          exact ⟨⟨hn.1, this.1⟩, hb.1, this.2⟩
        · simp at h
      by_cases hlet : ∃ n t v body nd, e = Lean.Expr.letE n t v body nd
      · obtain ⟨n, t, v, body, nd, rfl⟩ := hlet
        have hq : inlineDefs defs projs (fuel + 1) (Lean.Expr.letE n t v body nd) (b + 1) =
            (match inlineDefs defs projs fuel v b with
             | some (v', b) =>
               match inlineDefs defs projs fuel body b with
               | some (body', b) => some (.letE n t v' body' nd, b)
               | none => none
             | none => none) := rfl
        rw [hq] at h
        simp only [NoPh, BvarLt, Bool.and_eq_true] at hn hb
        split at h
        · rename_i v' b1 hv
          split at h
          · rename_i body' b2 hbd
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, -⟩ := h
            have h1 := ih v b L v' b1 hn.1.2 hb.1.2 hv
            have h2 := ih body b1 (L + 1) body' b2 hn.2 hb.2 hbd
            simp only [NoPh, BvarLt, Bool.and_eq_true]
            exact ⟨⟨⟨hn.1.1, h1.1⟩, h2.1⟩, ⟨hb.1.1, h1.2⟩, h2.2⟩
          · simp at h
        · simp at h
      · have hq : inlineDefs defs projs (fuel + 1) e (b + 1) =
            (match inlSpine e [] with
    | (.const n [], args) =>
      match defs n with
      | some v =>
        match inlBeta #[] v args b with
        | some (e', b) => inlineDefs defs projs fuel e' b
        | none => none
      | none =>
        let field? : Option (Lean.Expr × Nat) :=
          match projs n with
          | some (ctor, numParams, idx) =>
            if args.length = numParams + 1 then
              match args.getLast? with
              | some record =>
                match inlHeadCtor defs ctor fuel record b with
                | some (ctorArgs, b) => (ctorArgs[numParams + idx]?).map (·, b)
                | none => none
              | none => none
            else none
          | none => none
        match field? with
        | some (field, b) => inlineDefs defs projs fuel field b
        | none =>
          match inlMap (inlineDefs defs projs fuel) args b with
          | some (args', b) => some (args'.foldl Lean.Expr.app (.const n []), b)
          | none => none
    | (.const n ls, args) =>
      match inlMap (inlineDefs defs projs fuel) args b with
      | some (args', b) =>
        match inlSignalApplicative n ls args' with
        | some e' => some (e', b)
        | none => some (args'.foldl Lean.Expr.app (.const n ls), b)
      | none => none
    | (.lam n t body bi, args) =>
      match inlineDefs defs projs fuel body b with
      | some (body', b) =>
        match inlMap (inlineDefs defs projs fuel) args b with
        | some (args', b) => some (args'.foldl Lean.Expr.app (.lam n t body' bi), b)
        | none => none
      | none => none
    | (h, args) =>
      match inlMap (inlineDefs defs projs fuel) args b with
      | some (args', b) => some (args'.foldl Lean.Expr.app h, b)
      | none => none) := by
          cases e <;> first | rfl | (exfalso; first | exact hlam ⟨_, _, _, _, rfl⟩ | exact hlet ⟨_, _, _, _, _, rfl⟩)
        rw [hq] at h
        have hmap : ∀ (args : List Lean.Expr), (∀ a ∈ args, NoPh a = true ∧ BvarLt L a = true) →
            ∀ (b0 : Nat) (args' : List Lean.Expr) (b1 : Nat),
            inlMap (inlineDefs defs projs fuel) args b0 = some (args', b1) →
            ∀ x ∈ args', NoPh x = true ∧ BvarLt L x = true := by
          intro args hargs b0 args' b1 hm
          exact inlMap_ph (inlineDefs defs projs fuel) L
            (fun a b a' b' hna hba hs => ih a b L a' b' hna hba hs) args b0 args' b1 hargs hm
        split at h
        · rename_i n args hs
          have hsp := inlSpineAll_ph L e [] _ _ hn hb (by simp) hs
          split at h
          · rename_i v hv
            split at h
            · rename_i e1 b1 hbeta
              have hv0 := hd n v hv
              have := inlBeta_ph L v #[] args b e1 b1 (by simp) hsp.2 hv0.1
                (by rw [show (#[] : Array Lean.Expr).size + L = 0 + L by simp]
                    exact bvarLt_mono (Nat.zero_le _) hv0.2) hbeta
              exact ih e1 b1 L e' b' this.1 this.2 h
            · simp at h
          · rename_i hdn
            dsimp only at h
            have hfield : ∀ (field : Lean.Expr) (b1 : Nat),
                (match projs n with
                  | some (ctor, numParams, idx) =>
                    if args.length = numParams + 1 then
                      match args.getLast? with
                      | some record =>
                        match inlHeadCtor defs ctor fuel record b with
                        | some (ctorArgs, b) => (ctorArgs[numParams + idx]?).map (·, b)
                        | none => none
                      | none => none
                    else none
                  | none => none) = some (field, b1) →
                NoPh field = true ∧ BvarLt L field = true := by
              intro field b1 hF
              split at hF
              · rename_i ctor np idx _
                split at hF
                · split at hF
                  · rename_i record hrec
                    split at hF
                    · rename_i cargs b2 hcargs
                      have hc := inlHeadCtor_ph defs hd ctor fuel record b L cargs b2
                        (hsp.2 record (List.mem_of_getLast? hrec)).1 (hsp.2 record (List.mem_of_getLast? hrec)).2 hcargs
                      cases hget : cargs[np + idx]? with
                      | none => simp [hget] at hF
                      | some f0 =>
                        simp only [hget, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hF
                        obtain ⟨rfl, -⟩ := hF
                        exact hc _ (List.mem_of_getElem? hget)
                    · simp at hF
                  · simp at hF
                · simp at hF
              · simp at hF
            generalize hF : (match projs n with
                  | some (ctor, numParams, idx) =>
                    if args.length = numParams + 1 then
                      match args.getLast? with
                      | some record =>
                        match inlHeadCtor defs ctor fuel record b with
                        | some (ctorArgs, b) => (ctorArgs[numParams + idx]?).map (·, b)
                        | none => none
                      | none => none
                    else none
                  | none => none) = F at h
            cases F with
            | some fb =>
              obtain ⟨field, b1⟩ := fb
              have hfp := hfield field b1 hF
              simp only at h
              exact ih field b1 L e' b' hfp.1 hfp.2 h
            | none =>
              simp only at h
              split at h
              · rename_i args' b1 hm
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, -⟩ := h
                exact foldl_app_ph L _ args' ⟨rfl, rfl⟩ (hmap args hsp.2 b args' b1 hm)
              · simp at h
        · rename_i n ls args _ hs
          have hsp := inlSpineAll_ph L e [] _ _ hn hb (by simp) hs
          split at h
          · rename_i args' b1 hm
            have hm' := hmap args hsp.2 b args' b1 hm
            split at h
            · rename_i e1 hsig
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, -⟩ := h
              exact inlSignalApplicative_ph L n ls args' e1 hm' hsig
            · simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, -⟩ := h
              exact foldl_app_ph L _ args' ⟨rfl, rfl⟩ hm'
          · simp at h
        · rename_i n t body bi args hs
          have hsp := inlSpineAll_ph L e [] _ _ hn hb (by simp) hs
          obtain ⟨⟨hln, hlb⟩, hargs⟩ := hsp
          simp only [NoPh, BvarLt, Bool.and_eq_true] at hln hlb
          split at h
          · rename_i body' b1 hbody
            have h1 := ih body b (L + 1) body' b1 hln.2 hlb.2 hbody
            split at h
            · rename_i args' b2 hm
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, -⟩ := h
              refine foldl_app_ph L _ args' ?_ (hmap args hargs b1 args' b2 hm)
              simp only [NoPh, BvarLt, Bool.and_eq_true]
              exact ⟨⟨hln.1, h1.1⟩, hlb.1, h1.2⟩
            · simp at h
          · simp at h
        · rename_i hh args _ _ _ hs
          have hsp := inlSpineAll_ph L e [] _ _ hn hb (by simp) hs
          split at h
          · rename_i args' b1 hm
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, -⟩ := h
            exact foldl_app_ph L _ args' hsp.1 (hmap args hsp.2 b args' b1 hm)
          · simp at h

theorem userDefinition?_ph (env : Lean.Environment) (hv : Tools.Assume.EnvDeclValue.DeclValuePh env)
    (n : Lean.Name) (v : Lean.Expr) (h : userDefinition? env n = some v) :
    NoPh v = true ∧ BvarLt 0 v = true := by
  unfold userDefinition? at h
  split at h
  · rename_i d hfind
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact hv n d hfind
    · simp at h
  · simp at h

theorem inlineDefs_user_ph (env : Lean.Environment) (hv : Tools.Assume.EnvDeclValue.DeclValuePh env)
    (L : Nat) (e : Lean.Expr) (hn : NoPh e = true) (hb : BvarLt L e = true) :
    NoPh (match inlineDefs (userDefinition? env) (userProjection? env) inlineDepth e inlineBudget with
      | some (e', _) => e'
      | none => e) = true ∧
    BvarLt L (match inlineDefs (userDefinition? env) (userProjection? env) inlineDepth e inlineBudget with
      | some (e', _) => e'
      | none => e) = true := by
  split
  · rename_i e1 b1 h
    exact inlineDefs_ph (userDefinition? env) (userProjection? env) (userDefinition?_ph env hv)
      inlineDepth e inlineBudget L e1 b1 hn hb h
  · exact ⟨hn, hb⟩

end Tools.ShippingGen5ReaderTrace
