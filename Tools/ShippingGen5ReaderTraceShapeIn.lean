import Tools.ShippingGen5ReaderTraceShape
import Tools.ShippingGen5ReaderTraceExtract
import Tools.ShippingGen5ReaderTraceLet
import Tools.Assume.N3Extern
import Tools.ShippingGen5ReaderTraceReg
set_option autoImplicit false
-- NOT BUILT: written against freeze rev14 `scripts/gen5/DG_READERTRACE_FREEZE_REV14.md` §2.3 (U-R12c, structural lemmas without premise). No sorry / axiom / native_decide in source.

/-! # DG-READERTRACE U-R12c: `NoPh ∧ BvarLt` through the preprocessing of `shapeMid`

Structural lemmas (no premise): `inlFoldNat_ph`, `machLoopAsLet_ph`, `mixedGatePeel_ph`, `machRootLets_ph`, `machRoot_ph`.
Conditional on the existing named hypotheses only: `zeroLit_ph` (`ZeroLitAgrees0`, T1L-54), `shapeMid_ph` (+ `RootFloatAgrees`, T1L-52).
`shapeInputs_of` assembles `ShapeInputs` from named hypotheses that are theorem arguments here, not ledger rows (the rev15 freeze decides what is adopted):
`hdecl` (the declaration's value), `hpack` (`packTupleInputs`), `hnorm` (`machNormF`), `hdom` (`DomAtomic` of the run domain), `hbs` (`p.bs.length ≤ nDecl`).
Conditional (intermediate) result: none of these hypotheses is shown to hold for accepted sources. -/

namespace Tools.ShippingGen5ReaderTrace
open Lean Sparkle.Compiler.Elab Tools.ShippingGen5Cover2 Tools.ShippingGen5Cover3 Tools.ShippingGen5Cover5 Tools.ShippingGen5Cover6
  Tools.ShippingReaderFuel Tools.ShippingReaderFuelShapeR5 Tools.ShippingLetsReaderInv Tools.ShippingLetsAliasInv

theorem inlNatLit_ph (k L : Nat) : NoPh (inlNatLit k) = true ∧ BvarLt L (inlNatLit k) = true := by
  simp [inlNatLit, mkApp3, mkApp, NoPh, BvarLt]

theorem inlNatSum?_ph {L : Nat} (e r : Lean.Expr) (h : inlNatSum? e = some r) :
    NoPh r = true ∧ BvarLt L r = true := by
  unfold inlNatSum? at h
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | (injection h with h; subst h; exact inlNatLit_ph _ _)

theorem inlFoldNat_ph {L : Nat} : ∀ e : Lean.Expr, NoPh e = true → BvarLt L e = true →
    NoPh (inlFoldNat e) = true ∧ BvarLt L (inlFoldNat e) = true
  | .app f a, hn, hb => by
    simp only [NoPh, BvarLt, Bool.and_eq_true] at hn hb
    have h1 := inlFoldNat_ph f hn.1 hb.1
    have h2 := inlFoldNat_ph a hn.2 hb.2
    unfold inlFoldNat
    cases hs : inlNatSum? (Lean.Expr.app (inlFoldNat f) (inlFoldNat a)) with
    | some r => simpa [hs] using inlNatSum?_ph (L := L) _ r hs
    | none =>
      simp only [hs, Option.getD_none, NoPh, BvarLt, Bool.and_eq_true]
      exact ⟨⟨h1.1, h2.1⟩, ⟨h1.2, h2.2⟩⟩
  | .lam _ t b _, hn, hb => by
    simp only [NoPh, BvarLt, Bool.and_eq_true, inlFoldNat] at hn hb ⊢
    have h1 := inlFoldNat_ph t hn.1 hb.1
    have h2 := inlFoldNat_ph b hn.2 hb.2
    exact ⟨⟨h1.1, h2.1⟩, ⟨h1.2, h2.2⟩⟩
  | .forallE _ t b _, hn, hb => by
    simp only [NoPh, BvarLt, Bool.and_eq_true, inlFoldNat] at hn hb ⊢
    have h1 := inlFoldNat_ph t hn.1 hb.1
    have h2 := inlFoldNat_ph b hn.2 hb.2
    exact ⟨⟨h1.1, h2.1⟩, ⟨h1.2, h2.2⟩⟩
  | .letE _ t v b _, hn, hb => by
    simp only [NoPh, BvarLt, Bool.and_eq_true, inlFoldNat] at hn hb ⊢
    have h1 := inlFoldNat_ph t hn.1.1 hb.1.1
    have h2 := inlFoldNat_ph v hn.1.2 hb.1.2
    have h3 := inlFoldNat_ph b hn.2 hb.2
    exact ⟨⟨⟨h1.1, h2.1⟩, h3.1⟩, ⟨⟨h1.2, h2.2⟩, h3.2⟩⟩
  | .mdata _ e, hn, hb => by
    simp only [NoPh, BvarLt, inlFoldNat] at hn hb ⊢
    exact inlFoldNat_ph e hn hb
  | .proj _ _ e, hn, hb => by
    simp only [NoPh, BvarLt, inlFoldNat] at hn hb ⊢
    exact inlFoldNat_ph e hn hb
  | .bvar _, hn, hb => ⟨hn, hb⟩
  | .fvar _, hn, hb => ⟨hn, hb⟩
  | .mvar _, hn, hb => ⟨hn, hb⟩
  | .sort _, hn, hb => ⟨hn, hb⟩
  | .const _ _, hn, hb => ⟨hn, hb⟩
  | .lit _, hn, hb => ⟨hn, hb⟩

/-! ## `zeroLit` (through the structural `replaceNoCache`; the link is `ZeroLitAgrees0`, T1L-54) -/

theorem replaceNoCache_ph (f : Lean.Expr → Option Lean.Expr)
    (hf : ∀ x r, f x = some r → NoPh r = true ∧ ∀ L, BvarLt L r = true) :
    ∀ (e : Lean.Expr) (L : Nat), NoPh e = true → BvarLt L e = true →
      NoPh (e.replaceNoCache f) = true ∧ BvarLt L (e.replaceNoCache f) = true
  | .forallE nm t b bi, L, hn, hb => by
    cases hfe : f (.forallE nm t b bi) with
    | some r => rw [Lean.Expr.replaceNoCache, hfe]; exact ⟨(hf _ r hfe).1, (hf _ r hfe).2 L⟩
    | none =>
      rw [Lean.Expr.replaceNoCache, hfe]
      simp only [NoPh, BvarLt, Bool.and_eq_true, Lean.Expr.updateForallE!, Lean.Expr.updateForall!, Lean.mkForall] at hn hb ⊢
      have h1 := replaceNoCache_ph f hf t L hn.1 hb.1
      have h2 := replaceNoCache_ph f hf b (L + 1) hn.2 hb.2
      exact ⟨⟨h1.1, h2.1⟩, ⟨h1.2, h2.2⟩⟩
  | .lam nm t b bi, L, hn, hb => by
    cases hfe : f (.lam nm t b bi) with
    | some r => rw [Lean.Expr.replaceNoCache, hfe]; exact ⟨(hf _ r hfe).1, (hf _ r hfe).2 L⟩
    | none =>
      rw [Lean.Expr.replaceNoCache, hfe]
      simp only [NoPh, BvarLt, Bool.and_eq_true, Lean.Expr.updateLambdaE!, Lean.Expr.updateLambda!, Lean.mkLambda] at hn hb ⊢
      have h1 := replaceNoCache_ph f hf t L hn.1 hb.1
      have h2 := replaceNoCache_ph f hf b (L + 1) hn.2 hb.2
      exact ⟨⟨h1.1, h2.1⟩, ⟨h1.2, h2.2⟩⟩
  | .mdata d b, L, hn, hb => by
    cases hfe : f (.mdata d b) with
    | some r => rw [Lean.Expr.replaceNoCache, hfe]; exact ⟨(hf _ r hfe).1, (hf _ r hfe).2 L⟩
    | none =>
      rw [Lean.Expr.replaceNoCache, hfe]
      simp only [NoPh, BvarLt, Lean.Expr.updateMData!, Lean.mkMData] at hn hb ⊢
      exact replaceNoCache_ph f hf b L hn hb
  | .letE nm t v b nd, L, hn, hb => by
    cases hfe : f (.letE nm t v b nd) with
    | some r => rw [Lean.Expr.replaceNoCache, hfe]; exact ⟨(hf _ r hfe).1, (hf _ r hfe).2 L⟩
    | none =>
      rw [Lean.Expr.replaceNoCache, hfe]
      simp only [NoPh, BvarLt, Bool.and_eq_true, Lean.Expr.updateLetE!, Lean.Expr.updateLet!] at hn hb ⊢
      have h1 := replaceNoCache_ph f hf t L hn.1.1 hb.1.1
      have h2 := replaceNoCache_ph f hf v L hn.1.2 hb.1.2
      have h3 := replaceNoCache_ph f hf b (L + 1) hn.2 hb.2
      exact ⟨⟨⟨h1.1, h2.1⟩, h3.1⟩, ⟨⟨h1.2, h2.2⟩, h3.2⟩⟩
  | .app g a, L, hn, hb => by
    cases hfe : f (.app g a) with
    | some r => rw [Lean.Expr.replaceNoCache, hfe]; exact ⟨(hf _ r hfe).1, (hf _ r hfe).2 L⟩
    | none =>
      rw [Lean.Expr.replaceNoCache, hfe]
      simp only [NoPh, BvarLt, Bool.and_eq_true, Lean.Expr.updateApp!, Lean.mkApp] at hn hb ⊢
      have h1 := replaceNoCache_ph f hf g L hn.1 hb.1
      have h2 := replaceNoCache_ph f hf a L hn.2 hb.2
      exact ⟨⟨h1.1, h2.1⟩, ⟨h1.2, h2.2⟩⟩
  | .proj s i b, L, hn, hb => by
    cases hfe : f (.proj s i b) with
    | some r => rw [Lean.Expr.replaceNoCache, hfe]; exact ⟨(hf _ r hfe).1, (hf _ r hfe).2 L⟩
    | none =>
      rw [Lean.Expr.replaceNoCache, hfe]
      simp only [NoPh, BvarLt, Lean.Expr.updateProj!, Lean.mkProj] at hn hb ⊢
      exact replaceNoCache_ph f hf b L hn hb
  | .bvar i, L, hn, hb => by
    cases hfe : f (.bvar i) with
    | some r => rw [Lean.Expr.replaceNoCache, hfe] <;> first | exact ⟨(hf _ r hfe).1, (hf _ r hfe).2 L⟩ | (intros; rename_i h; cases h)
    | none => rw [Lean.Expr.replaceNoCache, hfe] <;> first | exact ⟨hn, hb⟩ | (intros; rename_i h; cases h)
  | .fvar i, L, hn, hb => by
    cases hfe : f (.fvar i) with
    | some r => rw [Lean.Expr.replaceNoCache, hfe] <;> first | exact ⟨(hf _ r hfe).1, (hf _ r hfe).2 L⟩ | (intros; rename_i h; cases h)
    | none => rw [Lean.Expr.replaceNoCache, hfe] <;> first | exact ⟨hn, hb⟩ | (intros; rename_i h; cases h)
  | .mvar i, L, hn, hb => by
    cases hfe : f (.mvar i) with
    | some r => rw [Lean.Expr.replaceNoCache, hfe] <;> first | exact ⟨(hf _ r hfe).1, (hf _ r hfe).2 L⟩ | (intros; rename_i h; cases h)
    | none => rw [Lean.Expr.replaceNoCache, hfe] <;> first | exact ⟨hn, hb⟩ | (intros; rename_i h; cases h)
  | .sort u, L, hn, hb => by
    cases hfe : f (.sort u) with
    | some r => rw [Lean.Expr.replaceNoCache, hfe] <;> first | exact ⟨(hf _ r hfe).1, (hf _ r hfe).2 L⟩ | (intros; rename_i h; cases h)
    | none => rw [Lean.Expr.replaceNoCache, hfe] <;> first | exact ⟨hn, hb⟩ | (intros; rename_i h; cases h)
  | .const c us, L, hn, hb => by
    cases hfe : f (.const c us) with
    | some r => rw [Lean.Expr.replaceNoCache, hfe] <;> first | exact ⟨(hf _ r hfe).1, (hf _ r hfe).2 L⟩ | (intros; rename_i h; cases h)
    | none => rw [Lean.Expr.replaceNoCache, hfe] <;> first | exact ⟨hn, hb⟩ | (intros; rename_i h; cases h)
  | .lit l, L, hn, hb => by
    cases hfe : f (.lit l) with
    | some r => rw [Lean.Expr.replaceNoCache, hfe] <;> first | exact ⟨(hf _ r hfe).1, (hf _ r hfe).2 L⟩ | (intros; rename_i h; cases h)
    | none => rw [Lean.Expr.replaceNoCache, hfe] <;> first | exact ⟨hn, hb⟩ | (intros; rename_i h; cases h)

theorem zeroLit_ph (hz : Tools.Assume.N3Extern.ZeroLitAgrees0) {L : Nat} {e : Lean.Expr}
    (hn : NoPh e = true) (hb : BvarLt L e = true) :
    NoPh (Sparkle.Compiler.MachRawSurface.zeroLit inlNatLit canonicalNatLitValue? e) = true ∧
    BvarLt L (Sparkle.Compiler.MachRawSurface.zeroLit inlNatLit canonicalNatLitValue? e) = true := by
  rw [hz e (noPh_letOk 0 e hn)]
  refine replaceNoCache_ph _ ?_ e L hn hb
  intro x r hx
  unfold Tools.Assume.N3Extern.zeroLitF at hx
  split at hx
  · obtain ⟨k, -, rfl⟩ := Option.map_eq_some_iff.mp hx
    have h0 := inlNatLit_ph k 0
    have h1 := inlNatLit_ph 0 0
    refine ⟨?_, fun L' => ?_⟩
    · simp only [mkApp2, mkApp, NoPh, Bool.and_eq_true, Bool.true_and]; exact ⟨h0.1, h1.1⟩
    · have h0' := inlNatLit_ph k L'
      have h1' := inlNatLit_ph 0 L'
      simp only [mkApp2, mkApp, BvarLt, Bool.and_eq_true, Bool.true_and]; exact ⟨h0'.2, h1'.2⟩
  · simp at hx

/-! ## `machLoopAsLet` -/

theorem machLoopAsLet_ph {L : Nat} : ∀ e : Lean.Expr, NoPh e = true → BvarLt L e = true →
    NoPh (machLoopAsLet e) = true ∧ BvarLt L (machLoopAsLet e) = true := by
  intro e
  induction e generalizing L with
  | letE nm t v b nd iht ihv ihb =>
    intro hn hb
    simp only [NoPh, BvarLt, Bool.and_eq_true, machLoopAsLet] at hn hb ⊢
    have h := ihb (L := L + 1) hn.2 hb.2
    exact ⟨⟨hn.1, h.1⟩, ⟨hb.1, h.2⟩⟩
  | _ =>
    intro hn hb
    unfold machLoopAsLet
    first
      | exact ⟨hn, hb⟩
      | (split <;> first | exact ⟨hn, hb⟩ | simp_all [NoPh, BvarLt, mkApp2, mkApp])

/-! ## `mixedGatePeel` -/

theorem mixedGatePeel_ph {L : Nat} : ∀ (e : Lean.Expr) (bs : List (Name × MixedGateBinder)) (b : Lean.Expr),
    mixedGatePeel e = some (bs, b) → NoPh e = true → BvarLt L e = true →
    NoPh b = true ∧ BvarLt (L + bs.length) b = true
  | .lam nm ty body bi, bs, b, h, hn, hb => by
    simp only [NoPh, BvarLt, Bool.and_eq_true] at hn hb
    unfold mixedGatePeel at h
    cases hk : mixedGateBinderKind? ty with
    | none => simp [hk] at h
    | some kind =>
      cases hp : mixedGatePeel body with
      | none => simp [hk, hp] at h
      | some r =>
        obtain ⟨bs', e'⟩ := r
        simp only [hk, hp, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have := mixedGatePeel_ph (L := L + 1) body bs' e' hp hn.2 hb.2
        refine ⟨this.1, ?_⟩
        have e1 : L + (((nm, kind) :: bs').length) = L + 1 + bs'.length := by simp; omega
        rw [e1]; exact this.2
  | .bvar _, bs, b, h, hn, hb => by
    unfold mixedGatePeel at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact ⟨hn, by simpa using hb⟩
  | .fvar _, bs, b, h, hn, hb => by
    unfold mixedGatePeel at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact ⟨hn, by simpa using hb⟩
  | .mvar _, bs, b, h, hn, hb => by
    unfold mixedGatePeel at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact ⟨hn, by simpa using hb⟩
  | .sort _, bs, b, h, hn, hb => by
    unfold mixedGatePeel at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact ⟨hn, by simpa using hb⟩
  | .const _ _, bs, b, h, hn, hb => by
    unfold mixedGatePeel at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact ⟨hn, by simpa using hb⟩
  | .lit _, bs, b, h, hn, hb => by
    unfold mixedGatePeel at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact ⟨hn, by simpa using hb⟩
  | .app _ _, bs, b, h, hn, hb => by
    unfold mixedGatePeel at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact ⟨hn, by simpa using hb⟩
  | .forallE _ _ _ _, bs, b, h, hn, hb => by
    unfold mixedGatePeel at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact ⟨hn, by simpa using hb⟩
  | .letE _ _ _ _ _, bs, b, h, hn, hb => by
    unfold mixedGatePeel at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact ⟨hn, by simpa using hb⟩
  | .mdata _ _, bs, b, h, hn, hb => by
    unfold mixedGatePeel at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact ⟨hn, by simpa using hb⟩
  | .proj _ _ _, bs, b, h, hn, hb => by
    unfold mixedGatePeel at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact ⟨hn, by simpa using hb⟩

/-! ## `machRoot` -/

/-- the root `let` values, listed outermost first: the k-th sits under `k` extra binders. -/
def LetsPh (L : Nat) (l : List (Name × Lean.Expr × Lean.Expr)) : Prop :=
  ∀ (k : Nat) (x : Name × Lean.Expr × Lean.Expr), l[k]? = some x → NoPh x.2.2 = true ∧ BvarLt (k + L) x.2.2 = true

theorem letsPh_snoc {L : Nat} {l : List (Name × Lean.Expr × Lean.Expr)} (hl : LetsPh L l)
    (x : Name × Lean.Expr × Lean.Expr) (hn : NoPh x.2.2 = true) (hb : BvarLt (l.length + L) x.2.2 = true) :
    LetsPh L (l ++ [x]) := by
  intro k y hk
  by_cases hlt : k < l.length
  · rw [List.getElem?_append_left hlt] at hk
    exact hl k y hk
  · have hk' : k = l.length := by
      rcases Nat.lt_or_ge l.length k with h | h
      · rw [List.getElem?_append_right (by omega)] at hk
        simp [List.getElem?_cons, show k - l.length ≠ 0 by omega] at hk
      · omega
    subst hk'
    rw [List.getElem?_append_right (by omega)] at hk
    simp at hk
    subst hk
    exact ⟨hn, hb⟩

theorem machRootLets_len : ∀ (e : Lean.Expr) (acc : List (Name × Lean.Expr × Lean.Expr)),
    acc.length ≤ (machRootLets e acc).1.length
  | .letE nm ty v b nd, acc => by
    rw [machRootLets]
    have := machRootLets_len b ((nm, ty, v) :: acc)
    simp at this ⊢; omega
  | .bvar _, acc => by rw [machRootLets]; exact Nat.le_refl _; all_goals (intros; rename_i h; cases h)
  | .fvar _, acc => by rw [machRootLets]; exact Nat.le_refl _; all_goals (intros; rename_i h; cases h)
  | .mvar _, acc => by rw [machRootLets]; exact Nat.le_refl _; all_goals (intros; rename_i h; cases h)
  | .sort _, acc => by rw [machRootLets]; exact Nat.le_refl _; all_goals (intros; rename_i h; cases h)
  | .const _ _, acc => by rw [machRootLets]; exact Nat.le_refl _; all_goals (intros; rename_i h; cases h)
  | .lit _, acc => by rw [machRootLets]; exact Nat.le_refl _; all_goals (intros; rename_i h; cases h)
  | .app _ _, acc => by rw [machRootLets]; exact Nat.le_refl _; all_goals (intros; rename_i h; cases h)
  | .lam _ _ _ _, acc => by rw [machRootLets]; exact Nat.le_refl _; all_goals (intros; rename_i h; cases h)
  | .forallE _ _ _ _, acc => by rw [machRootLets]; exact Nat.le_refl _; all_goals (intros; rename_i h; cases h)
  | .mdata _ _, acc => by rw [machRootLets]; exact Nat.le_refl _; all_goals (intros; rename_i h; cases h)
  | .proj _ _ _, acc => by rw [machRootLets]; exact Nat.le_refl _; all_goals (intros; rename_i h; cases h)

theorem machRootLets_ph {L : Nat} : ∀ (e : Lean.Expr) (acc : List (Name × Lean.Expr × Lean.Expr)),
    NoPh e = true → BvarLt (L + acc.length) e = true → LetsPh L acc.reverse →
    LetsPh L (machRootLets e acc).1.reverse ∧ NoPh (machRootLets e acc).2 = true ∧
      BvarLt (L + (machRootLets e acc).1.length) (machRootLets e acc).2 = true
  | .letE nm ty v b nd, acc, hn, hb, hacc => by
    simp only [NoPh, BvarLt, Bool.and_eq_true] at hn hb
    rw [machRootLets]
    have hacc' : LetsPh L ((nm, ty, v) :: acc).reverse := by
      rw [List.reverse_cons]
      refine letsPh_snoc hacc _ hn.1.2 ?_
      rw [List.length_reverse, Nat.add_comm]; exact hb.1.2
    refine machRootLets_ph b _ hn.2 ?_ hacc'
    have : L + ((nm, ty, v) :: acc).length = L + acc.length + 1 := by simp only [List.length_cons]; omega
    rw [this]; exact hb.2
  | .bvar j, acc, hn, hb, hacc => by
    rw [machRootLets]; exact ⟨hacc, hn, hb⟩
    all_goals (intros; rename_i h; cases h)
  | .fvar _, acc, hn, hb, hacc => by
    rw [machRootLets]; exact ⟨hacc, hn, hb⟩
    all_goals (intros; rename_i h; cases h)
  | .mvar _, acc, hn, hb, hacc => by
    rw [machRootLets]; exact ⟨hacc, hn, hb⟩
    all_goals (intros; rename_i h; cases h)
  | .sort _, acc, hn, hb, hacc => by
    rw [machRootLets]; exact ⟨hacc, hn, hb⟩
    all_goals (intros; rename_i h; cases h)
  | .const _ _, acc, hn, hb, hacc => by
    rw [machRootLets]; exact ⟨hacc, hn, hb⟩
    all_goals (intros; rename_i h; cases h)
  | .lit _, acc, hn, hb, hacc => by
    rw [machRootLets]; exact ⟨hacc, hn, hb⟩
    all_goals (intros; rename_i h; cases h)
  | .app _ _, acc, hn, hb, hacc => by
    rw [machRootLets]; exact ⟨hacc, hn, hb⟩
    all_goals (intros; rename_i h; cases h)
  | .lam _ _ _ _, acc, hn, hb, hacc => by
    rw [machRootLets]; exact ⟨hacc, hn, hb⟩
    all_goals (intros; rename_i h; cases h)
  | .forallE _ _ _ _, acc, hn, hb, hacc => by
    rw [machRootLets]; exact ⟨hacc, hn, hb⟩
    all_goals (intros; rename_i h; cases h)
  | .mdata _ _, acc, hn, hb, hacc => by
    rw [machRootLets]; exact ⟨hacc, hn, hb⟩
    all_goals (intros; rename_i h; cases h)
  | .proj _ _ _, acc, hn, hb, hacc => by
    rw [machRootLets]; exact ⟨hacc, hn, hb⟩
    all_goals (intros; rename_i h; cases h)

/-- the answer of `machRoot`: the root lets, the enclosing run (its four parts, after `machRunApp?`) and the root. -/
def RootPhOut (L : Nat) (r : List (Name × Lean.Expr × Lean.Expr) × Option (Name × Nat × Nat) × Option Lean.Expr × Lean.Expr) : Prop :=
  LetsPh L r.1 ∧
  (∀ dom αs ie b, r.2.2.1.bind machRunApp? = some (dom, αs, ie, b) →
      NoPh dom = true ∧ BvarLt (r.1.length + L) dom = true ∧ NoPh b = true ∧ BvarLt (r.1.length + 1 + L) b = true) ∧
  NoPh r.2.2.2 = true ∧ BvarLt (r.1.length + L) r.2.2.2 = true

theorem machRoot_ph_base {L : Nat} (projs : Name → Option (Name × Nat × Nat)) (e : Lean.Expr)
    (hnl : ∀ nm t v b nd, e ≠ Lean.Expr.letE nm t v b nd) (acc : List (Name × Lean.Expr × Lean.Expr))
    (hn : NoPh e = true) (hb : BvarLt (L + acc.length) e = true) (hacc : LetsPh L acc.reverse) :
    RootPhOut L (machRoot projs e acc) := by
    unfold machRoot
    split
    · exact absurd rfl (hnl _ _ _ _ _)
    rename_i hne
    have hb0 : BvarLt (acc.reverse.length + L) e = true := by
      rw [List.length_reverse, Nat.add_comm]; exact hb
    have hs := inlSpine_ph0 hn hb
    split
    · rename_i hrun
      refine ⟨hacc, ?_, hn, hb0⟩
      intro dom αs ie b hq
      simp only [Option.bind_some] at hq
      have hph := machRunApp?_ph hn hb0 hq
      exact ⟨hph.1.1, hph.1.2, hph.2.2.2.1, bvarLt_mono (by simp only [List.length_reverse]; omega) hph.2.2.2.2⟩
    · rcases hsp : inlSpine _ [] with ⟨fn, args⟩
      simp only [hsp] at hs ⊢
      split
      · rename_i p ls args' heq
        have ha : args' = args := by
          first | exact (Prod.mk.inj heq).2 | exact (Prod.mk.inj heq).2.symm
        subst ha
        split
        · rename_i ctor np idx r hproj hlast
          have hr := hs r (List.mem_of_getLast? hlast)
          have hq := machRootLets_ph (L := L) r acc hr.1 hr.2 hacc
          have hlen := machRootLets_len r acc
          generalize machRootLets r acc = q at hq hlen ⊢
          obtain ⟨acc', r'⟩ := q
          dsimp only at hq hlen ⊢
          split
          · refine ⟨hq.1, ?_, hn, ?_⟩
            · intro dom αs ie b hq'
              simp only [Option.bind_some, List.length_reverse] at hq'
              have hph := machRunApp?_ph (L := L + acc'.length) hq.2.1 hq.2.2 hq'
              refine ⟨hph.1.1, bvarLt_mono (by simp only [List.length_reverse]; omega) hph.1.2, hph.2.2.2.1,
                bvarLt_mono (by simp only [List.length_reverse]; omega) hph.2.2.2.2⟩
            · rw [List.length_reverse, Nat.add_comm]
              exact bvarLt_mono (by omega) hb
          · refine ⟨hacc, ?_, hn, hb0⟩
            intro dom αs ie b hq'; simp at hq'
        · refine ⟨hacc, ?_, hn, hb0⟩
          intro dom αs ie b hq'; simp at hq'
      · refine ⟨hacc, ?_, hn, hb0⟩
        intro dom αs ie b hq'; simp at hq'


theorem machRoot_ph {L : Nat} (projs : Name → Option (Name × Nat × Nat)) :
    ∀ (e : Lean.Expr) (acc : List (Name × Lean.Expr × Lean.Expr)),
      NoPh e = true → BvarLt (L + acc.length) e = true → LetsPh L acc.reverse →
      RootPhOut L (machRoot projs e acc) := by
  intro e
  induction e with
  | letE nm t v b nd iht ihv ihb =>
    intro acc hn hb hacc
    simp only [NoPh, BvarLt, Bool.and_eq_true] at hn hb
    rw [machRoot]
    have hacc' : LetsPh L ((nm, t, v) :: acc).reverse := by
      rw [List.reverse_cons]
      refine letsPh_snoc hacc _ hn.1.2 ?_
      rw [List.length_reverse, Nat.add_comm]; exact hb.1.2
    refine ihb _ hn.2 ?_ hacc'
    have : L + ((nm, t, v) :: acc).length = L + acc.length + 1 := by simp only [List.length_cons]; omega
    rw [this]; exact hb.2
  | _ =>
    intro acc hn hb hacc
    exact machRoot_ph_base projs _ (by intro nm t v b nd h; cases h) acc hn hb hacc

/-! ## `shapeMid` and `ShapeInputs` -/

/-- the `NoPh ∧ BvarLt` content of `MidInputs` for a given `shapeMid` (everything except `p.bs.length ≤ nDecl` and `DomAtomic dom`),
at the bound `L` of the normalised body. -/
def MidPh (L : Nat) (m : ShapeMid) : Prop :=
  LetsPh L m.rootLets ∧
  (∀ (dom αs ie b : Lean.Expr), m.run? = some (dom, αs, ie, b) →
      NoPh dom = true ∧ BvarLt (m.rootLets.length + L) dom = true ∧
      NoPh b = true ∧ BvarLt (m.rootLets.length + 1 + L) b = true) ∧
  (m.run? = none → NoPh m.root = true ∧ BvarLt (m.rootLets.length + L) m.root = true)

theorem shapeMid_ph (hz : Tools.Assume.N3Extern.ZeroLitAgrees0) (hrf : RootFloatAgrees) (senv : StructEnv) (p : ShapePre)
    {en : Lean.Expr} {L : Nat} (hn : NoPh en = true) (hb : BvarLt L en = true) :
    MidPh L (shapeMid senv p en) := by
  have h1 := inlFoldNat_ph (L := L) en hn hb
  have h2 := zeroLit_ph hz h1.1 h1.2
  have h3 := rootFloat_ph hrf h2.1 h2.2
  have h4 := machLoopAsLet_ph (L := L) _ h3.1 h3.2
  have hroot := machRoot_ph (L := L) senv.proj _ [] h4.1 (by simpa using h4.2) (by intro k x hx; simp at hx)
  rcases hq0 : machRoot senv.proj
    (machLoopAsLet (Sparkle.Compiler.MachRawSurface.rootFloat
      (Sparkle.Compiler.MachRawSurface.zeroLit inlNatLit canonicalNatLitValue? (inlFoldNat en)))) [] with
    ⟨rl, sel, run0, root⟩
  rw [hq0] at hroot
  obtain ⟨hl, hrun, hrn, hrb⟩ := hroot
  dsimp only at hl hrun hrn hrb
  simp only [shapeMid, hq0]
  refine ⟨hl, ?_, fun _ => ⟨hrn, hrb⟩⟩
  intro dom αs ie b h
  split at h
  · -- a wrapped result: the run is the last argument of the root
    rename_i W hW
    obtain ⟨r, hr, hq⟩ := Option.bind_eq_some_iff.mp h
    have hbk : root.getAppArgs.back? = some r := by
      split at hr
      · exact hr
      · exact absurd hr (by simp)
    have hmem : r ∈ root.getAppArgs := Array.mem_of_back? hbk
    have hr' := phArgs_getAppArgs hrn hrb r hmem
    have hph := machRunApp?_ph hr'.1 hr'.2 hq
    exact ⟨hph.1.1, hph.1.2, hph.2.2.2.1, by rw [Nat.add_assoc, Nat.add_comm 1 L, ← Nat.add_assoc]; exact hph.2.2.2.2⟩
  · exact hrun dom αs ie b h

theorem shapeInputs_of (hz : Tools.Assume.N3Extern.ZeroLitAgrees0) (hrf : RootFloatAgrees)
    {nDecl : Nat} {senv : StructEnv} {sm : Bool} {ps : List (String × Nat)} {ci : ConstantInfo} {n : Nat}
    (hdecl : ∀ d, ci = ConstantInfo.defnInfo d → NoPh d.value = true ∧ BvarLt 0 d.value = true)
    (hpack : ∀ (L : Nat) (e : Lean.Expr), NoPh e = true → BvarLt L e = true →
      NoPh (Sparkle.Compiler.MachTupleIn.packTupleInputs e) = true ∧
        BvarLt L (Sparkle.Compiler.MachTupleIn.packTupleInputs e) = true)
    (hnorm : ∀ (L : Nat) (e en : Lean.Expr), NoPh e = true → BvarLt L e = true → machNormF n senv e = some en →
      NoPh en = true ∧ BvarLt L en = true)
    (hdom : ∀ (p : ShapePre) (en : Lean.Expr), shapePre sm ps ci senv = some p → machNormF n senv p.e = some en →
      ∀ (dom αs ie b : Lean.Expr), (shapeMid senv p en).run? = some (dom, αs, ie, b) → DomAtomic dom)
    (hbs : ∀ p : ShapePre, shapePre sm ps ci senv = some p → p.bs.length ≤ nDecl) :
    ShapeInputs nDecl senv sm ps ci n := by
  intro p en hp hen
  obtain ⟨hci, hpeel, -⟩ := shapePre_facts hp
  have hd := hdecl p.d hci
  have h1 := hpack 0 _ hd.1 hd.2
  have h2 := mixedGatePeel_ph (L := 0) _ p.bs p.e hpeel h1.1 h1.2
  rw [Nat.zero_add] at h2
  have h3 := hnorm p.bs.length p.e en h2.1 h2.2 hen
  have hm := shapeMid_ph hz hrf senv p h3.1 h3.2
  have hle := hbs p hp
  refine ⟨hle, ?_, ?_, ?_⟩
  · intro k x hx
    have := hm.1 k x hx
    exact ⟨this.1, bvarLt_mono (by omega) this.2⟩
  · intro dom αs ie b hr
    have := hm.2.1 dom αs ie b hr
    exact ⟨this.1, bvarLt_mono (by omega) this.2.1, hdom p en hp hen dom αs ie b hr, this.2.2.1,
      bvarLt_mono (by omega) this.2.2.2⟩
  · intro hr
    have := hm.2.2 hr
    exact ⟨this.1, bvarLt_mono (by omega) this.2⟩

end Tools.ShippingGen5ReaderTrace
