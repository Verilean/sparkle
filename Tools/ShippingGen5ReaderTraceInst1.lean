import Tools.ShippingGen5ReaderTraceLift
import Tools.ShippingLetsExternSpec
set_option autoImplicit false
-- NOT BUILT yet (pending Pod build). Written against freeze rev9 `scripts/gen5/DG_READERTRACE_FREEZE_REV9.md` §1 (Inst1Ph as a lemma from the existing `Inst1Agrees`, T1L-51); clean issue-linked build pending (coder). No sorry / axiom / native_decide in source.

/-! # DG-READERTRACE: `Inst1Ph` — `Expr.instantiate1` preserves `NoPh` / `BvarLt` (lemma from the existing `Inst1Agrees`)

Structural lemmas about the total model `inst1Spec` (`Tools/ShippingLetsExternSpec.lean`), same method as `inst1Spec_ok`. The only link to the C++ `instantiate1` is the existing named hypothesis
`Inst1Agrees` (T1L-51, unrestricted equation); no new premise. Note: the `BvarLt` lemma takes `BvarLt m' a` (not the lifted form) so the binder induction goes through; `liftSpec_bvarLt` supplies the lifted form. -/

namespace Tools.ShippingGen5ReaderTrace
open Lean Tools.ShippingLetsReaderInv

theorem inst1Spec_noPh : ∀ (b a : Lean.Expr) (off : Nat), NoPh b = true → NoPh a = true →
    NoPh (inst1Spec b a off) = true := by
  intro b a
  induction b with
  | bvar i =>
    intro off _ ha
    unfold inst1Spec
    split
    · rfl
    · split
      · exact liftSpec_noPh a 0 off ha
      · rfl
  | app f x ihf ihx =>
    intro off h ha; simp only [NoPh, Bool.and_eq_true] at h
    simp only [inst1Spec, NoPh, Bool.and_eq_true]; exact ⟨ihf _ h.1 ha, ihx _ h.2 ha⟩
  | lam _ t b _ iht ihb =>
    intro off h ha; simp only [NoPh, Bool.and_eq_true] at h
    simp only [inst1Spec, NoPh, Bool.and_eq_true]; exact ⟨iht _ h.1 ha, ihb _ h.2 ha⟩
  | forallE _ t b _ iht ihb =>
    intro off h ha; simp only [NoPh, Bool.and_eq_true] at h
    simp only [inst1Spec, NoPh, Bool.and_eq_true]; exact ⟨iht _ h.1 ha, ihb _ h.2 ha⟩
  | letE _ t v b _ iht ihv ihb =>
    intro off h ha; simp only [NoPh, Bool.and_eq_true] at h
    simp only [inst1Spec, NoPh, Bool.and_eq_true]
    exact ⟨⟨iht _ h.1.1 ha, ihv _ h.1.2 ha⟩, ihb _ h.2 ha⟩
  | mdata _ e ih => intro off h ha; simp only [NoPh] at h; simp only [inst1Spec, NoPh]; exact ih _ h ha
  | proj _ _ e ih => intro off h ha; simp only [NoPh] at h; simp only [inst1Spec, NoPh]; exact ih _ h ha
  | fvar _ => intro off h _; exact h
  | mvar _ => intro off _ _; rfl
  | sort _ => intro off _ _; rfl
  | const _ _ => intro off _ _; rfl
  | lit _ => intro off _ _; rfl

theorem inst1Spec_bvarLt : ∀ (b a : Lean.Expr) (off m m' : Nat), BvarLt (m + 1 + off) b = true →
    BvarLt m' a = true → m ≤ m' → BvarLt (m' + off) (inst1Spec b a off) = true := by
  intro b a
  induction b with
  | bvar i =>
    intro off m m' h ha hm
    simp only [BvarLt, decide_eq_true_eq] at h
    unfold inst1Spec
    split
    · simp only [BvarLt, decide_eq_true_eq]; omega
    · split
      · exact liftSpec_bvarLt a 0 off m' ha
      · simp only [BvarLt, decide_eq_true_eq]; omega
  | app f x ihf ihx =>
    intro off m m' h ha hm; simp only [BvarLt, Bool.and_eq_true] at h
    simp only [inst1Spec, BvarLt, Bool.and_eq_true]; exact ⟨ihf _ _ _ h.1 ha hm, ihx _ _ _ h.2 ha hm⟩
  | lam _ t b _ iht ihb =>
    intro off m m' h ha hm; simp only [BvarLt, Bool.and_eq_true] at h
    simp only [inst1Spec, BvarLt, Bool.and_eq_true]
    refine ⟨iht _ _ _ h.1 ha hm, ?_⟩
    have := ihb (off + 1) m m' (by rw [show m + 1 + (off + 1) = m + 1 + off + 1 by omega]; exact h.2) ha hm
    rwa [show m' + (off + 1) = m' + off + 1 by omega] at this
  | forallE _ t b _ iht ihb =>
    intro off m m' h ha hm; simp only [BvarLt, Bool.and_eq_true] at h
    simp only [inst1Spec, BvarLt, Bool.and_eq_true]
    refine ⟨iht _ _ _ h.1 ha hm, ?_⟩
    have := ihb (off + 1) m m' (by rw [show m + 1 + (off + 1) = m + 1 + off + 1 by omega]; exact h.2) ha hm
    rwa [show m' + (off + 1) = m' + off + 1 by omega] at this
  | letE _ t v b _ iht ihv ihb =>
    intro off m m' h ha hm; simp only [BvarLt, Bool.and_eq_true] at h
    simp only [inst1Spec, BvarLt, Bool.and_eq_true]
    refine ⟨⟨iht _ _ _ h.1.1 ha hm, ihv _ _ _ h.1.2 ha hm⟩, ?_⟩
    have := ihb (off + 1) m m' (by rw [show m + 1 + (off + 1) = m + 1 + off + 1 by omega]; exact h.2) ha hm
    rwa [show m' + (off + 1) = m' + off + 1 by omega] at this
  | mdata _ e ih => intro off m m' h ha hm; simp only [BvarLt] at h; simp only [inst1Spec, BvarLt]; exact ih _ _ _ h ha hm
  | proj _ _ e ih => intro off m m' h ha hm; simp only [BvarLt] at h; simp only [inst1Spec, BvarLt]; exact ih _ _ _ h ha hm
  | fvar _ => intro _ _ _ _ _ _; rfl
  | mvar _ => intro _ _ _ _ _ _; rfl
  | sort _ => intro _ _ _ _ _ _; rfl
  | const _ _ => intro _ _ _ _ _ _; rfl
  | lit _ => intro _ _ _ _ _ _; rfl

/-- the Ph form of T1L-51, as a statement about `Expr.instantiate1` -/
def Inst1Ph : Prop := ∀ (b a : Lean.Expr) (m m' : Nat), NoPh b = true → NoPh a = true →
    BvarLt (m + 1) b = true → BvarLt m' a = true → m ≤ m' →
    NoPh (b.instantiate1 a) = true ∧ BvarLt m' (b.instantiate1 a) = true

theorem inst1Ph_of_agrees (h : Inst1Agrees) : Inst1Ph := by
  intro b a m m' hb ha hbl hal hm
  rw [h b a]
  refine ⟨inst1Spec_noPh b a 0 hb ha, ?_⟩
  simpa using inst1Spec_bvarLt b a 0 m m' (by simpa using hbl) hal hm

end Tools.ShippingGen5ReaderTrace
