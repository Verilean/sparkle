import Tools.ShippingGen5ReaderTraceCtl
import Tools.ShippingLetsExternSpec
set_option autoImplicit false
-- Built in Pod (kjob lake build Tools.ShippingGen5ReaderTraceLift, exit 0) on the tree of f053d6018560ba5dfe5d501bb447716ba5c1bd6f (this header is comment-only). Written against freeze rev7 `scripts/gen5/DG_READERTRACE_FREEZE_REV7.md` §2 (U-R4c, part 2); clean issue-linked build pending (coder). No sorry / axiom / native_decide in source.

/-! # DG-READERTRACE U-R4c (part 2): `liftSpec` / `rootFloatS` preserve `NoPh` and `BvarLt`

Structural lemmas about the total models `liftSpec` / `rootFloatS` (`Tools/ShippingLetsExternSpec.lean`), same method as `liftSpec_ok` / `rootFloatS_ok`. They use no extern fact and no
`LiftAgrees` / `RootFloatAgrees`: the connection `Expr.liftLooseBVars = liftSpec` / `rootFloat = rootFloatS` is a named hypothesis of the arm unit (U-R5), not of this file.
Not supplied: U-R4d, U-R5, `TraceGood senv nDecl (readF senv n)`, the real run and FG. -/

namespace Tools.ShippingGen5ReaderTrace
open Lean Tools.ShippingLetsReaderInv

theorem liftSpec_noPh : ∀ (e : Lean.Expr) (s d : Nat), NoPh e = true → NoPh (liftSpec e s d) = true := by
  intro e
  induction e with
  | bvar i => intro s d _; unfold liftSpec; split <;> rfl
  | app f a ihf iha =>
    intro s d h; simp only [NoPh, Bool.and_eq_true] at h
    simp only [liftSpec, NoPh, Bool.and_eq_true]; exact ⟨ihf _ _ h.1, iha _ _ h.2⟩
  | lam _ t b _ iht ihb =>
    intro s d h; simp only [NoPh, Bool.and_eq_true] at h
    simp only [liftSpec, NoPh, Bool.and_eq_true]; exact ⟨iht _ _ h.1, ihb _ _ h.2⟩
  | forallE _ t b _ iht ihb =>
    intro s d h; simp only [NoPh, Bool.and_eq_true] at h
    simp only [liftSpec, NoPh, Bool.and_eq_true]; exact ⟨iht _ _ h.1, ihb _ _ h.2⟩
  | letE _ t v b _ iht ihv ihb =>
    intro s d h; simp only [NoPh, Bool.and_eq_true] at h
    simp only [liftSpec, NoPh, Bool.and_eq_true]; exact ⟨⟨iht _ _ h.1.1, ihv _ _ h.1.2⟩, ihb _ _ h.2⟩
  | mdata _ e ih => intro s d h; simp only [NoPh] at h; simp only [liftSpec, NoPh]; exact ih _ _ h
  | proj _ _ e ih => intro s d h; simp only [NoPh] at h; simp only [liftSpec, NoPh]; exact ih _ _ h
  | fvar _ => intro s d h; exact h
  | mvar _ => intro s d _; rfl
  | sort _ => intro s d _; rfl
  | const _ _ => intro s d _; rfl
  | lit _ => intro s d _; rfl

theorem liftSpec_bvarLt : ∀ (e : Lean.Expr) (s d L : Nat), BvarLt L e = true →
    BvarLt (L + d) (liftSpec e s d) = true := by
  intro e
  induction e with
  | bvar i =>
    intro s d L h
    simp only [BvarLt, decide_eq_true_eq] at h
    unfold liftSpec
    split
    · simp only [BvarLt, decide_eq_true_eq]; omega
    · simp only [BvarLt, decide_eq_true_eq]; omega
  | app f a ihf iha =>
    intro s d L h; simp only [BvarLt, Bool.and_eq_true] at h
    simp only [liftSpec, BvarLt, Bool.and_eq_true]; exact ⟨ihf _ _ _ h.1, iha _ _ _ h.2⟩
  | lam _ t b _ iht ihb =>
    intro s d L h; simp only [BvarLt, Bool.and_eq_true] at h
    simp only [liftSpec, BvarLt, Bool.and_eq_true]
    refine ⟨iht _ _ _ h.1, ?_⟩
    have := ihb (s + 1) d (L + 1) h.2
    rwa [show L + 1 + d = L + d + 1 by omega] at this
  | forallE _ t b _ iht ihb =>
    intro s d L h; simp only [BvarLt, Bool.and_eq_true] at h
    simp only [liftSpec, BvarLt, Bool.and_eq_true]
    refine ⟨iht _ _ _ h.1, ?_⟩
    have := ihb (s + 1) d (L + 1) h.2
    rwa [show L + 1 + d = L + d + 1 by omega] at this
  | letE _ t v b _ iht ihv ihb =>
    intro s d L h; simp only [BvarLt, Bool.and_eq_true] at h
    simp only [liftSpec, BvarLt, Bool.and_eq_true]
    refine ⟨⟨iht _ _ _ h.1.1, ihv _ _ _ h.1.2⟩, ?_⟩
    have := ihb (s + 1) d (L + 1) h.2
    rwa [show L + 1 + d = L + d + 1 by omega] at this
  | mdata _ e ih => intro s d L h; simp only [BvarLt] at h; simp only [liftSpec, BvarLt]; exact ih _ _ _ h
  | proj _ _ e ih => intro s d L h; simp only [BvarLt] at h; simp only [liftSpec, BvarLt]; exact ih _ _ _ h
  | fvar _ => intro s d L _; rfl
  | mvar _ => intro s d L _; rfl
  | sort _ => intro s d L _; rfl
  | const _ _ => intro s d L _; rfl
  | lit _ => intro s d L _; rfl

theorem rootFloatS_noPh : ∀ e : Lean.Expr, NoPh e = true → NoPh (rootFloatS e) = true := by
  intro e
  induction e using rootFloatS.induct with
  | case1 nm t n2 t2 v2 w nd2 b nd ih =>
    intro he
    rw [rootFloatS]
    simp only [NoPh, Bool.and_eq_true, and_assoc] at he
    obtain ⟨ht, ht2, hv2, hw, hb⟩ := he
    refine ih ?_
    simp only [NoPh, Bool.and_eq_true, and_assoc]
    exact ⟨ht2, hv2, liftSpec_noPh t _ _ ht, hw, liftSpec_noPh b _ _ hb⟩
  | case2 nm t v b nd hv ih =>
    intro he
    rw [rootFloatS]
    · simp only [NoPh, Bool.and_eq_true] at he ⊢
      exact ⟨he.1, ih he.2⟩
    · exact hv
  | case3 f nm t v b nd ih =>
    intro he
    rw [rootFloatS]
    simp only [NoPh, Bool.and_eq_true, and_assoc] at he ⊢
    obtain ⟨hf, ht, hv, hb⟩ := he
    refine ⟨ht, hv, ih ?_⟩
    simp only [NoPh, Bool.and_eq_true]
    exact ⟨liftSpec_noPh f _ _ hf, hb⟩
  | case4 e h1 h2 h3 =>
    intro he
    rw [rootFloatS]
    · exact he
    · exact h1
    · exact h2
    · exact h3

theorem rootFloatS_bvarLt : ∀ (e : Lean.Expr) (L : Nat), BvarLt L e = true → BvarLt L (rootFloatS e) = true := by
  intro e
  induction e using rootFloatS.induct with
  | case1 nm t n2 t2 v2 w nd2 b nd ih =>
    intro L he
    rw [rootFloatS]
    simp only [BvarLt, Bool.and_eq_true, and_assoc] at he
    obtain ⟨ht, ht2, hv2, hw, hb⟩ := he
    refine ih L ?_
    simp only [BvarLt, Bool.and_eq_true, and_assoc]
    exact ⟨ht2, hv2, liftSpec_bvarLt t 0 1 L ht, hw, liftSpec_bvarLt b 1 1 (L + 1) hb⟩
  | case2 nm t v b nd hv ih =>
    intro L he
    rw [rootFloatS]
    · simp only [BvarLt, Bool.and_eq_true] at he ⊢
      exact ⟨he.1, ih (L + 1) he.2⟩
    · exact hv
  | case3 f nm t v b nd ih =>
    intro L he
    rw [rootFloatS]
    simp only [BvarLt, Bool.and_eq_true, and_assoc] at he ⊢
    obtain ⟨hf, ht, hv, hb⟩ := he
    refine ⟨ht, hv, ih (L + 1) ?_⟩
    simp only [BvarLt, Bool.and_eq_true]
    exact ⟨liftSpec_bvarLt f 0 1 L hf, hb⟩
  | case4 e h1 h2 h3 =>
    intro L he
    rw [rootFloatS]
    · exact he
    · exact h1
    · exact h2
    · exact h3

end Tools.ShippingGen5ReaderTrace
