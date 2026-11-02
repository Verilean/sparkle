import Tools.PassPh.Defs
set_option autoImplicit false
-- SKELETON: sorry あり、探索ブランチのみ（受理の対象ではない）. Built in Pod (kjob lake build Tools.PassPh.Pass, exit 0) on the tree of dec1b348 (Lean content identical; header comment-only). Types follow scripts/gen5/RT_PASS_PH_FREEZE.md rev1 (approved as document/types only).

/-! # pass_ph skeleton: ListLit group (listLit?_good). Depends on Defs only (Inst1Agrees + inst1Spec lemmas). -/

namespace Tools.PassPh
open Lean Tools.ShippingLetsReaderInv Tools.ShippingGen5ReaderTrace Tools.Assume.AbbrevExtern Sparkle.Compiler.MachRecUnfold

theorem bind_ok_M {γ β : Type} (m : Sparkle.Compiler.MachRecUnfold.M γ)
    (k : γ → Sparkle.Compiler.MachRecUnfold.M β) (b : β)
    (h : (m >>= k) = ExceptT.mk (some (.ok b))) :
    ∃ r, m = ExceptT.mk (some (.ok r)) ∧ k r = ExceptT.mk (some (.ok b)) := by
  suffices key : ∀ x : Option (Except String γ), (ExceptT.mk x >>= k) = ExceptT.mk (some (.ok b)) →
      ∃ r, (ExceptT.mk x : M γ) = ExceptT.mk (some (.ok r)) ∧ k r = ExceptT.mk (some (.ok b)) from key m.run h
  intro x h
  rcases x with _ | r
  · simp [bind, ExceptT.bind, ExceptT.mk] at h
  · cases r with
    | error e => simp [bind, ExceptT.bind, ExceptT.mk] at h <;> exact absurd (Option.some.inj h) (by simp)
    | ok r => exact ⟨r, rfl, by simpa [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont] using h⟩

theorem GL_app {L : Nat} {f a : Lean.Expr} (h : GL L (.app f a)) : GL L f ∧ GL L a := by
  simp only [GL, NoPh, BvarLt, Bool.and_eq_true] at h ⊢
  exact ⟨⟨h.1.1, h.2.1⟩, h.1.2, h.2.2⟩

theorem GL_mdata {L : Nat} {d : Lean.MData} {b : Lean.Expr} (h : GL L (.mdata d b)) : GL L b := by
  simpa [G, NoPh, BvarLt] using h

theorem listLit?_good_aux (hi1 : Inst1Agrees) (natLit? : Lean.Expr → Option Nat)
    (fuel L : Nat) (e α : Lean.Expr) (xs : List Lean.Expr) (hG : GL L e)
    (h : listLit? natLit? fuel e = ExceptT.mk (some (.ok (α, xs)))) : GL L α ∧ ∀ x ∈ xs, GL L x := by
  generalize he : e = e' at h
  unfold listLit? at h
  split at h
  case h_1 _ _ b =>
    subst he
    exact listLit?_good_aux hi1 natLit? fuel L b α xs (GL_mdata hG) h
  case h_2 _ _ _ v b _ =>
    subst he
    by_cases hv : v.hasLooseBVars = true
    · simp [hv, stuck, ExceptT.lift, ExceptT.mk] at h
    · rw [if_neg hv] at h
      cases fuel with
      | zero =>
        exact absurd (Option.some.inj h) (by simp)
      | succ n =>
        have hG' : GL L (b.instantiate1 v) := by
          simp only [GL, NoPh, BvarLt, Bool.and_eq_true] at hG
          have := inst1Ph_of_agrees hi1 b v L L hG.1.2 hG.1.1.2 hG.2.2 hG.2.1.2 (Nat.le_refl L)
          exact ⟨this.1, this.2⟩
        exact listLit?_good_aux hi1 natLit? n L _ α xs hG' h
  case h_3 =>
    subst he
    simp [pure, ExceptT.pure, ExceptT.mk] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨(GL_app hG).2, by simp⟩
  case h_4 _ _ α' a rest =>
    subst he
    obtain ⟨⟨_, ys⟩, hm, hk⟩ := bind_ok_M _ _ _ h
    simp [pure, ExceptT.pure, ExceptT.mk] at hk
    obtain ⟨rfl, rfl⟩ := hk
    have h1 := GL_app hG
    have h2 := GL_app h1.1
    have h3 := GL_app h2.1
    have ih := listLit?_good_aux hi1 natLit? fuel L rest _ ys h1.2 hm
    exact ⟨h3.2, by simpa [h2.2] using ih.2⟩
  case h_5 _ _ _ a =>
    subst he
    exact listLit?_good_aux hi1 natLit? fuel L a α xs (GL_app hG).2 h
  case h_6 _ _ _ l =>
    subst he
    exact listLit?_good_aux hi1 natLit? fuel L l α xs (GL_app hG).2 h
  case h_7 _ _ _ l =>
    subst he
    exact listLit?_good_aux hi1 natLit? fuel L l α xs (GL_app hG).2 h
  case h_8 _ _ α' l n =>
    subst he
    obtain ⟨⟨_, ys⟩, hm, hk⟩ := bind_ok_M _ _ _ h
    obtain ⟨n0, hn, hk2⟩ := bind_ok_M _ _ _ hk
    simp [pure, ExceptT.pure, ExceptT.mk] at hk2
    obtain ⟨rfl, rfl⟩ := hk2
    have h1 := GL_app hG
    have h2 := GL_app h1.1
    have h3 := GL_app h2.1
    have ih := listLit?_good_aux hi1 natLit? fuel L l _ ys h2.2 hm
    refine ⟨?_, ?_⟩
    · have := h3.2
      simp only [GL, NoPh, BvarLt, Bool.and_eq_true, mkApp2, mkApp] at this ⊢
      simp [this]
    · intro x hx
      simp only [List.mem_map] at hx
      obtain ⟨⟨a, i⟩, hai, rfl⟩ := hx
      have ha := ih.2 a (List.fst_mem_of_mem_zipIdx hai)
      have := h3.2
      simp only [GL, NoPh, BvarLt, Bool.and_eq_true, mkApp4, mkApp, natLitE, mkApp3] at this ha ⊢
      simp [this, ha]
  case h_9 =>
    simp [stuck, ExceptT.lift, ExceptT.mk] at h
termination_by (fuel, sizeOf e)
decreasing_by
  all_goals simp_wf
  all_goals first | (apply Prod.Lex.left; omega) | (apply Prod.Lex.right; (try simp); (try rw [he]); simp; omega)

theorem listLit?_goodL (hi1 : Inst1Agrees) (natLit? : Lean.Expr → Option Nat) :
    ∀ (fuel L : Nat) (e α : Lean.Expr) (xs : List Lean.Expr), GL L e →
      listLit? natLit? fuel e = ExceptT.mk (some (.ok (α, xs))) → GL L α ∧ ∀ x ∈ xs, GL L x :=
  fun fuel L e α xs hG h => listLit?_good_aux hi1 natLit? fuel L e α xs hG h

end Tools.PassPh
