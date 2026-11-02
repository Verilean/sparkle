import Tools.PassPh.Beta
import Tools.PassPh.Rec
import Tools.ShippingGen5ReaderTraceReg
set_option autoImplicit false
-- SKELETON (rev2 L version): not built yet. Types follow scripts/gen5/RT_PASS_PH_FREEZE.md rev2.

/-! # pass_ph skeleton: Iota group (iota_good, reduceMatcher?_good, reduceHead_good). Depends on Beta + Rec. -/

namespace Tools.PassPh
open Lean Tools.ShippingLetsReaderInv Tools.ShippingGen5ReaderTrace Tools.Assume.AbbrevExtern Sparkle.Compiler.MachRecUnfold

private theorem M_pure_ok {α : Type} {a r : α} (h : (pure a : M α) = ExceptT.mk (some (.ok r))) : a = r := by
  have h' : (some (Except.ok a) : Option (Except String α)) = some (.ok r) := h
  exact Except.ok.inj (Option.some.inj h')

private theorem M_stuck_no {α : Type} {r : α} (h : (stuck : M α) = ExceptT.mk (some (.ok r))) : False := by
  have h' : (none : Option (Except String α)) = some (.ok r) := h
  cases h'

private theorem M_ofExcept_ok {α : Type} {x : Except String α} {r : α}
    (h : ofExcept x = ExceptT.mk (some (.ok r))) : x = .ok r := by
  have h' : (some x : Option (Except String α)) = some (.ok r) := h
  exact Option.some.inj h'

private theorem M_bind_ok {α β : Type} (x : M α) (f : α → M β) (r : β)
    (h : (x >>= f) = ExceptT.mk (some (.ok r))) :
    ∃ a, x = ExceptT.mk (some (.ok a)) ∧ f a = ExceptT.mk (some (.ok r)) := by
  have key : ∀ y : Option (Except String α), (ExceptT.mk y >>= f) = ExceptT.mk (some (.ok r)) →
      ∃ a, ExceptT.mk y = ExceptT.mk (some (.ok a)) ∧ f a = ExceptT.mk (some (.ok r)) := by
    intro y hy
    rcases y with _ | _ | a
    · have h' : (none : Option (Except String β)) = some (.ok r) := hy
      cases h'
    · have h' : (some (Except.error _) : Option (Except String β)) = some (.ok r) := hy
      cases h'
    · exact ⟨a, rfl, hy⟩
  exact key x h

private theorem GL_args {L : Nat} {e : Lean.Expr} (h : GL L e) : ∀ a ∈ e.getAppArgs, GL L a :=
  fun a ha => getAppArgs_goodL L e h.1 h.2 a ha

private theorem GL_extract {L : Nat} {as : Array Lean.Expr} (h : ∀ a ∈ as, GL L a) (i j : Nat) : ∀ a ∈ as.extract i j, GL L a :=
  fun a ha => by
    obtain ⟨k, _, rfl⟩ := Array.mem_extract_iff_getElem.mp ha
    exact h _ (Array.getElem_mem _)

private theorem ilp_GL (hrep : ReplaceAgrees) (ps : List Lean.Name) (ls : List Lean.Level) (e : Lean.Expr) (L : Nat)
    (he : G e) : GL L (e.instantiateLevelParams ps ls) := GL_mono (Nat.zero_le L) (ilp_ph hrep ps ls e he)

open Lean Tools.ShippingLetsReaderInv Tools.ShippingGen5ReaderTrace Tools.Assume.AbbrevExtern Sparkle.Compiler.MachRecUnfold

private theorem M_lift_ok {α : Type} {x : Option α} {a : α}
    (h : (ExceptT.lift x : M α) = ExceptT.mk (some (.ok a))) : x = some a := by
  have h' : (Except.ok <$> x : Option (Except String α)) = some (.ok a) := h
  rcases x with _ | b
  · cases h'
  · have := Except.ok.inj (Option.some.inj h')
    rw [this]

theorem iota_goodL (env : Lean.Environment) (natLit? : Lean.Expr → Option Nat)
    (hd : Tools.Assume.EnvDeclValue.DeclValuePh env) (hr : RecRulePhU env)
    (hrep : ReplaceAgrees) (hh : HeadBetaAgreesL) (hbt : BetaNonTargetAgrees) :
    ∀ (fuel L : Nat) (e r : Lean.Expr), GL L e → iota env natLit? fuel e = ExceptT.mk (some (.ok r)) → GL L r := by
  intro fuel
  induction fuel with
  | zero => intro L e r _ h; exact (M_stuck_no h).elim
  | succ fuel ih =>
    intro L e r he h
    unfold iota at h
    obtain ⟨e1, h1, h⟩ := M_bind_ok _ _ _ h
    have hg : GL L e1 := headBetaM_goodL hh hbt _ L e e1 he (M_ofExcept_ok h1)
    have hargs := GL_args hg
    have hpure : (pure e1 : M Lean.Expr) = ExceptT.mk (some (.ok r)) → GL L r := fun hx => (M_pure_ok hx) ▸ hg
    split at h
    · rename_i n ls hfn
      split at h
      · rename_i _ pfx s
        split at h
        · rename_i hsp
          split at h
          · rename_i d hdf
            exact ih L _ _ (mkAppN_goodL L _ _ (ilp_GL hrep _ _ _ L (hd (pfx.str s) d hdf)) hargs) h
          · exact hpure h
        · split at h
          · rename_i hsr
            split at h
            · rename_i rv hrv
              try dsimp only at h
              split at h
              · exact (M_stuck_no h).elim
              · rename_i hsz
                obtain ⟨⟨cv, fields⟩, hc, h⟩ := M_bind_ok _ _ _ h
                have hc' := M_lift_ok hc
                try dsimp only at h
                split at h
                · rename_i rule hrule
                  try dsimp only at h
                  have hsr' : s = "rec" := by simpa using hsr
                  subst hsr'
                  have hfields := ctorApp_goodL L env natLit? _ cv fields (getBang_goodL hargs _) hc'
                  exact ih L _ _ (rec_arm_goodUL hrep env hr pfx rv hrv cv.name rule hrule L ls _ _ _
                    (GL_extract hargs _ _) hfields (GL_extract hargs _ _)) h
                · exact (M_stuck_no h).elim
            · exact hpure h
          · split at h
            · rename_i hsc
              repeat' (first | split at h | (dsimp only at h; split at h))
              all_goals first
                | exact hpure h
                | exact (M_stuck_no h).elim
                | (obtain ⟨⟨cv, fields⟩, hc, h⟩ := M_bind_ok _ _ _ h
                   have hc' := M_lift_ok hc
                   try dsimp only at h
                   have hfields := ctorApp_goodL L env natLit? _ cv fields (getBang_goodL hargs _) hc'
                   exact ih L _ _ (mkAppN_goodL L _ _ (mkAppN_goodL L _ _ (getBang_goodL hargs _) hfields)
                     (GL_extract hargs _ _)) h)
            · exact hpure h
      · exact hpure h
    · exact hpure h


theorem reduceMatcher?_goodL (env : Lean.Environment) (natLit? : Lean.Expr → Option Nat)
    (hd : Tools.Assume.EnvDeclValue.DeclValuePh env) (hr : RecRulePhU env)
    (hrep : ReplaceAgrees) (hh : HeadBetaAgreesL) (hbt : BetaNonTargetAgrees) :
    ∀ (L : Nat) (e r : Lean.Expr), GL L e → reduceMatcher? env natLit? e = ExceptT.mk (some (.ok r)) → GL L r := by
  intro L e r he h
  unfold reduceMatcher? at h
  split at h
  · rename_i n ls hfn
    split at h
    · exact (M_stuck_no h).elim
    · split at h
      · rename_i d hdf
        obtain ⟨r1, h1, h⟩ := M_bind_ok _ _ _ h
        have hg1 : GL L r1 := iota_goodL env natLit? hd hr hrep hh hbt 256 L _ r1
          (mkAppN_goodL L _ _ (ilp_GL hrep _ _ _ L (hd n d hdf)) (GL_args he)) h1
        try dsimp only at h
        split at h
        · split at h
          · exact (M_stuck_no h).elim
          · exact (M_pure_ok h) ▸ hg1
        · exact (M_pure_ok h) ▸ hg1
      · exact (M_stuck_no h).elim
  · exact (M_stuck_no h).elim

theorem reduceHead_goodL (env : Lean.Environment) (natLit? : Lean.Expr → Option Nat)
    (hd : Tools.Assume.EnvDeclValue.DeclValuePh env) (hr : RecRulePhU env)
    (hrep : ReplaceAgrees) (hh : HeadBetaAgreesL) (hbt : BetaNonTargetAgrees) :
    ∀ (fuel L : Nat) (e r : Lean.Expr), GL L e → reduceHead env natLit? fuel e = ExceptT.mk (some (.ok r)) → GL L r := by
  intro fuel
  induction fuel with
  | zero => intro L e r _ h; exact (M_stuck_no h).elim
  | succ fuel ih =>
    intro L e r he h
    unfold reduceHead at h
    obtain ⟨e1, h1, h⟩ := M_bind_ok _ _ _ h
    have hg : GL L e1 := headBetaM_goodL hh hbt _ L e e1 he (M_ofExcept_ok h1)
    try dsimp only at h
    split at h
    · -- letE arm: the recursive call is on the body `b` (`GL (L+1)`), hence the `∀ L` induction hypothesis
      rename_i n t v b nd
      obtain ⟨b', hb', h⟩ := M_bind_ok _ _ _ h
      have hb1 : GL (L + 1) b := by
        simp only [GL, NoPh, BvarLt, Bool.and_eq_true] at hg ⊢
        exact ⟨hg.1.2, hg.2.2⟩
      have hb2 := ih (L + 1) b b' hb1 hb'
      have := M_pure_ok h
      subst this
      simp only [GL, NoPh, BvarLt, Bool.and_eq_true] at hg hb2 ⊢
      exact ⟨⟨hg.1.1, hb2.1⟩, ⟨hg.2.1, hb2.2⟩⟩
    · split at h
      · obtain ⟨r1, h2, h⟩ := M_bind_ok _ _ _ h
        exact ih L _ _ (reduceMatcher?_goodL env natLit? hd hr hrep hh hbt L e1 r1 hg h2) h
      · exact (M_pure_ok h) ▸ hg

end Tools.PassPh
