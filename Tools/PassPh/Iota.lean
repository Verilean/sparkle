import Tools.PassPh.Beta
import Tools.PassPh.Rec
import Tools.ShippingGen5ReaderTraceReg
set_option autoImplicit false
-- SKELETON: sorry あり、探索ブランチのみ（受理の対象ではない）. Built in Pod (kjob lake build Tools.PassPh.Pass, exit 0) on the tree of dec1b348 (Lean content identical; header comment-only). Types follow scripts/gen5/RT_PASS_PH_FREEZE.md rev1 (approved as document/types only).

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

private theorem G_consume : ∀ e : Lean.Expr, G e → G e.consumeMData := by
  intro e
  induction e with
  | mdata m b ih =>
    intro h
    simp only [G, NoPh, BvarLt] at h
    exact ih h
  | _ => intro h; exact h

private theorem G_fn {e : Lean.Expr} (h : G e) : G e.getAppFn :=
  Tools.ShippingGen5ReaderTraceAbbrevS1.getAppFn_good e h.1 h.2

private theorem G_args {e : Lean.Expr} (h : G e) : ∀ a ∈ e.getAppArgs, G a :=
  fun a ha => Tools.ShippingGen5ReaderTrace.phArgs_getAppArgs h.1 h.2 a ha

private theorem G_extract {as : Array Lean.Expr} (h : ∀ a ∈ as, G a) (i j : Nat) : ∀ a ∈ as.extract i j, G a :=
  fun a ha => by
    obtain ⟨k, _, rfl⟩ := Array.mem_extract_iff_getElem.mp ha
    exact h _ (Array.getElem_mem _)

private theorem G_getBang {as : Array Lean.Expr} (h : ∀ a ∈ as, G a) (i : Nat) : G as[i]! :=
  Tools.ShippingGen5ReaderTraceAbbrevS1.getBang_good h i

open Lean Tools.ShippingLetsReaderInv Tools.ShippingGen5ReaderTrace Tools.Assume.AbbrevExtern Sparkle.Compiler.MachRecUnfold

private theorem M_lift_ok {α : Type} {x : Option α} {a : α}
    (h : (ExceptT.lift x : M α) = ExceptT.mk (some (.ok a))) : x = some a := by
  have h' : (Except.ok <$> x : Option (Except String α)) = some (.ok a) := h
  rcases x with _ | b
  · cases h'
  · have := Except.ok.inj (Option.some.inj h')
    rw [this]

theorem iota_good (env : Lean.Environment) (natLit? : Lean.Expr → Option Nat)
    (hd : Tools.Assume.EnvDeclValue.DeclValuePh env) (hr : RecRulePhU env)
    (hrep : ReplaceAgrees) (hh : HeadBetaAgrees0) (hbt : BetaNonTargetAgrees) :
    ∀ (fuel : Nat) (e r : Lean.Expr), G e → iota env natLit? fuel e = ExceptT.mk (some (.ok r)) → G r := by
  intro fuel
  induction fuel with
  | zero => intro e r _ h; exact (M_stuck_no h).elim
  | succ fuel ih =>
    intro e r he h
    unfold iota at h
    obtain ⟨e1, h1, h⟩ := M_bind_ok _ _ _ h
    have hg : G e1 := headBetaM_good hh hbt _ e e1 he (M_ofExcept_ok h1)
    have hargs := G_args hg
    have hpure : (pure e1 : M Lean.Expr) = ExceptT.mk (some (.ok r)) → G r := fun hx => (M_pure_ok hx) ▸ hg
    split at h
    · rename_i n ls hfn
      split at h
      · rename_i _ pfx s
        split at h
        · rename_i hsp
          split at h
          · rename_i d hdf
            exact ih _ _ (mkAppN_good _ _ (ilp_ph hrep _ _ _ (hd (pfx.str s) d hdf)) hargs) h
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
                  have hfields := ctorApp_good env natLit? _ cv fields (G_getBang hargs _) hc'
                  exact ih _ _ (rec_arm_goodU hrep env hr pfx rv hrv cv.name rule hrule ls _ _ _
                    (G_extract hargs _ _) hfields (G_extract hargs _ _)) h
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
                   have hfields := ctorApp_good env natLit? _ cv fields (G_getBang hargs _) hc'
                   exact ih _ _ (mkAppN_good _ _ (mkAppN_good _ _ (G_getBang hargs _) hfields)
                     (G_extract hargs _ _)) h)
            · exact hpure h
      · exact hpure h
    · exact hpure h


theorem reduceMatcher?_good (env : Lean.Environment) (natLit? : Lean.Expr → Option Nat)
    (hd : Tools.Assume.EnvDeclValue.DeclValuePh env) (hr : RecRulePhU env)
    (hrep : ReplaceAgrees) (hh : HeadBetaAgrees0) (hbt : BetaNonTargetAgrees) :
    ∀ (e r : Lean.Expr), G e → reduceMatcher? env natLit? e = ExceptT.mk (some (.ok r)) → G r := by
  intro e r he h
  unfold reduceMatcher? at h
  split at h
  · rename_i n ls hfn
    split at h
    · exact (M_stuck_no h).elim
    · split at h
      · rename_i d hdf
        obtain ⟨r1, h1, h⟩ := M_bind_ok _ _ _ h
        have hg1 : G r1 := iota_good env natLit? hd hr hrep hh hbt 256 _ r1
          (mkAppN_good _ _ (ilp_ph hrep _ _ _ (hd n d hdf)) (G_args he)) h1
        try dsimp only at h
        split at h
        · split at h
          · exact (M_stuck_no h).elim
          · exact (M_pure_ok h) ▸ hg1
        · exact (M_pure_ok h) ▸ hg1
      · exact (M_stuck_no h).elim
  · exact (M_stuck_no h).elim

theorem reduceHead_good (env : Lean.Environment) (natLit? : Lean.Expr → Option Nat)
    (hd : Tools.Assume.EnvDeclValue.DeclValuePh env) (hr : RecRulePhU env)
    (hrep : ReplaceAgrees) (hh : HeadBetaAgrees0) (hbt : BetaNonTargetAgrees) :
    ∀ (fuel : Nat) (e r : Lean.Expr), G e → reduceHead env natLit? fuel e = ExceptT.mk (some (.ok r)) → G r := by
  intro fuel
  induction fuel with
  | zero => intro e r _ h; exact (M_stuck_no h).elim
  | succ fuel ih =>
    intro e r he h
    unfold reduceHead at h
    obtain ⟨e1, h1, h⟩ := M_bind_ok _ _ _ h
    have hg : G e1 := headBetaM_good hh hbt _ e e1 he (M_ofExcept_ok h1)
    try dsimp only at h
    split at h
    · -- letE arm: the recursive call is on the body `b`, which is only `BvarLt 1`, not `G`;
      -- the statement (G only) gives no induction hypothesis for it.
      sorry
    · split at h
      · obtain ⟨r1, h2, h⟩ := M_bind_ok _ _ _ h
        exact ih _ _ (reduceMatcher?_good env natLit? hd hr hrep hh hbt e1 r1 hg h2) h
      · exact (M_pure_ok h) ▸ hg

end Tools.PassPh
