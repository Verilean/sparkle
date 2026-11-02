import Tools.ShippingGen5ReaderTraceInlineP1
import Tools.ShippingGen5ReaderTraceAbbrevS1
import Tools.ShippingGen5ReaderTraceDirect2
import Tools.PassPh.Pass
-- NOT BUILT (rt126): content of InlineCompose2 (rt124, built ok at 73f53745) moved to this module name so downstream imports are unchanged; `PassPh` hypothesis replaced by `pass_ph` (Tools/PassPh/Pass.lean). Old-name aliases at the end. No sorry / axiom / native_decide. Hypotheses only: DeclValuePh, RecRulePhU (Tools.PassPh), ReplaceAgrees, Inst1Agrees, HeadBetaAgreesL, BetaNonTargetAgrees, ExprEqvLaws. Clean build is the coder's.

namespace Tools.ShippingGen5ReaderTrace
open Lean Sparkle.Compiler.Elab Tools.ShippingLetsReaderInv Tools.ShippingReaderFuel Tools.Assume.AbbrevExtern Tools.ShippingGen5ReaderTraceAbbrevS1
open Sparkle.Compiler.MachTupleIn Tools.ShippingGen5ReaderTracePack Tools.ShippingReaderFuelShapeR5
open Tools.PassPh

theorem inl_step_ph_pp (env : Lean.Environment) (hv : Tools.Assume.EnvDeclValue.DeclValuePh env)
    (e : Lean.Expr) (hn : NoPh e = true) (hb : BvarLt 0 e = true) :
    NoPh (userInlStep env e) = true ∧ BvarLt 0 (userInlStep env e) = true :=
  inlineDefs_user_ph env hv 0 e hn hb

theorem rounds_ph_pp (env : Lean.Environment) (hv : Tools.Assume.EnvDeclValue.DeclValuePh env)
    (hrr : RecRulePhU env) (hrep : ReplaceAgrees) (hi1 : Inst1Agrees) (hh : HeadBetaAgreesL)
    (hbt : BetaNonTargetAgrees) (hEq : Tools.Assume.ExprEqvGL.ExprEqvLaws) (fuel : Nat) :
    ∀ (k : Nat) (e r : Lean.Expr), NoPh e = true → BvarLt 0 e = true →
      userInlinerEWith.rounds fuel env k e = .ok r → NoPh r = true ∧ BvarLt 0 r = true := by
  intro k
  induction k with
  | zero =>
    intro e r hn hb h
    simp only [userInlinerEWith.rounds] at h
    cases h; exact ⟨hn, hb⟩
  | succ k ih =>
    intro e r hn hb h
    simp only [userInlinerEWith.rounds, bind, Except.bind] at h
    cases hp : Sparkle.Compiler.MachRecUnfold.passWith fuel env canonicalNatLitValue? (userRecHelper env) e with
    | error m => rw [hp] at h; cases h
    | ok e' =>
      rw [hp] at h
      have hpe := passWith_ph canonicalNatLitValue? env hv hrr hrep hi1 hh hbt hEq fuel (userRecHelper env) e e' hn hb hp
      simp only [] at h
      split at h
      · cases h; exact ⟨hn, hb⟩
      · have h2 := inl_step_ph_pp env hv e' hpe.1 hpe.2
        exact ih _ r h2.1 h2.2 h

theorem abbrev_fold_ph_pp (env : Lean.Environment) (hv : Tools.Assume.EnvDeclValue.DeclValuePh env)
    (hr : ReplaceAgrees) (hb : HeadBetaAgrees0) (x : Lean.Expr) (hn : NoPh x = true) (hbl : BvarLt 0 x = true) :
    NoPh (inlFoldNat (inlAbbrevs env 4 x)) = true ∧ BvarLt 0 (inlFoldNat (inlAbbrevs env 4 x)) = true := by
  have h3 := inlAbbrevs_ph env hv hr hb 4 x hn hbl
  exact inlFoldNat_ph (L := 0) _ h3.1 h3.2


theorem userInliner_ph_pp (env : Lean.Environment) (hv : Tools.Assume.EnvDeclValue.DeclValuePh env)
    (hrr : RecRulePhU env) (hrep : ReplaceAgrees) (hh : HeadBetaAgreesL)
    (hbt : BetaNonTargetAgrees) (hEq : Tools.Assume.ExprEqvGL.ExprEqvLaws) (hi1 : Inst1Agrees)
    (e : Lean.Expr) (hn : NoPh e = true) (hbl : BvarLt 0 e = true) :
    NoPh (userInliner env e) = true ∧ BvarLt 0 (userInliner env e) = true := by
  have h1 := inl_step_ph_pp env hv e hn hbl
  have hb0 : HeadBetaAgrees0 := headBetaAgreesL_zero hh
  unfold userInliner userInlinerE userInlinerEWith
  simp only []
  split
  · rename_i r hr
    split at hr
    · simp only [bind, Except.bind] at hr
      cases hq : userInlinerEWith.rounds Sparkle.Compiler.MachRecUnfold.passLimit env 64 (userInlStep env e) with
      | error m => rw [hq] at hr; cases hr
      | ok e2 =>
        rw [hq] at hr
        cases hr
        have h2 := rounds_ph_pp env hv hrr hrep hi1 hh hbt hEq _ 64 _ _ h1.1 h1.2 hq
        exact abbrev_fold_ph_pp env hv hrep hb0 _ h2.1 h2.2
    · cases hr
      exact abbrev_fold_ph_pp env hv hrep hb0 _ h1.1 h1.2
  · exact abbrev_fold_ph_pp env hv hrep hb0 _ h1.1 h1.2

theorem inlinedConst_defn_ph_pp (env : Lean.Environment) (hv : Tools.Assume.EnvDeclValue.DeclValuePh env)
    (hrr : RecRulePhU env) (hrep : ReplaceAgrees) (hh : HeadBetaAgreesL)
    (hbt : BetaNonTargetAgrees) (hEq : Tools.Assume.ExprEqvGL.ExprEqvLaws) (hi1 : Inst1Agrees)
    (c : Lean.Name) (ci0 : Lean.ConstantInfo) (hc : env.find? c = some ci0) (d : Lean.DefinitionVal)
    (hd : inlinedConst (userInliner env) ci0 = .defnInfo d) :
    NoPh d.value = true ∧ BvarLt 0 d.value = true := by
  cases ci0 with
  | defnInfo d0 =>
    simp only [inlinedConst, ConstantInfo.defnInfo.injEq] at hd
    subst hd
    have h0 := hv c d0 hc
    exact userInliner_ph_pp env hv hrr hrep hh hbt hEq hi1 _ h0.1 h0.2
  | _ => simp only [inlinedConst] at hd <;> cases hd

theorem shapeInputs_of_decl_pp
    (hz : Tools.Assume.N3Extern.ZeroLitAgrees0) (hla : LiftAgrees) (hi1 : Inst1Agrees)
    (env : Lean.Environment) {ci : Lean.ConstantInfo}
    (hdecl : ∀ d, ci = ConstantInfo.defnInfo d → NoPh d.value = true ∧ BvarLt 0 d.value = true)
    (hbr : Tools.Assume.PackTupleBridge.PackTupleInputsBridge)
    (hraw : Tools.Assume.NormNodePh.RawNodePh (structEnv env))
    (hnode : Tools.Assume.NormNodePh.NormNodePh (structEnv env))
    {sm : Bool} {ps : List (String × Nat)} {n : Nat} :
    ShapeInputs' (nDeclOfCi ci) (structEnv env) sm ps ci n := by
  have hrf : RootFloatAgrees := Tools.PartialTotal.Agree.rootFloatAgrees hla
  intro p en hp hen
  obtain ⟨hci', hpeel, -⟩ := shapePre_facts hp
  have hd := hdecl p.d hci'
  have h1 : NoPh (Sparkle.Compiler.MachTupleIn.packTupleInputs p.d.value) = true ∧
      BvarLt 0 (Sparkle.Compiler.MachTupleIn.packTupleInputs p.d.value) = true := by
    rw [hbr _ hd.1 hd.2]
    exact packTupleInputsF_ph hla hi1 _ 0 _ hd.1 hd.2
  have h2 := mixedGatePeel_ph (L := 0) _ p.bs p.e hpeel h1.1 h1.2
  rw [Nat.zero_add] at h2
  have h3 := machNormF_ph hi1 (structEnv env) hraw hnode n p.bs.length p.e en h2.1 h2.2 hen
  have hm := shapeMid_ph hz hrf (structEnv env) p h3.1 h3.2
  have hle := hbs_of_nDeclOfCi sm ps ci (structEnv env) p hp
  refine ⟨hle, ?_, ?_, ?_⟩
  · intro k x hx
    have := hm.1 k x hx
    exact ⟨this.1, bvarLt_mono (by omega) this.2⟩
  · intro dom αs ie b hr
    have := hm.2.1 dom αs ie b hr
    exact ⟨this.1, bvarLt_mono (by omega) this.2.1, this.2.2.1, bvarLt_mono (by omega) this.2.2.2⟩
  · intro hr
    have := hm.2.2 hr
    exact ⟨this.1, bvarLt_mono (by omega) this.2⟩

theorem shapeInputs_of_inline_pp
    (hz : Tools.Assume.N3Extern.ZeroLitAgrees0) (hla : LiftAgrees) (hi1 : Inst1Agrees)
    (env : Lean.Environment) (hv : Tools.Assume.EnvDeclValue.DeclValuePh env)
    (hrr : RecRulePhU env) (hrep : ReplaceAgrees) (hh : HeadBetaAgreesL)
    (hbt : BetaNonTargetAgrees) (hEq : Tools.Assume.ExprEqvGL.ExprEqvLaws)
    {c : Lean.Name} {ci0 : Lean.ConstantInfo} (hc : env.find? c = some ci0)
    {ci : Lean.ConstantInfo} (hci : ci = inlinedConst (userInliner env) ci0)
    (hbr : Tools.Assume.PackTupleBridge.PackTupleInputsBridge)
    (hraw : Tools.Assume.NormNodePh.RawNodePh (structEnv env))
    (hnode : Tools.Assume.NormNodePh.NormNodePh (structEnv env))
    {sm : Bool} {ps : List (String × Nat)} {n : Nat} :
    ShapeInputs' (nDeclOfCi ci) (structEnv env) sm ps ci n := by
  refine shapeInputs_of_decl_pp hz hla hi1 env ?_ hbr hraw hnode
  intro d hd
  rw [hci] at hd
  exact inlinedConst_defn_ph_pp env hv hrr hrep hh hbt hEq hi1 c ci0 hc d hd

theorem shapeInputs_of_entryConst_pp
    (hz : Tools.Assume.N3Extern.ZeroLitAgrees0) (hla : LiftAgrees) (hi1 : Inst1Agrees)
    (env : Lean.Environment) (hv : Tools.Assume.EnvDeclValue.DeclValuePh env)
    (hrr : RecRulePhU env) (hrep : ReplaceAgrees) (hh : HeadBetaAgreesL)
    (hbt : BetaNonTargetAgrees) (hEq : Tools.Assume.ExprEqvGL.ExprEqvLaws)
    {c : Lean.Name} {ci0 : Lean.ConstantInfo} (hc : env.find? c = some ci0)
    (certifiedFrontEnd symbolicMode : Bool) (parameters : List (String × Nat)) (isInst : Lean.Expr → Bool)
    (projs : StructEnv)
    (hbr : Tools.Assume.PackTupleBridge.PackTupleInputsBridge)
    (hraw : Tools.Assume.NormNodePh.RawNodePh (structEnv env))
    (hnode : Tools.Assume.NormNodePh.NormNodePh (structEnv env))
    {sm : Bool} {ps : List (String × Nat)} {n : Nat} :
    ShapeInputs' (nDeclOfCi (entryConst certifiedFrontEnd symbolicMode parameters ci0 isInst (userInliner env) projs))
      (structEnv env) sm ps (entryConst certifiedFrontEnd symbolicMode parameters ci0 isInst (userInliner env) projs) n := by
  refine shapeInputs_of_decl_pp hz hla hi1 env ?_ hbr hraw hnode
  intro d hd
  unfold entryConst at hd
  split at hd
  · split at hd
    · exact inlinedConst_defn_ph_pp env hv hrr hrep hh hbt hEq hi1 c ci0 hc d hd
    · exact hv c d (by rw [hc, hd])
  · exact hv c d (by rw [hc, hd])

/-! Aliases for the names of the pre-S2 file. Types are the NEW ones (`PassPh` hypothesis gone; `hb : HeadBetaAgrees0` replaced by `hh : HeadBetaAgreesL`, plus `hbt`, `hEq`). `PassPh` and the local `RecRulePhU` no longer exist here (`RecRulePhU` is `Tools.PassPh.RecRulePhU`). -/
abbrev inl_step_ph := @inl_step_ph_pp
abbrev rounds_ph := @rounds_ph_pp
abbrev abbrev_fold_ph := @abbrev_fold_ph_pp
abbrev userInliner_ph := @userInliner_ph_pp
abbrev inlinedConst_defn_ph := @inlinedConst_defn_ph_pp
abbrev shapeInputs_of_decl' := @shapeInputs_of_decl_pp
abbrev shapeInputs_of_inline' := @shapeInputs_of_inline_pp
abbrev shapeInputs_of_entryConst' := @shapeInputs_of_entryConst_pp

end Tools.ShippingGen5ReaderTrace
