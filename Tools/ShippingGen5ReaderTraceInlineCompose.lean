import Tools.ShippingGen5ReaderTraceInlineP1
import Tools.ShippingGen5ReaderTraceAbbrevS1
import Tools.ShippingGen5ReaderTraceDirect2
-- Built in Pod (kjob lake build Tools.ShippingGen5ReaderTraceInlineCompose, exit 0) on the tree of 2a6af8f053b88b44dbe1681b0dbaa93ec9e7b1b9 (Lean content identical; this header is comment-only). Clean build is the coder's. No sorry / axiom / native_decide in source. Written against `scripts/gen5/RT_INLINE_COMPOSE_FREEZE.md`. Hypotheses only: DeclValuePh, RecRulePh, PassPh (S2 leaf), ReplaceAgrees, HeadBetaAgrees0.
-- NOT BUILT. EXPLORATION SKELETON (contains sorry; not counted toward acceptance or the ledger). Written against `scripts/gen5/RT_INLINE_COMPOSE_FREEZE.md`.

namespace Tools.ShippingGen5ReaderTrace
open Lean Sparkle.Compiler.Elab Tools.ShippingLetsReaderInv Tools.ShippingReaderFuel Tools.Assume.AbbrevExtern Tools.ShippingGen5ReaderTraceAbbrevS1
open Sparkle.Compiler.MachTupleIn Tools.ShippingGen5ReaderTracePack Tools.ShippingReaderFuelShapeR5

/-- (hypothesis only; supplied by `sparkle-rt-recrule`) recursor rules of `env` are closed `NoPh` terms -/
def RecRulePh (env : Lean.Environment) : Prop :=
  ∀ (n : Lean.Name) (rv : Lean.RecursorVal), env.find? n = some (.recInfo rv) →
    ∀ r ∈ rv.rules, NoPh r.rhs = true ∧ BvarLt 0 r.rhs = true

/-- (hypothesis only; leaf S2 `pass_ph`, `sparkle-rt-pass-total`) `MachRecUnfold.pass` preserves `NoPh ∧ BvarLt 0` -/
def PassPh (env : Lean.Environment) : Prop :=
  Tools.Assume.EnvDeclValue.DeclValuePh env → RecRulePh env →
    ∀ (isUser : Lean.Name → Bool) (e : Lean.Expr), NoPh e = true → BvarLt 0 e = true →
      NoPh (Sparkle.Compiler.MachRecUnfold.pass env canonicalNatLitValue? isUser e) = true ∧
        BvarLt 0 (Sparkle.Compiler.MachRecUnfold.pass env canonicalNatLitValue? isUser e) = true

theorem inl_step_ph (env : Lean.Environment) (hv : Tools.Assume.EnvDeclValue.DeclValuePh env)
    (e : Lean.Expr) (hn : NoPh e = true) (hb : BvarLt 0 e = true) :
    NoPh (match inlineDefs (userDefinition? env) (userProjection? env) inlineDepth e inlineBudget with
      | some (e', _) => e'
      | none => e) = true ∧
    BvarLt 0 (match inlineDefs (userDefinition? env) (userProjection? env) inlineDepth e inlineBudget with
      | some (e', _) => e'
      | none => e) = true :=
  inlineDefs_user_ph env hv 0 e hn hb

theorem rounds_ph (env : Lean.Environment) (hv : Tools.Assume.EnvDeclValue.DeclValuePh env)
    (hrr : RecRulePh env) (hp : PassPh env) (inl : Lean.Expr → Lean.Expr) (isRec : Lean.Name → Bool)
    (hinl : ∀ e : Lean.Expr, NoPh e = true → BvarLt 0 e = true → NoPh (inl e) = true ∧ BvarLt 0 (inl e) = true) :
    ∀ (k : Nat) (e : Lean.Expr), NoPh e = true → BvarLt 0 e = true →
      NoPh (userInliner.rounds env inl isRec k e) = true ∧ BvarLt 0 (userInliner.rounds env inl isRec k e) = true := by
  intro k
  induction k with
  | zero => intro e hn hb; exact ⟨hn, hb⟩
  | succ k ih =>
    intro e hn hb
    simp only [userInliner.rounds]
    have hpe := hp hv hrr isRec e hn hb
    split
    · exact ⟨hn, hb⟩
    · have h2 := hinl _ hpe.1 hpe.2
      exact ih _ h2.1 h2.2

theorem abbrev_fold_ph (env : Lean.Environment) (hv : Tools.Assume.EnvDeclValue.DeclValuePh env)
    (hr : ReplaceAgrees) (hb : HeadBetaAgrees0) (x : Lean.Expr) (hn : NoPh x = true) (hbl : BvarLt 0 x = true) :
    NoPh (inlFoldNat (inlAbbrevs env 4 x)) = true ∧ BvarLt 0 (inlFoldNat (inlAbbrevs env 4 x)) = true := by
  have h3 := inlAbbrevs_ph env hv hr hb 4 x hn hbl
  exact inlFoldNat_ph (L := 0) _ h3.1 h3.2

theorem userInliner_ph (env : Lean.Environment) (hv : Tools.Assume.EnvDeclValue.DeclValuePh env)
    (hrr : RecRulePh env) (hp : PassPh env) (hr : ReplaceAgrees) (hb : HeadBetaAgrees0)
    (e : Lean.Expr) (hn : NoPh e = true) (hbl : BvarLt 0 e = true) :
    NoPh (userInliner env e) = true ∧ BvarLt 0 (userInliner env e) = true := by
  have h1 := inl_step_ph env hv e hn hbl
  unfold userInliner
  simp only []
  split
  · refine abbrev_fold_ph env hv hr hb _ ?_ ?_
    · exact (rounds_ph env hv hrr hp _ _ (fun x hx hy => inl_step_ph env hv x hx hy) 64 _ h1.1 h1.2).1
    · exact (rounds_ph env hv hrr hp _ _ (fun x hx hy => inl_step_ph env hv x hx hy) 64 _ h1.1 h1.2).2
  · exact abbrev_fold_ph env hv hr hb _ h1.1 h1.2

theorem inlinedConst_defn_ph (env : Lean.Environment) (hv : Tools.Assume.EnvDeclValue.DeclValuePh env)
    (hrr : RecRulePh env) (hp : PassPh env) (hr : ReplaceAgrees) (hb : HeadBetaAgrees0)
    (c : Lean.Name) (ci0 : Lean.ConstantInfo) (hc : env.find? c = some ci0) (d : Lean.DefinitionVal)
    (hd : inlinedConst (userInliner env) ci0 = .defnInfo d) :
    NoPh d.value = true ∧ BvarLt 0 d.value = true := by
  cases ci0 with
  | defnInfo d0 =>
    simp only [inlinedConst, ConstantInfo.defnInfo.injEq] at hd
    subst hd
    have h0 := hv c d0 hc
    exact userInliner_ph env hv hrr hp hr hb _ h0.1 h0.2
  | _ => simp only [inlinedConst] at hd <;> cases hd

theorem shapeInputs_of_decl'
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

theorem shapeInputs_of_inline'
    (hz : Tools.Assume.N3Extern.ZeroLitAgrees0) (hla : LiftAgrees) (hi1 : Inst1Agrees)
    (env : Lean.Environment) (hv : Tools.Assume.EnvDeclValue.DeclValuePh env)
    (hrr : RecRulePh env) (hp : PassPh env) (hr : ReplaceAgrees) (hb : HeadBetaAgrees0)
    {c : Lean.Name} {ci0 : Lean.ConstantInfo} (hc : env.find? c = some ci0)
    {ci : Lean.ConstantInfo} (hci : ci = inlinedConst (userInliner env) ci0)
    (hbr : Tools.Assume.PackTupleBridge.PackTupleInputsBridge)
    (hraw : Tools.Assume.NormNodePh.RawNodePh (structEnv env))
    (hnode : Tools.Assume.NormNodePh.NormNodePh (structEnv env))
    {sm : Bool} {ps : List (String × Nat)} {n : Nat} :
    ShapeInputs' (nDeclOfCi ci) (structEnv env) sm ps ci n := by
  refine shapeInputs_of_decl' hz hla hi1 env ?_ hbr hraw hnode
  intro d hd
  rw [hci] at hd
  exact inlinedConst_defn_ph env hv hrr hp hr hb c ci0 hc d hd

theorem shapeInputs_of_entryConst'
    (hz : Tools.Assume.N3Extern.ZeroLitAgrees0) (hla : LiftAgrees) (hi1 : Inst1Agrees)
    (env : Lean.Environment) (hv : Tools.Assume.EnvDeclValue.DeclValuePh env)
    (hrr : RecRulePh env) (hp : PassPh env) (hr : ReplaceAgrees) (hb : HeadBetaAgrees0)
    {c : Lean.Name} {ci0 : Lean.ConstantInfo} (hc : env.find? c = some ci0)
    (certifiedFrontEnd symbolicMode : Bool) (parameters : List (String × Nat)) (isInst : Lean.Expr → Bool)
    (projs : StructEnv)
    (hbr : Tools.Assume.PackTupleBridge.PackTupleInputsBridge)
    (hraw : Tools.Assume.NormNodePh.RawNodePh (structEnv env))
    (hnode : Tools.Assume.NormNodePh.NormNodePh (structEnv env))
    {sm : Bool} {ps : List (String × Nat)} {n : Nat} :
    ShapeInputs' (nDeclOfCi (entryConst certifiedFrontEnd symbolicMode parameters ci0 isInst (userInliner env) projs))
      (structEnv env) sm ps (entryConst certifiedFrontEnd symbolicMode parameters ci0 isInst (userInliner env) projs) n := by
  refine shapeInputs_of_decl' hz hla hi1 env ?_ hbr hraw hnode
  intro d hd
  unfold entryConst at hd
  split at hd
  · split at hd
    · exact inlinedConst_defn_ph env hv hrr hp hr hb c ci0 hc d hd
    · exact hv c d (by rw [hc, hd])
  · exact hv c d (by rw [hc, hd])

end Tools.ShippingGen5ReaderTrace
