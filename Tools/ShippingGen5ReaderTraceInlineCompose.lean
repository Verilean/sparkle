import Tools.ShippingGen5ReaderTraceInlineP1
import Tools.ShippingGen5ReaderTraceAbbrevS1
import Tools.ShippingGen5ReaderTraceDirect2
set_option autoImplicit false
-- NOT BUILT. EXPLORATION SKELETON (contains sorry; not counted toward acceptance or the ledger). Written against `scripts/gen5/RT_INLINE_COMPOSE_FREEZE.md`.

namespace Tools.ShippingGen5ReaderTrace
open Lean Sparkle.Compiler.Elab Tools.ShippingLetsReaderInv Tools.ShippingReaderFuel Tools.Assume.AbbrevExtern Tools.ShippingGen5ReaderTraceAbbrevS1

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
  sorry

theorem userInliner_ph (env : Lean.Environment) (hv : Tools.Assume.EnvDeclValue.DeclValuePh env)
    (hrr : RecRulePh env) (hp : PassPh env) (hr : ReplaceAgrees) (hb : HeadBetaAgrees0)
    (e : Lean.Expr) (hn : NoPh e = true) (hbl : BvarLt 0 e = true) :
    NoPh (userInliner env e) = true ∧ BvarLt 0 (userInliner env e) = true := by
  sorry

theorem inlinedConst_defn_ph (env : Lean.Environment) (hv : Tools.Assume.EnvDeclValue.DeclValuePh env)
    (hrr : RecRulePh env) (hp : PassPh env) (hr : ReplaceAgrees) (hb : HeadBetaAgrees0)
    (c : Lean.Name) (ci0 : Lean.ConstantInfo) (hc : env.find? c = some ci0) (d : Lean.DefinitionVal)
    (hd : inlinedConst (userInliner env) ci0 = .defnInfo d) :
    NoPh d.value = true ∧ BvarLt 0 d.value = true := by
  sorry

theorem shapeInputs_of_decl'
    (hz : Tools.Assume.N3Extern.ZeroLitAgrees0) (hla : LiftAgrees) (hi1 : Inst1Agrees)
    (env : Lean.Environment) {ci : Lean.ConstantInfo}
    (hdecl : ∀ d, ci = ConstantInfo.defnInfo d → NoPh d.value = true ∧ BvarLt 0 d.value = true)
    (hbr : Tools.Assume.PackTupleBridge.PackTupleInputsBridge)
    (hraw : Tools.Assume.NormNodePh.RawNodePh (structEnv env))
    (hnode : Tools.Assume.NormNodePh.NormNodePh (structEnv env))
    {sm : Bool} {ps : List (String × Nat)} {n : Nat} :
    ShapeInputs' (nDeclOfCi ci) (structEnv env) sm ps ci n := by
  sorry

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
  sorry

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
  sorry

end Tools.ShippingGen5ReaderTrace
