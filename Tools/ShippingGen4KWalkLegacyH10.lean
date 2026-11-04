import Tools.ShippingGen4KWalkLegacyH9
-- NOT BUILT (rt175 WIP). LegacyImplK part 10: `toIR` (induction on a size bound), `getPrimitiveNameFromLambda`, and the legacy translator's main body `Rec.translateExprToWireImpl` as `legacyImplKcore` / `legacyImplK'` (the child entry `hchild` as a hypothesis).
-- Takes `MemoFamily` (TRUSTED, approved) and `MsgMvK` as HYPOTHESES; adds NO premise, NO law, NO axiom. No `sorry`, no `native_decide`. Ledger delta: FG -0 +0 / T1 -0 +0.
namespace Tools.ShippingGen4KWalkLegacyH10
open Lean Meta
open Tools.ShippingEntrySoundness
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv
open Tools.ShippingChildBndInit
open Tools.ShippingChildBndCore
open Tools.ShippingChildInvA
open Tools.ShippingChildFresh
open Tools.ShippingChildVCA
open Tools.ShippingChildPathA
open Tools.ShippingChildTranslateA
open Tools.ShippingGen4KWalkTac2
open Tools.ShippingChildWalkA
open Tools.Assume.MemoFamily
open Tools.ShippingGen4KWalk
open Tools.ShippingGen4KWalkPrims
open Tools.ShippingGen4KWalkHelpers
open Tools.ShippingChildLegacyHelpersA
open Tools.ShippingGen4KWalkLegacyH1
open Tools.ShippingGen4KWalkLegacyH2
open Tools.ShippingGen4KWalkEmit
open Tools.ShippingGen4KWalkLegacyRules
open Tools.ShippingGen4KWalkLegacyH4
open Tools.ShippingGen4KWalkCanon
open Tools.ShippingGen4KWalkLegacyH7
open Tools.ShippingGen4KWalkLegacyH1
open Tools.ShippingGen4KWalkLegacyH2
open Tools.ShippingGen4KWalkProjField
open Tools.ShippingGen4KWalkDiag
open Tools.ShippingGen4KWalkLegacyH8a
open Tools.ShippingGen4KWalkLegacyH8
open Tools.ShippingGen4KWalkLegacyH3
open Tools.ShippingGen4KWalkLegacyH5
open Tools.ShippingGen4KWalkLegacyH6
open Tools.ShippingGen4KWalkLegacyH9
open Tools.ShippingGen4KWalkLegacyH7
open Tools.ShippingGen4KWalkTranslate

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

section H10
variable {O : RefLawsAOps MkRefd mref cref} (M : MemoFamily O) (hpp : PpMvK O) {I : Void IO.RealWorld → Prop}
  (hS : StableK O.quiet I) (hmsg : MsgMvK O)
include M hpp hS hmsg

theorem getPrimK (hA : AdmCtx O.quiet mctx cctx) (e : Lean.Expr) :
    KeepsCP mctx mref cctx cref I (Rec.getPrimitiveNameFromLambda e) := by
  induction e with
  | lam _ _ body _ _ ih => unfold Rec.getPrimitiveNameFromLambda; exact ih
  | _ => unfold Rec.getPrimitiveNameFromLambda; kwAll3

theorem toIRK_bound (wireS : String) (fvarId : FVarId) :
    ∀ (n : Nat) (e : Lean.Expr), sizeOf e < n →
      ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx →
        KeepsCP mctx mref cctx cref I (Rec.translateExprToWireImpl.toIR wireS fvarId e)
  | 0, _, h => by omega
  | n + 1, e, h => by
    intro mctx cctx hA
    have ih := fun e' (h' : sizeOf e' < n) (mctx : Meta.Context) (cctx : Core.Context)
      (hA : AdmCtx O.quiet mctx cctx) => toIRK_bound wireS fvarId n e' h' mctx cctx hA
    unfold Rec.translateExprToWireImpl.toIR
    kwAll3

theorem toIRK (wireS : String) (fvarId : FVarId) (hA : AdmCtx O.quiet mctx cctx) (e : Lean.Expr) :
    KeepsCP mctx mref cctx cref I (Rec.translateExprToWireImpl.toIR wireS fvarId e) :=
  toIRK_bound M hpp hS hmsg wireS fvarId (sizeOf e + 1) e (Nat.lt_succ_self _) mctx cctx hA

end H10

section H10b
variable {O : RefLawsAOps MkRefd mref cref} (M : MemoFamily O) (hpp : PpMvK O) {I : Void IO.RealWorld → Prop}
  (hS : StableK O.quiet I) (hmsg : MsgMvK O) (tr : TranslateFn)
  (htr : ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx →
    ∀ e hint top named, KeepsCP mctx mref cctx cref I (tr e hint top named))
  (hchild : ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx →
    ∀ c, Keeps mctx mref cctx cref I (childSynthEntry c))

set_option hygiene false in
macro "kwMain" : tactic => `(tactic| kwalkN [translateExprToWireAppK M hpp hS hmsg tr htr hchild hA _ _ _, getPrimK M hpp hS hmsg hA _, toIRK M hpp hS hmsg hA _ _ _, handleErrorPatternsK M hpp hS hA _ _ _ _ _, handleCircuitMonadK M hpp hS tr htr hA _ _ _ _ _, handleTupleProjectionsK M hpp hS tr htr hA _ _ _ _ _, handleApplicativeK M hpp hS tr htr hA _ _ _ _ _, handleBitVecOpsK M hpp hS tr htr hA _ _ _ _ _, handleRegisterK M hpp hS tr htr hA _ _ _ _ _, handleMuxK M hpp hS tr htr hA _ _ _ _ _, handleMemoryK M hpp hS tr htr hA _ _ _ _ _, handleLoopK M hpp hS tr htr hA _ _ _ _ _, handleDefinitionUnfoldK M hpp hS hmsg tr htr hchild hA _ _ _ _ _, stderrPairCPk M hS hA _ _, keepsK_msgToStringR M hS hmsg hA _ _, keepsK_addMessageContext M hA hS _, keepsK_ppExpr M hpp hS _ _,
  keepsK_throwError M _ hS _ _, keepsK_getDecl M hpp hS _ _, Keeps.withReaderA (q := O.quiet) _ _,
  extractWidthK M hpp hS _ _, inferHWTypeK M hpp hS _ _, extractDimExprK M hpp hS _ _,
  inferHWTypeWithDimensionsK M hpp hS _ _, inferHWTypeFromSignalK M hpp hS _ _,
  isSignalBinderTypeK M hpp hS _ _, extractNatK M hpp hS _ _, getWireWidthK M hpp hS _ _,
  getWireWidthDimK M hpp hS _ _, cachedInferTypeK M hpp hS _ _, extractBitVecLiteralK M hpp hS _ _,
  extractNatLiteralK M hpp hS _ _, extractBitVecListK M hpp hS _ _, extractBitVecArrayK M hpp hS _ _,
  lowerZeroExtendWireK M hpp hS _ _ _ _ _,
  isTracingEnabledFor_keepsK M hpp hS _ _, addTrace_keepsK M hpp hS _ _ _,
  snapshotWireCaches_keepsK M hpp hS _, restoreWireCaches_keepsK M hpp hS _ _,
  makeWirePK M hA hS, addInputPK M hA hS, addOutputPK M hA hS, emitAssignP, bindSourceVariableP, lookupVarP,
  emitRegisterStmtA, emitRegisterK M hA hS, emitMemoryK M hA hS, freshNameA, emitInstanceA,
  canonHardwareKeyK M hA hS _, withLocalDeclPK M hS hA _ _ _, withLetDeclPK M hS hA _ _ _ _, M.tele.telescope I _ hS.1 hS.2 _ _,
  addModuleToDesignA, withVarMappingP, withDimVarMappingP, KeepsCP.tryCatch, KeepsCP.map _,
  keepsK_framedNM M hA hS (FramedNM.freshFVar (Fresh := MkRefd))])




include M hpp hS hmsg htr hchild

/-- **The legacy translator's main body keeps `I`**, given the child entry. -/
theorem legacyImplKcore (hA : AdmCtx O.quiet mctx cctx)
    (e : Lean.Expr) (hint : String) (top named : Bool) :
    KeepsCP mctx mref cctx cref I (Rec.translateExprToWireImpl tr e hint top named) := by
  unfold Rec.translateExprToWireImpl
  kwMain

end H10b

end Tools.ShippingGen4KWalkLegacyH10
