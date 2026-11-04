import Tools.ShippingGen4KWalkLegacyH8
import Tools.ShippingGen4KWalkLegacyH3
import Tools.ShippingGen4KWalkLegacyH5
import Tools.ShippingGen4KWalkLegacyH6
-- BUILT (normSpineK, translateExprToWireAppK): kjob lake build Tools.ShippingGen4KWalkLegacyH9 exit 0 (rt175, source as of this commit); clean build is the coder's. LegacyImplK part 9 (in progress): `normSpine` (induction on its fuel), the dispatcher `translateExprToWireApp` (all handlers as rules).
-- Takes `MemoFamily` (TRUSTED, approved) and `MsgMvK` as HYPOTHESES; adds NO premise, NO law, NO axiom. No `sorry`, no `native_decide`. Ledger delta: FG -0 +0 / T1 -0 +0.
namespace Tools.ShippingGen4KWalkLegacyH9
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

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

section H9a
variable {O : RefLawsAOps MkRefd mref cref} {I : Void IO.RealWorld → Prop}
end H9a

set_option hygiene false in
macro "kwAll3" : tactic => `(tactic| kwalkN [stderrPairCPk M hS hA _ _, keepsK_msgToStringR M hS hmsg hA _ _, keepsK_addMessageContext M hA hS _, keepsK_ppExpr M hpp hS _ _,
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



section H9
variable {O : RefLawsAOps MkRefd mref cref} (M : MemoFamily O) (hpp : PpMvK O) {I : Void IO.RealWorld → Prop}
  (hS : StableK O.quiet I) (hmsg : MsgMvK O)

include M hpp hS hmsg
theorem normSpineK :
    ∀ (fuel : Nat) (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx →
      ∀ (x : Lean.Expr), Keeps mctx mref cctx cref I (Rec.translateExprToWireApp.normSpine x fuel)
  | 0, mctx, cctx, hA, x => by
    unfold Rec.translateExprToWireApp.normSpine
    kwAll3
  | fuel + 1, mctx, cctx, hA, x => by
    have ih := fun mctx cctx (hA : AdmCtx O.quiet mctx cctx) x => normSpineK fuel mctx cctx hA x
    unfold Rec.translateExprToWireApp.normSpine
    kwAll3

end H9


section H9b
variable {O : RefLawsAOps MkRefd mref cref} (M : MemoFamily O) (hpp : PpMvK O) {I : Void IO.RealWorld → Prop}
  (hS : StableK O.quiet I) (hmsg : MsgMvK O) (tr : TranslateFn)
  (htr : ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx →
    ∀ e hint top named, KeepsCP mctx mref cctx cref I (tr e hint top named))
  (hchild : ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx →
    ∀ c, Keeps mctx mref cctx cref I (childSynthEntry c))

set_option hygiene false in
macro "kwApp" : tactic => `(tactic| kwalkN [handleErrorPatternsK M hpp hS hA _ _ _ _ _, handleCircuitMonadK M hpp hS tr htr hA _ _ _ _ _, handleTupleProjectionsK M hpp hS tr htr hA _ _ _ _ _, handleApplicativeK M hpp hS tr htr hA _ _ _ _ _, handleBitVecOpsK M hpp hS tr htr hA _ _ _ _ _, handleRegisterK M hpp hS tr htr hA _ _ _ _ _, handleMuxK M hpp hS tr htr hA _ _ _ _ _, handleMemoryK M hpp hS tr htr hA _ _ _ _ _, handleLoopK M hpp hS tr htr hA _ _ _ _ _, handleDefinitionUnfoldK M hpp hS hmsg tr htr hchild hA _ _ _ _ _, stderrPairCPk M hS hA _ _, keepsK_msgToStringR M hS hmsg hA _ _, keepsK_addMessageContext M hA hS _, keepsK_ppExpr M hpp hS _ _,
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

/-- **The dispatcher** `Rec.translateExprToWireApp`: the nine handlers in order, after the `Signal` pre-filters and `normSpine`. -/
theorem translateExprToWireAppK (hA : AdmCtx O.quiet mctx cctx)
    (e : Lean.Expr) (hint : String) (named : Bool) :
    KeepsCP mctx mref cctx cref I (Rec.translateExprToWireApp tr e hint named) := by
  have hns := normSpineK M hpp hS hmsg 32 mctx cctx hA
  unfold Rec.translateExprToWireApp
  kwApp

end H9b

end Tools.ShippingGen4KWalkLegacyH9
