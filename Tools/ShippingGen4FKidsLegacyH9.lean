import Tools.ShippingGen4FKidsTac
import Tools.ShippingGen4FKidsTele
import Tools.ShippingGen4FKidsCanon
import Tools.ShippingGen4KWalkLegacyH8
import Tools.ShippingGen4FKidsLegacyH8
import Tools.ShippingGen4KWalkLegacyH3
import Tools.ShippingGen4FKidsLegacyH3
import Tools.ShippingGen4KWalkLegacyH5
import Tools.ShippingGen4FKidsLegacyH5
import Tools.ShippingGen4KWalkLegacyH6
import Tools.ShippingGen4FKidsLegacyH6
-- BUILT (normSpineKS, translateExprToWireAppKS): kjob lake build Tools.ShippingGen4KWalkLegacyH9 exit 0 (rt175, source as of this commit); clean build is the coder's. LegacyImplKS part 9 (in progress): `normSpine` (induction on its fuel), the dispatcher `translateExprToWireApp` (all handlers as rules).
-- Takes `MemoFamily` (TRUSTED, approved) and `MsgMvK` as HYPOTHESES; adds NO premise, NO law, NO axiom. No `sorry`, no `native_decide`. Ledger delta: FG -0 +0 / T1 -0 +0.
namespace Tools.ShippingGen4FKidsLegacyH9
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
open Tools.ShippingGen4FKidsPrims
open Tools.ShippingGen4KWalkHelpers
open Tools.ShippingGen4FKidsHelpers
open Tools.ShippingChildLegacyHelpersA
open Tools.ShippingGen4KWalkLegacyH1
open Tools.ShippingGen4FKidsLegacyH1
open Tools.ShippingGen4KWalkLegacyH2
open Tools.ShippingGen4FKidsLegacyH2
open Tools.ShippingGen4KWalkEmit
open Tools.ShippingGen4FKidsEmit
open Tools.ShippingGen4KWalkLegacyRules
open Tools.ShippingGen4FKidsLegacyRules
open Tools.ShippingGen4KWalkLegacyH4
open Tools.ShippingGen4FKidsLegacyH4
open Tools.ShippingGen4KWalkCanon
open Tools.ShippingGen4FKidsCanon
open Tools.ShippingGen4KWalkLegacyH7
open Tools.ShippingGen4FKidsLegacyH7
open Tools.ShippingGen4KWalkLegacyH1
open Tools.ShippingGen4FKidsLegacyH1
open Tools.ShippingGen4KWalkLegacyH2
open Tools.ShippingGen4FKidsLegacyH2
open Tools.ShippingGen4KWalkProjField
open Tools.ShippingGen4FKidsProjField
open Tools.ShippingGen4KWalkDiag
open Tools.ShippingGen4FKidsDiag
open Tools.ShippingGen4KWalkLegacyH8a
open Tools.ShippingGen4FKidsLegacyH8a
open Tools.ShippingGen4KWalkLegacyH8
open Tools.ShippingGen4FKidsLegacyH8
open Tools.ShippingGen4KWalkLegacyH3
open Tools.ShippingGen4FKidsLegacyH3
open Tools.ShippingGen4KWalkLegacyH5
open Tools.ShippingGen4FKidsLegacyH5
open Tools.ShippingGen4KWalkLegacyH6
open Tools.ShippingGen4FKidsLegacyH6

open Tools.ShippingGen4FKids
open Tools.ShippingGen4FKidsCalc
open Tools.ShippingGen4FKidsPrims
open Tools.ShippingGen4FKidsTac
open Tools.ShippingGen4FKidsTele

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

section H9a
variable {O : RefLawsAOps MkRefd mref cref} {I : Void IO.RealWorld → Prop}
end H9a

set_option hygiene false in
macro "kwAll3" : tactic => `(tactic| swalkN [stderrPairCPkS M hS hA _ _, keepsK_msgToStringRS M hS hmsg hA _ _, keepsK_addMessageContextS M hA hS _, keepsK_ppExprS M hpp hS _ _,
  keepsK_throwErrorS M _ hS _ _, keepsK_getDeclS M hpp hS _ _, Keeps.withReaderA (q := O.quiet) _ _,
  extractWidthKS M hpp hS _ _, inferHWTypeKS M hpp hS _ _, extractDimExprKS M hpp hS _ _,
  inferHWTypeWithDimensionsKS M hpp hS _ _, inferHWTypeFromSignalKS M hpp hS _ _,
  isSignalBinderTypeKS M hpp hS _ _, extractNatKS M hpp hS _ _, getWireWidthKS M hpp hS _ _,
  getWireWidthDimKS M hpp hS _ _, cachedInferTypeKS M hpp hS _ _, extractBitVecLiteralKS M hpp hS _ _,
  extractNatLiteralKS M hpp hS _ _, extractBitVecListKS M hpp hS _ _, extractBitVecArrayKS M hpp hS _ _,
  lowerZeroExtendWireKS M hpp hS _ _ _ _ _,
  isTracingEnabledFor_keepsKS M hpp hS _ _, addTrace_keepsKS M hpp hS _ _ _,
  snapshotWireCaches_keepsKS M hpp hS _, restoreWireCaches_keepsKS M hpp hS _ _,
  makeWirePS M hA hS, addInputPS M hA hS, addOutputPS M hA hS, emitAssignP, bindSourceVariableP, lookupVarP,
  emitRegisterStmtA, emitRegisterK M hA hS, emitMemoryK M hA hS, freshNameA, emitInstanceA,
  canonHardwareKeyKS M hA hS _, withLocalDeclPKS M hS hA _ _ _, withLetDeclPKS M hS hA _ _ _ _, M.tele.telescope I _ hS.1 hS.2 _ _,
  addModuleToDesignA, withVarMappingP, withDimVarMappingPS, KeepsCS.tryCatch, KeepsCS.map _,
  keepsK_framedNM M hA hS (FramedNM.freshFVar (Fresh := MkRefd))])



section H9
variable {O : RefLawsAOps MkRefd mref cref} (M : MemoFamily O) (hpp : PpMvKS O) {I : Void IO.RealWorld → Prop}
  (hS : StableK O.quiet I) (hmsg : MsgMvK O)

include M hpp hS hmsg
theorem normSpineKS :
    ∀ (fuel : Nat) (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx →
      ∀ (x : Lean.Expr), Keeps mctx mref cctx cref I (Rec.translateExprToWireApp.normSpine x fuel)
  | 0, mctx, cctx, hA, x => by
    unfold Rec.translateExprToWireApp.normSpine
    kwAll3
  | fuel + 1, mctx, cctx, hA, x => by
    have ih := fun mctx cctx (hA : AdmCtx O.quiet mctx cctx) x => normSpineKS fuel mctx cctx hA x
    unfold Rec.translateExprToWireApp.normSpine
    kwAll3

end H9


section H9b
variable {O : RefLawsAOps MkRefd mref cref} (M : MemoFamily O) (hpp : PpMvKS O) {I : Void IO.RealWorld → Prop}
  (hS : StableK O.quiet I) (hmsg : MsgMvK O) (tr : TranslateFn)
  (htr : ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx →
    ∀ e hint top named, KeepsCS mctx mref cctx cref I (tr e hint top named))
  (hchild : ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx →
    ∀ c, Keeps mctx mref cctx cref I (childSynthEntry c))

set_option hygiene false in
macro "kwApp" : tactic => `(tactic| swalkN [handleErrorPatternsKS M hpp hS hA _ _ _ _ _, handleCircuitMonadKS M hpp hS tr htr hA _ _ _ _ _, handleTupleProjectionsKS M hpp hS tr htr hA _ _ _ _ _, handleApplicativeKS M hpp hS tr htr hA _ _ _ _ _, handleBitVecOpsKS M hpp hS tr htr hA _ _ _ _ _, handleRegisterKS M hpp hS tr htr hA _ _ _ _ _, handleMuxKS M hpp hS tr htr hA _ _ _ _ _, handleMemoryKS M hpp hS tr htr hA _ _ _ _ _, handleLoopKS M hpp hS tr htr hA _ _ _ _ _, handleDefinitionUnfoldKS M hpp hS hmsg tr htr hchild hA _ _ _ _ _, stderrPairCPkS M hS hA _ _, keepsK_msgToStringRS M hS hmsg hA _ _, keepsK_addMessageContextS M hA hS _, keepsK_ppExprS M hpp hS _ _,
  keepsK_throwErrorS M _ hS _ _, keepsK_getDeclS M hpp hS _ _, Keeps.withReaderA (q := O.quiet) _ _,
  extractWidthKS M hpp hS _ _, inferHWTypeKS M hpp hS _ _, extractDimExprKS M hpp hS _ _,
  inferHWTypeWithDimensionsKS M hpp hS _ _, inferHWTypeFromSignalKS M hpp hS _ _,
  isSignalBinderTypeKS M hpp hS _ _, extractNatKS M hpp hS _ _, getWireWidthKS M hpp hS _ _,
  getWireWidthDimKS M hpp hS _ _, cachedInferTypeKS M hpp hS _ _, extractBitVecLiteralKS M hpp hS _ _,
  extractNatLiteralKS M hpp hS _ _, extractBitVecListKS M hpp hS _ _, extractBitVecArrayKS M hpp hS _ _,
  lowerZeroExtendWireKS M hpp hS _ _ _ _ _,
  isTracingEnabledFor_keepsKS M hpp hS _ _, addTrace_keepsKS M hpp hS _ _ _,
  snapshotWireCaches_keepsKS M hpp hS _, restoreWireCaches_keepsKS M hpp hS _ _,
  makeWirePS M hA hS, addInputPS M hA hS, addOutputPS M hA hS, emitAssignP, bindSourceVariableP, lookupVarP,
  emitRegisterStmtA, emitRegisterK M hA hS, emitMemoryK M hA hS, freshNameA, emitInstanceA,
  canonHardwareKeyKS M hA hS _, withLocalDeclPKS M hS hA _ _ _, withLetDeclPKS M hS hA _ _ _ _, M.tele.telescope I _ hS.1 hS.2 _ _,
  addModuleToDesignA, withVarMappingP, withDimVarMappingPS, KeepsCS.tryCatch, KeepsCS.map _,
  keepsK_framedNM M hA hS (FramedNM.freshFVar (Fresh := MkRefd))])



include M hpp hS hmsg htr hchild

/-- **The dispatcher** `Rec.translateExprToWireApp`: the nine handlers in order, after the `Signal` pre-filters and `normSpine`. -/
theorem translateExprToWireAppKS (hA : AdmCtx O.quiet mctx cctx)
    (e : Lean.Expr) (hint : String) (named : Bool) :
    KeepsCS mctx mref cctx cref I (Rec.translateExprToWireApp tr e hint named) := by
  have hns := normSpineKS M hpp hS hmsg 32 mctx cctx hA
  unfold Rec.translateExprToWireApp
  kwApp

end H9b

end Tools.ShippingGen4FKidsLegacyH9
