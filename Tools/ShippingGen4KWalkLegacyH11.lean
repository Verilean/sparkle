import Tools.ShippingGen4KWalkLegacyH10a
import Tools.ShippingGen4KWalkLegacyH10b
import Tools.ShippingGen4KWalkLegacyH8d
-- BUILT (rt180): kjob lake build Tools.ShippingGen4KWalkLegacyH11 exit 0, 8.6 s, peak RSS 3.8 GB (axioms propext, Classical.choice, Quot.sound); clean build is the coder's. LegacyImplK part 11: the main body `Rec.translateExprToWireImpl`.
namespace Tools.ShippingGen4KWalkLegacyH11
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
open Tools.ShippingGen4KWalkLegacyH8d
open Tools.ShippingGen4KWalkLegacyH8
open Tools.ShippingGen4KWalkLegacyH3
open Tools.ShippingGen4KWalkLegacyH5
open Tools.ShippingGen4KWalkLegacyH6
open Tools.ShippingGen4KWalkLegacyH9
open Tools.ShippingGen4KWalkLegacyH10a
open Tools.ShippingGen4KWalkLegacyH10b
open Tools.ShippingGen4KWalkLegacyH7
open Tools.ShippingGen4KWalkTranslate

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false


section H10b
variable {O : RefLawsAOps MkRefd mref cref} (M : MemoFamily O) (hpp : PpMvK O) {I : Void IO.RealWorld → Prop}
  (hS : StableK O.quiet I) (hmsg : MsgMvK O) (tr : TranslateFn)
  (htr : ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx →
    ∀ e hint top named, KeepsCP mctx mref cctx cref I (tr e hint top named))
  (hchild : ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx →
    ∀ c, Keeps mctx mref cctx cref I (childSynthEntry c))

set_option hygiene false in
-- (rt177) the context's `AdmCtx` is found by `assumption` (after a `withLocalDecl` the newest `hA` is an inaccessible name, and `hA` named the OUTER one: the rule then failed to unify and the walk unfolded the callee)
macro "kwMain" : tactic => `(tactic| kwalkS [translateExprToWireAppK M hpp hS hmsg tr htr hchild (by assumption) _ _ _, getPrimK M hpp hS hmsg (by assumption) _, toIRK M hpp hS hmsg _ _ (by assumption) _, handleErrorPatternsK M hpp hS (by assumption) _ _ _ _ _, handleCircuitMonadK M hpp hS tr htr (by assumption) _ _ _ _ _, handleTupleProjectionsK M hpp hS tr htr (by assumption) _ _ _ _ _, handleApplicativeK M hpp hS tr htr (by assumption) _ _ _ _ _, handleBitVecOpsK M hpp hS tr htr (by assumption) _ _ _ _ _, handleRegisterK M hpp hS tr htr (by assumption) _ _ _ _ _, handleMuxK M hpp hS tr htr (by assumption) _ _ _ _ _, handleMemoryK M hpp hS tr htr (by assumption) _ _ _ _ _, handleLoopK M hpp hS tr htr (by assumption) _ _ _ _ _, handleDefinitionUnfoldK M hpp hS hmsg tr htr hchild (by assumption) _ _ _ _ _, stderrPairCPk M hS (by assumption) _ _, profBlockCPk2 M hS (by assumption) _ _, keepsK_profBlock M hS (by assumption) _, keepsK_msgToStringR M hS hmsg (by assumption) _ _, keepsK_addMessageContext M (by assumption) hS _, keepsK_ppExpr M hpp hS _ _,
  keepsK_throwError M _ hS _ _, keepsK_getDecl M hpp hS _ _, Keeps.withReaderA (q := O.quiet) _ _,
  extractWidthK M hpp hS _ _, inferHWTypeK M hpp hS _ _, extractDimExprK M hpp hS _ _,
  inferHWTypeWithDimensionsK M hpp hS _ _, inferHWTypeFromSignalK M hpp hS _ _,
  isSignalBinderTypeK M hpp hS _ _, extractNatK M hpp hS _ _, getWireWidthK M hpp hS _ _,
  getWireWidthDimK M hpp hS _ _, cachedInferTypeK M hpp hS _ _, extractBitVecLiteralK M hpp hS _ _,
  extractNatLiteralK M hpp hS _ _, extractBitVecListK M hpp hS _ _, extractBitVecArrayK M hpp hS _ _,
  lowerZeroExtendWireK M hpp hS _ _ _ _ _,
  isTracingEnabledFor_keepsK M hpp hS _ _, addTrace_keepsK M hpp hS _ _ _,
  snapshotWireCaches_keepsK M hpp hS _, restoreWireCaches_keepsK M hpp hS _ _,
  makeWirePK M (by assumption) hS, addInputPK M (by assumption) hS, addOutputPK M (by assumption) hS, emitAssignP, bindSourceVariableP, lookupVarP,
  emitRegisterStmtA, emitRegisterK M (by assumption) hS, emitMemoryK M (by assumption) hS, freshNameA, emitInstanceA,
  canonHardwareKeyK M (by assumption) hS _, withLocalDeclPK M hS (by assumption) _ _ _, withLetDeclPK M hS (by assumption) _ _ _ _, M.tele.telescope I _ hS.1 hS.2 _ _,
  addModuleToDesignA, withVarMappingP, withDimVarMappingP, KeepsCP.tryCatch, KeepsCP.map _,
  keepsK_framedNM M (by assumption) hS (FramedNM.freshFVar (Fresh := MkRefd))])




include M hpp hS hmsg htr hchild

/-- **The legacy translator's main body keeps `I`**, given the child entry. -/
theorem legacyImplKcore (hA : AdmCtx O.quiet mctx cctx)
    (e : Lean.Expr) (hint : String) (top named : Bool) :
    KeepsCP mctx mref cctx cref I (Rec.translateExprToWireImpl tr e hint top named) := by
  unfold Rec.translateExprToWireImpl
  kwMain

end H10b

end Tools.ShippingGen4KWalkLegacyH11

#print axioms Tools.ShippingGen4KWalkLegacyH11.legacyImplKcore
