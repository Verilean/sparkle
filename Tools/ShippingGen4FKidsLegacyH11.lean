import Tools.ShippingGen4FKidsTac
import Tools.ShippingGen4FKidsTele
import Tools.ShippingGen4FKidsCanon
import Tools.ShippingGen4KWalkLegacyH10a
import Tools.ShippingGen4FKidsLegacyH10a
import Tools.ShippingGen4KWalkLegacyH10b
import Tools.ShippingGen4FKidsLegacyH10b
import Tools.ShippingGen4KWalkLegacyH8d
import Tools.ShippingGen4FKidsLegacyH8d
-- BUILT (rt180): kjob lake build Tools.ShippingGen4KWalkLegacyH11 exit 0, 8.6 s, peak RSS 3.8 GB (axioms propext, Classical.choice, Quot.sound); clean build is the coder's. LegacyImplKS part 11: the main body `Rec.translateExprToWireImpl`.
namespace Tools.ShippingGen4FKidsLegacyH11
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
open Tools.ShippingGen4KWalkLegacyH8d
open Tools.ShippingGen4FKidsLegacyH8d
open Tools.ShippingGen4KWalkLegacyH8
open Tools.ShippingGen4FKidsLegacyH8
open Tools.ShippingGen4KWalkLegacyH3
open Tools.ShippingGen4FKidsLegacyH3
open Tools.ShippingGen4KWalkLegacyH5
open Tools.ShippingGen4FKidsLegacyH5
open Tools.ShippingGen4KWalkLegacyH6
open Tools.ShippingGen4FKidsLegacyH6
open Tools.ShippingGen4KWalkLegacyH9
open Tools.ShippingGen4FKidsLegacyH9
open Tools.ShippingGen4KWalkLegacyH10a
open Tools.ShippingGen4FKidsLegacyH10a
open Tools.ShippingGen4KWalkLegacyH10b
open Tools.ShippingGen4FKidsLegacyH10b
open Tools.ShippingGen4KWalkLegacyH7
open Tools.ShippingGen4FKidsLegacyH7
open Tools.ShippingGen4KWalkTranslate
open Tools.ShippingGen4FKidsTranslate

open Tools.ShippingGen4FKids
open Tools.ShippingGen4FKidsCalc
open Tools.ShippingGen4FKidsPrims
open Tools.ShippingGen4FKidsTac
open Tools.ShippingGen4FKidsTele
open Tools.ShippingGen4FKidsEntry

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false


section H10b
variable {O : RefLawsAOps MkRefd mref cref} (M : MemoFamily O) (hpp : PpMvKS O) {I : Void IO.RealWorld → Prop}
  (hS : StableK O.quiet I) (hmsg : MsgMvK O) (tr : TranslateFn)
  (htr : ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx →
    ∀ e hint top named, KeepsCS mctx mref cctx cref I (tr e hint top named))
  (hchild : ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx →
    ∀ c, Triple mctx mref cctx cref I (childSynthEntry c)
      (fun r w => I w ∧ PairPF r) (fun e w => I w ∧ OkExc e))

set_option hygiene false in
-- (rt177) the context's `AdmCtx` is found by `assumption` (after a `withLocalDecl` the newest `hA` is an inaccessible name, and `hA` named the OUTER one: the rule then failed to unify and the walk unfolded the callee)
macro "kwMain" : tactic => `(tactic| swalkS [translateExprToWireAppKS M hpp hS hmsg tr htr hchild (by assumption) _ _ _, getPrimKS M hpp hS hmsg (by assumption) _, toIRKS M hpp hS hmsg _ _ (by assumption) _, handleErrorPatternsKS M hpp hS (by assumption) _ _ _ _ _, handleCircuitMonadKS M hpp hS tr htr (by assumption) _ _ _ _ _, handleTupleProjectionsKS M hpp hS tr htr (by assumption) _ _ _ _ _, handleApplicativeKS M hpp hS tr htr (by assumption) _ _ _ _ _, handleBitVecOpsKS M hpp hS tr htr (by assumption) _ _ _ _ _, handleRegisterKS M hpp hS tr htr (by assumption) _ _ _ _ _, handleMuxKS M hpp hS tr htr (by assumption) _ _ _ _ _, handleMemoryKS M hpp hS tr htr (by assumption) _ _ _ _ _, handleLoopKS M hpp hS tr htr (by assumption) _ _ _ _ _, handleDefinitionUnfoldKS M hpp hS hmsg tr htr hchild (by assumption) _ _ _ _ _, stderrPairCPkS M hS (by assumption) _ _, profBlockCPk2S M hS (by assumption) _ _, keepsK_profBlockS M hS (by assumption) _, keepsK_msgToStringRS M hS hmsg (by assumption) _ _, keepsK_addMessageContextS M (by assumption) hS _, keepsK_ppExprS M hpp hS _ _,
  keepsK_throwErrorS M _ hS _ _, keepsK_getDeclS M hpp hS _ _, Keeps.withReaderA (q := O.quiet) _ _,
  extractWidthKS M hpp hS _ _, inferHWTypeKS M hpp hS _ _, extractDimExprKS M hpp hS _ _,
  inferHWTypeWithDimensionsKS M hpp hS _ _, inferHWTypeFromSignalKS M hpp hS _ _,
  isSignalBinderTypeKS M hpp hS _ _, extractNatKS M hpp hS _ _, getWireWidthKS M hpp hS _ _,
  getWireWidthDimKS M hpp hS _ _, cachedInferTypeKS M hpp hS _ _, extractBitVecLiteralKS M hpp hS _ _,
  extractNatLiteralKS M hpp hS _ _, extractBitVecListKS M hpp hS _ _, extractBitVecArrayKS M hpp hS _ _,
  lowerZeroExtendWireKS M hpp hS _ _ _ _ _,
  isTracingEnabledFor_keepsKS M hpp hS _ _, addTrace_keepsKS M hpp hS _ _ _,
  snapshotWireCaches_keepsKS M hpp hS _, restoreWireCaches_keepsKS M hpp hS _ _,
  makeWirePS M (by assumption) hS, addInputPS M (by assumption) hS, addOutputPS M (by assumption) hS, emitAssignPS, bindSourceVariablePS, lookupVarPS,
  emitRegisterStmtPS, emitRegisterPS M (by assumption) hS, emitMemoryPS M (by assumption) hS, freshNamePS, emitInstancePS,
  canonHardwareKeyKS M (by assumption) hS _, withLocalDeclPKS M hS (by assumption) _ _ _, withLetDeclPKS M hS (by assumption) _ _ _ _, M.tele.telescope I _ hS.1 hS.2 _ _,
  addModuleToDesignPS, withVarMappingPS, withDimVarMappingPS, KeepsCS.tryCatch, KeepsCS.map _,
  keepsK_framedNM M (by assumption) hS (FramedNM.freshFVar (Fresh := MkRefd))])




include M hpp hS hmsg htr hchild

/-- **The legacy translator's main body keeps `I`**, given the child entry. -/
theorem legacyImplKcoreS (hA : AdmCtx O.quiet mctx cctx)
    (e : Lean.Expr) (hint : String) (top named : Bool) :
    KeepsCS mctx mref cctx cref I (Rec.translateExprToWireImpl tr e hint top named) := by
  unfold Rec.translateExprToWireImpl
  kwMain

end H10b

end Tools.ShippingGen4FKidsLegacyH11

#print axioms Tools.ShippingGen4FKidsLegacyH11.legacyImplKcoreS
