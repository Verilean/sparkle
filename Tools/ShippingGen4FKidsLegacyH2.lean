import Tools.ShippingGen4FKidsTac
import Tools.ShippingGen4FKidsTele
import Tools.ShippingGen4FKidsCanon
import Tools.ShippingGen4KWalkHelpers
import Tools.ShippingGen4FKidsHelpers
import Tools.ShippingGen4KWalkDiag
import Tools.ShippingGen4FKidsDiag
import Tools.ShippingGen4KWalkProjField
import Tools.ShippingGen4FKidsProjField
import Tools.ShippingGen4KWalkTac2
import Tools.ShippingChildLegacyHandlersA
-- BUILT: kjob lake build Tools.ShippingGen4KWalkLegacyH2 exit 0 (rt174, source as of d8c3ec7b); clean build is the coder's. LegacyImplKS part 2: the helpers of Helpers.lean's A copy that the K copy did not cover (tracing, extractNat family, cachedInferType, getWireWidth*, lowerZeroExtendWire), walked by `swalkN` (Tac2).
-- Takes `MemoFamily` (TRUSTED, approved) as a HYPOTHESIS `M`; adds NO premise, NO law, NO axiom. No `sorry`, no `native_decide`. Ledger delta: FG -0 +0 / T1 -0 +0.
namespace Tools.ShippingGen4FKidsLegacyH2
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
open Tools.ShippingGen4KWalkProjField
open Tools.ShippingGen4FKidsProjField

open Tools.ShippingGen4FKids
open Tools.ShippingGen4FKidsCalc
open Tools.ShippingGen4FKidsPrims
open Tools.ShippingGen4FKidsTac
open Tools.ShippingGen4FKidsTele

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

section H2
variable {O : RefLawsAOps MkRefd mref cref} (M : MemoFamily O) (hpp : PpMvKS O) {I : Void IO.RealWorld → Prop}
  (hS : StableK O.quiet I)
include M hpp hS

set_option hygiene false in
macro "kwL0" : tactic => `(tactic| swalkN [keepsK_addMessageContextS M hA hS _, keepsK_ppExprS M hpp hS _ _, keepsK_throwErrorS M _ hS _ _,
  extractWidthKS M hpp hS _ _, inferHWTypeKS M hpp hS _ _, extractDimExprKS M hpp hS _ _,
  inferHWTypeWithDimensionsKS M hpp hS _ _, inferHWTypeFromSignalKS M hpp hS _ _,
  keepsK_getDeclS M hpp hS _ _, Keeps.withReaderA (q := O.quiet) _ _,
  makeWirePS M hA hS, addInputPS M hA hS, emitAssignP, bindSourceVariableP, lookupVarP])

set_option hygiene false in
macro "kwL" : tactic => `(tactic| swalkN [keepsK_addMessageContextS M hA hS _, keepsK_ppExprS M hpp hS _ _, keepsK_throwErrorS M _ hS _ _,
  extractWidthKS M hpp hS _ _, inferHWTypeKS M hpp hS _ _, extractDimExprKS M hpp hS _ _,
  inferHWTypeWithDimensionsKS M hpp hS _ _, inferHWTypeFromSignalKS M hpp hS _ _,
  keepsK_getDeclS M hpp hS _ _, Keeps.withReaderA (q := O.quiet) _ _,
  makeWirePS M hA hS, addInputPS M hA hS, emitAssignP, bindSourceVariableP, lookupVarP,
  extractNatKS M hpp hS _ _])

theorem isTracingEnabledFor_keepsKS (hA : AdmCtx O.quiet mctx cctx) (cls : Name) :
    Keeps mctx mref cctx cref I (Lean.isTracingEnabledFor cls : MetaM Bool) := by
  unfold Lean.isTracingEnabledFor
  kwL0

theorem addTrace_keepsKS (hA : AdmCtx O.quiet mctx cctx) (cls : Name) (msg : MessageData) :
    Keeps mctx mref cctx cref I (Lean.addTrace cls msg : MetaM Unit) := by
  unfold Lean.addTrace Lean.modifyTraces
  kwL0

theorem extractNatStepKS (hA : AdmCtx O.quiet mctx cctx) (rec : Lean.Expr → CompilerM Nat)
    (hrec : ∀ a, KeepsCS mctx mref cctx cref I (rec a)) (e : Lean.Expr) :
    KeepsCS mctx mref cctx cref I (extractNatStep rec e) := by
  unfold extractNatStep
  kwL0

theorem extractNatKS (hA : AdmCtx O.quiet mctx cctx) (e : Lean.Expr) :
    KeepsCS mctx mref cctx cref I (extractNat e) := by
  unfold extractNat
  exact Tools.ShippingGen4FKidsCanon.KeepsCS.fuelFixM extractNatStep (fun rec hrec a => extractNatStepKS M hpp hS hA rec hrec a) _ e

theorem getWireWidthKS (hA : AdmCtx O.quiet mctx cctx) (w : String) :
    KeepsCS mctx mref cctx cref I (CompilerM.getWireWidth w) := by
  unfold CompilerM.getWireWidth
  kwL

theorem getWireWidthDimKS (hA : AdmCtx O.quiet mctx cctx) (w : String) :
    KeepsCS mctx mref cctx cref I (CompilerM.getWireWidthDim w) := by
  unfold CompilerM.getWireWidthDim
  kwL

theorem cachedInferTypeKS (hA : AdmCtx O.quiet mctx cctx) (e : Lean.Expr) :
    KeepsCS mctx mref cctx cref I (cachedInferType e) := by
  unfold cachedInferType
  kwL

theorem extractBitVecLiteralKS (hA : AdmCtx O.quiet mctx cctx) (e : Lean.Expr) :
    KeepsCS mctx mref cctx cref I (extractBitVecLiteral e) := by
  unfold extractBitVecLiteral
  kwL

theorem extractNatLiteralKS (hA : AdmCtx O.quiet mctx cctx) (e : Lean.Expr) :
    KeepsCS mctx mref cctx cref I (extractNatLiteral e) := by
  unfold extractNatLiteral
  kwL

theorem lowerZeroExtendWireKS (hA : AdmCtx O.quiet mctx cctx) (hint src : String)
    (t : Sparkle.IR.Type.DimExpr) (named : Bool) :
    KeepsCS mctx mref cctx cref I (lowerZeroExtendWire hint src t named) := by
  unfold lowerZeroExtendWire
  kwL

theorem extractBitVecListStepKS (hA : AdmCtx O.quiet mctx cctx)
    (rec : Lean.Expr → CompilerM (Array (Nat × Nat)))
    (hrec : ∀ a, KeepsCS mctx mref cctx cref I (rec a)) (e : Lean.Expr) :
    KeepsCS mctx mref cctx cref I (extractBitVecListStep rec e) := by
  unfold extractBitVecListStep
  swalkN [keepsK_addMessageContextS M hA hS _, keepsK_ppExprS M hpp hS _ _, keepsK_throwErrorS M _ hS _ _,
    extractNatKS M hpp hS _ _, extractBitVecLiteralKS M hpp hS _ _]

theorem extractBitVecListKS (hA : AdmCtx O.quiet mctx cctx) (e : Lean.Expr) :
    KeepsCS mctx mref cctx cref I (extractBitVecList e) := by
  unfold extractBitVecList
  exact Tools.ShippingGen4FKidsCanon.KeepsCS.fuelFixM extractBitVecListStep (fun rec hrec a => extractBitVecListStepKS M hpp hS hA rec hrec a) _ e

theorem extractBitVecArrayKS (hA : AdmCtx O.quiet mctx cctx) (e : Lean.Expr) :
    KeepsCS mctx mref cctx cref I (extractBitVecArray e) := by
  unfold extractBitVecArray
  swalkN [keepsK_ppExprS M hpp hS _ _, keepsK_throwErrorS M _ hS _ _, extractBitVecListKS M hpp hS _ _]

end H2

end Tools.ShippingGen4FKidsLegacyH2
