import Tools.ShippingGen4KWalkHelpers
import Tools.ShippingGen4KWalkDiag
import Tools.ShippingGen4KWalkProjField
import Tools.ShippingGen4KWalkTac2
import Tools.ShippingChildLegacyHandlersA
-- BUILT: kjob lake build Tools.ShippingGen4KWalkLegacyH2 exit 0 (rt174, source as of d8c3ec7b); clean build is the coder's. LegacyImplK part 2: the helpers of Helpers.lean's A copy that the K copy did not cover (tracing, extractNat family, cachedInferType, getWireWidth*, lowerZeroExtendWire), walked by `kwalkN` (Tac2).
-- Takes `MemoFamily` (TRUSTED, approved) as a HYPOTHESIS `M`; adds NO premise, NO law, NO axiom. No `sorry`, no `native_decide`. Ledger delta: FG -0 +0 / T1 -0 +0.
namespace Tools.ShippingGen4KWalkLegacyH2
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
open Tools.ShippingGen4KWalkProjField

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

section H2
variable {O : RefLawsAOps MkRefd mref cref} (M : MemoFamily O) (hpp : PpMvK O) {I : Void IO.RealWorld → Prop}
  (hS : StableK O.quiet I)
include M hpp hS

set_option hygiene false in
macro "kwL0" : tactic => `(tactic| kwalkN [keepsK_addMessageContext M hA hS _, keepsK_ppExpr M hpp hS _ _, keepsK_throwError M _ hS _ _,
  extractWidthK M hpp hS _ _, inferHWTypeK M hpp hS _ _, extractDimExprK M hpp hS _ _,
  inferHWTypeWithDimensionsK M hpp hS _ _, inferHWTypeFromSignalK M hpp hS _ _,
  keepsK_getDecl M hpp hS _ _, Keeps.withReaderA (q := O.quiet) _ _,
  makeWirePK M hA hS, addInputPK M hA hS, emitAssignP, bindSourceVariableP, lookupVarP])

set_option hygiene false in
macro "kwL" : tactic => `(tactic| kwalkN [keepsK_addMessageContext M hA hS _, keepsK_ppExpr M hpp hS _ _, keepsK_throwError M _ hS _ _,
  extractWidthK M hpp hS _ _, inferHWTypeK M hpp hS _ _, extractDimExprK M hpp hS _ _,
  inferHWTypeWithDimensionsK M hpp hS _ _, inferHWTypeFromSignalK M hpp hS _ _,
  keepsK_getDecl M hpp hS _ _, Keeps.withReaderA (q := O.quiet) _ _,
  makeWirePK M hA hS, addInputPK M hA hS, emitAssignP, bindSourceVariableP, lookupVarP,
  extractNatK M hpp hS _ _])

theorem isTracingEnabledFor_keepsK (hA : AdmCtx O.quiet mctx cctx) (cls : Name) :
    Keeps mctx mref cctx cref I (Lean.isTracingEnabledFor cls : MetaM Bool) := by
  unfold Lean.isTracingEnabledFor
  kwL0

theorem addTrace_keepsK (hA : AdmCtx O.quiet mctx cctx) (cls : Name) (msg : MessageData) :
    Keeps mctx mref cctx cref I (Lean.addTrace cls msg : MetaM Unit) := by
  unfold Lean.addTrace Lean.modifyTraces
  kwL0

theorem extractNatStepK (hA : AdmCtx O.quiet mctx cctx) (rec : Lean.Expr → CompilerM Nat)
    (hrec : ∀ a, KeepsCP mctx mref cctx cref I (rec a)) (e : Lean.Expr) :
    KeepsCP mctx mref cctx cref I (extractNatStep rec e) := by
  unfold extractNatStep
  kwL0

theorem extractNatK (hA : AdmCtx O.quiet mctx cctx) (e : Lean.Expr) :
    KeepsCP mctx mref cctx cref I (extractNat e) := by
  unfold extractNat
  exact fuelFixM_keepsCP extractNatStep
    (fun rec hrec mctx cctx hA a => extractNatStepK M hpp hS hA rec (hrec mctx cctx hA) a) _ mctx cctx hA e

theorem getWireWidthK (hA : AdmCtx O.quiet mctx cctx) (w : String) :
    KeepsCP mctx mref cctx cref I (CompilerM.getWireWidth w) := by
  unfold CompilerM.getWireWidth
  kwL

theorem getWireWidthDimK (hA : AdmCtx O.quiet mctx cctx) (w : String) :
    KeepsCP mctx mref cctx cref I (CompilerM.getWireWidthDim w) := by
  unfold CompilerM.getWireWidthDim
  kwL

theorem cachedInferTypeK (hA : AdmCtx O.quiet mctx cctx) (e : Lean.Expr) :
    KeepsCP mctx mref cctx cref I (cachedInferType e) := by
  unfold cachedInferType
  kwL

theorem extractBitVecLiteralK (hA : AdmCtx O.quiet mctx cctx) (e : Lean.Expr) :
    KeepsCP mctx mref cctx cref I (extractBitVecLiteral e) := by
  unfold extractBitVecLiteral
  kwL

theorem extractNatLiteralK (hA : AdmCtx O.quiet mctx cctx) (e : Lean.Expr) :
    KeepsCP mctx mref cctx cref I (extractNatLiteral e) := by
  unfold extractNatLiteral
  kwL

theorem lowerZeroExtendWireK (hA : AdmCtx O.quiet mctx cctx) (hint src : String)
    (t : Sparkle.IR.Type.DimExpr) (named : Bool) :
    KeepsCP mctx mref cctx cref I (lowerZeroExtendWire hint src t named) := by
  unfold lowerZeroExtendWire
  kwL

theorem extractBitVecListStepK (hA : AdmCtx O.quiet mctx cctx)
    (rec : Lean.Expr → CompilerM (Array (Nat × Nat)))
    (hrec : ∀ a, KeepsCP mctx mref cctx cref I (rec a)) (e : Lean.Expr) :
    KeepsCP mctx mref cctx cref I (extractBitVecListStep rec e) := by
  unfold extractBitVecListStep
  kwalkN [keepsK_addMessageContext M hA hS _, keepsK_ppExpr M hpp hS _ _, keepsK_throwError M _ hS _ _,
    extractNatK M hpp hS _ _, extractBitVecLiteralK M hpp hS _ _]

theorem extractBitVecListK (hA : AdmCtx O.quiet mctx cctx) (e : Lean.Expr) :
    KeepsCP mctx mref cctx cref I (extractBitVecList e) := by
  unfold extractBitVecList
  exact fuelFixM_keepsCP extractBitVecListStep
    (fun rec hrec mctx cctx hA a => extractBitVecListStepK M hpp hS hA rec (hrec mctx cctx hA) a) _ mctx cctx hA e

theorem extractBitVecArrayK (hA : AdmCtx O.quiet mctx cctx) (e : Lean.Expr) :
    KeepsCP mctx mref cctx cref I (extractBitVecArray e) := by
  unfold extractBitVecArray
  kwalkN [keepsK_ppExpr M hpp hS _ _, keepsK_throwError M _ hS _ _, extractBitVecListK M hpp hS _ _]

end H2

end Tools.ShippingGen4KWalkLegacyH2
