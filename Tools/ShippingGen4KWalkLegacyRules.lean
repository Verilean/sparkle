import Tools.ShippingGen4KWalkLegacyH1
import Tools.ShippingGen4KWalkLegacyH2
import Tools.ShippingGen4KWalkEmit
import Tools.ShippingGen4KWalkLegacyH4
import Tools.ShippingGen4KWalkCanon
-- NOT BUILT (rt174 draft). LegacyImplK: the shared rule list `kwAll` of the K copies of the legacy handlers (a tactic macro only).
-- NO premise, NO law, NO axiom. No `sorry`, no `native_decide`. Ledger delta: FG -0 +0 / T1 -0 +0.
namespace Tools.ShippingGen4KWalkLegacyRules
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
open Tools.ShippingGen4KWalkLegacyH4
open Tools.ShippingGen4KWalkCanon
open Tools.ShippingGen4KWalkEmit
open Tools.ShippingGen4KWalkProjField

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

-- The rule list of the legacy handlers (names from the section: M, hpp, hA, hS).
set_option hygiene false in
macro "kwAll" : tactic => `(tactic| kwalkN [keepsK_addMessageContext M hA hS _, keepsK_ppExpr M hpp hS _ _,
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

end Tools.ShippingGen4KWalkLegacyRules
