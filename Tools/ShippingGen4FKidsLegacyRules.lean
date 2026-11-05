import Tools.ShippingGen4FKidsTac
import Tools.ShippingGen4FKidsTele
import Tools.ShippingGen4FKidsCanon
import Tools.ShippingGen4KWalkLegacyH1
import Tools.ShippingGen4FKidsLegacyH1
import Tools.ShippingGen4KWalkLegacyH2
import Tools.ShippingGen4FKidsLegacyH2
import Tools.ShippingGen4KWalkEmit
import Tools.ShippingGen4FKidsEmit
import Tools.ShippingGen4KWalkLegacyH4
import Tools.ShippingGen4FKidsLegacyH4
import Tools.ShippingGen4KWalkCanon
import Tools.ShippingGen4FKidsCanon
-- BUILT: kjob lake build Tools.ShippingGen4KWalkLegacyRules exit 0 (rt174, source as of d8c3ec7b); clean build is the coder's. LegacyImplKS: the shared rule list `kwAll` of the K copies of the legacy handlers (a tactic macro only).
-- NO premise, NO law, NO axiom. No `sorry`, no `native_decide`. Ledger delta: FG -0 +0 / T1 -0 +0.
namespace Tools.ShippingGen4FKidsLegacyRules
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
open Tools.ShippingGen4KWalkLegacyH4
open Tools.ShippingGen4FKidsLegacyH4
open Tools.ShippingGen4KWalkCanon
open Tools.ShippingGen4FKidsCanon
open Tools.ShippingGen4KWalkEmit
open Tools.ShippingGen4FKidsEmit
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

-- The rule list of the legacy handlers (names from the section: M, hpp, hA, hS).
set_option hygiene false in
macro "kwAll" : tactic => `(tactic| swalkN [keepsK_addMessageContextS M hA hS _, keepsK_ppExprS M hpp hS _ _,
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

end Tools.ShippingGen4FKidsLegacyRules
