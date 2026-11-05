import Tools.ShippingGen4FKidsTac
import Tools.ShippingGen4FKidsTele
import Tools.ShippingGen4FKidsCanon
import Tools.ShippingGen4KWalkHelpers
import Tools.ShippingGen4FKidsHelpers
import Tools.ShippingGen4KWalkDiag
import Tools.ShippingGen4FKidsDiag
import Tools.ShippingGen4KWalkProjField
import Tools.ShippingGen4FKidsProjField
import Tools.ShippingChildLegacyHandlersA
-- BUILT: kjob lake build Tools.ShippingGen4KWalkLegacyH1 exit 0 (rt174, source as of d8c3ec7b); clean build is the coder's. LegacyImplKS part 1: `snapshotWireCaches`, `restoreWireCaches`, `handleErrorPatterns` (copy of the first handlers of ShippingChildLegacyHandlersA, walked by `swalkN`).
-- Takes `MemoFamily` (TRUSTED, approved) as a HYPOTHESIS `M`; adds NO premise, NO law, NO axiom. `PpMvKS` is derived by `ppMvK_of M` by the caller. No `sorry`, no `native_decide`. Ledger delta: FG -0 +0 / T1 -0 +0.
namespace Tools.ShippingGen4FKidsLegacyH1
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
open Tools.ShippingGen4KWalkTac
open Tools.ShippingGen4FKidsTac
open Tools.ShippingChildWalkA
open Tools.Assume.MemoFamily
open Tools.ShippingGen4KWalk
open Tools.ShippingGen4KWalkPrims
open Tools.ShippingGen4FKidsPrims
open Tools.ShippingGen4KWalkHelpers
open Tools.ShippingGen4FKidsHelpers
open Tools.ShippingGen4KWalkProjField
open Tools.ShippingGen4FKidsProjField

open Tools.ShippingGen4FKids
open Tools.ShippingGen4FKidsCalc
open Tools.ShippingGen4FKidsPrims
open Tools.ShippingGen4FKidsTac
open Tools.ShippingGen4FKidsTele
open Tools.ShippingGen4FKidsEntry

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

section H1
variable {O : RefLawsAOps MkRefd mref cref} (M : MemoFamily O) (hpp : PpMvKS O) {I : Void IO.RealWorld → Prop}
  (hS : StableK O.quiet I)
include M hpp hS

theorem snapshotWireCaches_keepsKS (hA : AdmCtx O.quiet mctx cctx) :
    KeepsCS mctx mref cctx cref I snapshotWireCaches := by
  unfold snapshotWireCaches
  refine KeepsCS.bindCtx (fun cs hcs => ?_)
  cases hc : cs.exprCache with
  | none =>
    dsimp only
    swalkN [keepsK_framedNM M _ hS (FramedNM.sideGetIO SideRefNM.letWire),
      keepsK_framedNM M _ hS (FramedNM.sideGetIO SideRefNM.loopWire),
      keepsK_framedNM M _ hS (FramedNM.sideGetIO SideRefNM.wireCanon),
      keepsK_framedNM M _ hS (FramedNM.sideGetIO SideRefNM.singleOut),
      keepsK_framedNM M _ hS (FramedNM.sideGetIO SideRefNM.subInstOut),
      keepsK_framedNM M _ hS (FramedNM.sideGetIO SideRefNM.wireWidth),
      keepsK_framedNM M _ hS (FramedNM.sideGetIO SideRefNM.fvarValue),
      keepsK_framedNM M _ hS (FramedNM.sideGetIO SideRefNM.fvarZetaVisited)]
  | some ref =>
    dsimp only
    swalkN [keepsK_framedNM M _ hS (FramedNM.exprCacheGetIO ref (hcs ref hc)),
      keepsK_framedNM M _ hS (FramedNM.sideGetIO SideRefNM.letWire),
      keepsK_framedNM M _ hS (FramedNM.sideGetIO SideRefNM.loopWire),
      keepsK_framedNM M _ hS (FramedNM.sideGetIO SideRefNM.wireCanon),
      keepsK_framedNM M _ hS (FramedNM.sideGetIO SideRefNM.singleOut),
      keepsK_framedNM M _ hS (FramedNM.sideGetIO SideRefNM.subInstOut),
      keepsK_framedNM M _ hS (FramedNM.sideGetIO SideRefNM.wireWidth),
      keepsK_framedNM M _ hS (FramedNM.sideGetIO SideRefNM.fvarValue),
      keepsK_framedNM M _ hS (FramedNM.sideGetIO SideRefNM.fvarZetaVisited)]

set_option hygiene false in
macro "kwSet" : tactic => `(tactic|
  swalkN [keepsK_framedNM M hA hS (FramedNM.sideSetIO _ SideRefNM.letWire),
      keepsK_framedNM M hA hS (FramedNM.sideSetIO _ SideRefNM.loopWire),
      keepsK_framedNM M hA hS (FramedNM.sideSetIO _ SideRefNM.wireCanon),
      keepsK_framedNM M hA hS (FramedNM.sideSetIO _ SideRefNM.singleOut),
      keepsK_framedNM M hA hS (FramedNM.sideSetIO _ SideRefNM.subInstOut),
      keepsK_framedNM M hA hS (FramedNM.sideSetIO _ SideRefNM.wireWidth),
      keepsK_framedNM M hA hS (FramedNM.sideSetIO _ SideRefNM.fvarValue),
      keepsK_framedNM M hA hS (FramedNM.sideSetIO _ SideRefNM.fvarZetaVisited)])

theorem restoreWireCaches_keepsKS (hA : AdmCtx O.quiet mctx cctx) (c : WireCaches) :
    KeepsCS mctx mref cctx cref I (restoreWireCaches c) := by
  unfold restoreWireCaches
  refine KeepsCS.bindCtx (fun cs hcs => ?_)
  cases hc : cs.exprCache with
  | none => cases hx : c.expr <;> dsimp only <;> kwSet
  | some ref =>
    cases hx : c.expr with
    | none => dsimp only; kwSet
    | some m =>
      dsimp only
      refine KeepsCS.bind (KeepsCS.lift (keepsK_framedNM M hA hS
        (FramedNM.localSetIO ref m LocalRefType.exprCache (hcs ref hc)))) (fun _ => ?_)
      kwSet

theorem handleErrorPatternsKS (hA : AdmCtx O.quiet mctx cctx)
    (e : Lean.Expr) (name : Name) (args : Array Lean.Expr) (hint : String) (named : Bool) :
    KeepsCS mctx mref cctx cref I (Rec.handleErrorPatterns e name args hint named) := by
  unfold Rec.handleErrorPatterns
  swalkN [keepsK_ppExprS M hpp hS _ _, keepsK_throwErrorS M _ hS _ _]

end H1

end Tools.ShippingGen4FKidsLegacyH1
