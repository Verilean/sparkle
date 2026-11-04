import Tools.ShippingGen4KWalkHelpers
import Tools.ShippingGen4KWalkDiag
import Tools.ShippingGen4KWalkProjField
import Tools.ShippingChildLegacyHandlersA
-- NOT BUILT (rt174 draft). LegacyImplK part 1: `snapshotWireCaches`, `restoreWireCaches`, `handleErrorPatterns` (copy of the first handlers of ShippingChildLegacyHandlersA, walked by `kwalkM`).
-- Takes `MemoFamily` (TRUSTED, approved) as a HYPOTHESIS `M`; adds NO premise, NO law, NO axiom. `PpMvK` is derived by `ppMvK_of M` by the caller. No `sorry`, no `native_decide`. Ledger delta: FG -0 +0 / T1 -0 +0.
namespace Tools.ShippingGen4KWalkLegacyH1
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
open Tools.ShippingChildWalkA
open Tools.Assume.MemoFamily
open Tools.ShippingGen4KWalk
open Tools.ShippingGen4KWalkPrims
open Tools.ShippingGen4KWalkHelpers
open Tools.ShippingGen4KWalkProjField

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

section H1
variable {O : RefLawsAOps MkRefd mref cref} (M : MemoFamily O) (hpp : PpMvK O) {I : Void IO.RealWorld → Prop}
  (hS : StableK O.quiet I)
include M hpp hS

theorem snapshotWireCaches_keepsK (hA : AdmCtx O.quiet mctx cctx) :
    KeepsCP mctx mref cctx cref I snapshotWireCaches := by
  unfold snapshotWireCaches
  refine KeepsCP.bindCtx (fun cs hcs => ?_)
  cases hc : cs.exprCache with
  | none =>
    dsimp only
    kwalkM [keepsK_framedNM M _ hS (FramedNM.sideGetIO SideRefNM.letWire),
      keepsK_framedNM M _ hS (FramedNM.sideGetIO SideRefNM.loopWire),
      keepsK_framedNM M _ hS (FramedNM.sideGetIO SideRefNM.wireCanon),
      keepsK_framedNM M _ hS (FramedNM.sideGetIO SideRefNM.singleOut),
      keepsK_framedNM M _ hS (FramedNM.sideGetIO SideRefNM.subInstOut),
      keepsK_framedNM M _ hS (FramedNM.sideGetIO SideRefNM.wireWidth),
      keepsK_framedNM M _ hS (FramedNM.sideGetIO SideRefNM.fvarValue),
      keepsK_framedNM M _ hS (FramedNM.sideGetIO SideRefNM.fvarZetaVisited)]
  | some ref =>
    dsimp only
    kwalkM [keepsK_framedNM M _ hS (FramedNM.exprCacheGetIO ref (hcs ref hc)),
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
  kwalkM [keepsK_framedNM M hA hS (FramedNM.sideSetIO _ SideRefNM.letWire),
      keepsK_framedNM M hA hS (FramedNM.sideSetIO _ SideRefNM.loopWire),
      keepsK_framedNM M hA hS (FramedNM.sideSetIO _ SideRefNM.wireCanon),
      keepsK_framedNM M hA hS (FramedNM.sideSetIO _ SideRefNM.singleOut),
      keepsK_framedNM M hA hS (FramedNM.sideSetIO _ SideRefNM.subInstOut),
      keepsK_framedNM M hA hS (FramedNM.sideSetIO _ SideRefNM.wireWidth),
      keepsK_framedNM M hA hS (FramedNM.sideSetIO _ SideRefNM.fvarValue),
      keepsK_framedNM M hA hS (FramedNM.sideSetIO _ SideRefNM.fvarZetaVisited)])

theorem restoreWireCaches_keepsK (hA : AdmCtx O.quiet mctx cctx) (c : WireCaches) :
    KeepsCP mctx mref cctx cref I (restoreWireCaches c) := by
  unfold restoreWireCaches
  refine KeepsCP.bindCtx (fun cs hcs => ?_)
  cases hc : cs.exprCache with
  | none => cases hx : c.expr <;> dsimp only <;> kwSet
  | some ref =>
    cases hx : c.expr with
    | none => dsimp only; kwSet
    | some m =>
      dsimp only
      refine KeepsCP.bind (KeepsCP.lift (keepsK_framedNM M hA hS
        (FramedNM.localSetIO ref m LocalRefType.exprCache (hcs ref hc)))) (fun _ => ?_)
      kwSet

theorem handleErrorPatternsK (hA : AdmCtx O.quiet mctx cctx)
    (e : Lean.Expr) (name : Name) (args : Array Lean.Expr) (hint : String) (named : Bool) :
    KeepsCP mctx mref cctx cref I (Rec.handleErrorPatterns e name args hint named) := by
  unfold Rec.handleErrorPatterns
  kwalkM [keepsK_ppExpr M hpp hS _ _, keepsK_throwError M _ hS _ _]

end H1

end Tools.ShippingGen4KWalkLegacyH1
