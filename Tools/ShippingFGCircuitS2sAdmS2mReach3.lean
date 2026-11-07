import Tools.ShippingFGCircuitS2mReach3
import Tools.ShippingFGCircuitS2sAdmLawsX
import Tools.ShippingFGCircuitS2sAdmS2hHist
import Tools.ShippingFGCircuitS2sAdmS2hHist2
import Tools.ShippingFGCircuitS2sAdmChildCacheA
import Tools.ShippingFGCircuitS2sAdmChildCanonKeyA
import Tools.ShippingFGCircuitS2sAdmChildComposeA
import Tools.ShippingFGCircuitS2sAdmChildComposeC
import Tools.ShippingFGCircuitS2sAdmChildCoreC
import Tools.ShippingFGCircuitS2sAdmChildDepthA
import Tools.ShippingFGCircuitS2sAdmChildDepthC
import Tools.ShippingFGCircuitS2sAdmChildFallbackA
import Tools.ShippingFGCircuitS2sAdmChildFrontA
import Tools.ShippingFGCircuitS2sAdmChildFrontCP
import Tools.ShippingFGCircuitS2sAdmChildInvA
import Tools.ShippingFGCircuitS2sAdmChildLegacyCachedA
import Tools.ShippingFGCircuitS2sAdmChildLegacyHandlersA
import Tools.ShippingFGCircuitS2sAdmChildLegacyHelpersA
import Tools.ShippingFGCircuitS2sAdmChildLegacyImplA
import Tools.ShippingFGCircuitS2sAdmChildLegacyTailA
import Tools.ShippingFGCircuitS2sAdmChildMainA
import Tools.ShippingFGCircuitS2sAdmChildPathA
import Tools.ShippingFGCircuitS2sAdmChildPinC
import Tools.ShippingFGCircuitS2sAdmChildProjFieldA
import Tools.ShippingFGCircuitS2sAdmChildRunA
import Tools.ShippingFGCircuitS2sAdmChildRunAKids
import Tools.ShippingFGCircuitS2sAdmChildRunAMain
import Tools.ShippingFGCircuitS2sAdmChildTeleCP
import Tools.ShippingFGCircuitS2sAdmChildTeleLocalA
import Tools.ShippingFGCircuitS2sAdmChildTeleMainA
import Tools.ShippingFGCircuitS2sAdmChildTranslateA
import Tools.ShippingFGCircuitS2sAdmChildTranslatePathA
import Tools.ShippingFGCircuitS2sAdmChildVCA
import Tools.ShippingFGCircuitS2sAdmChildVertA
import Tools.ShippingFGCircuitS2sAdmChildWalkA
import Tools.ShippingFGCircuitS2sAdmKWalk
import Tools.ShippingChildRunAKids
import Tools.ShippingChildComposeC
import Tools.ShippingFGCircuitS2sAdmChildPinC
import Tools.ShippingFGCircuitS2sAdmCallsGatePinned
import Tools.ShippingFGCircuitS2sAdmRunLocal
import Tools.ShippingFGCircuitS2sAdmLinked
import Tools.ShippingFGCircuitS2sAdmRunReads
import Tools.ShippingFGCircuitS2sAdmServedRealA
import Tools.ShippingFGCircuitS2sAdmParentRanA
import Tools.ShippingFGCircuitS2sAdmParentTailsA
import Tools.ShippingFGCircuitS2sAdmParentDesignA
import Tools.ShippingFGCircuitS2sAdmS1qLinked
import Tools.ShippingFGCircuitS2sAdmS1tFinal
import Tools.ShippingFGCircuitS2sAdmS1uSrc
import Tools.ShippingFGCircuitS2sAdmS1zClose
import Tools.ShippingFGCircuitS2sAdmS2dKids
import Tools.ShippingFGCircuitS2sAdmS2hHist3
import Tools.ShippingFGCircuitS2sAdmS2mReach
import Tools.ShippingFGCircuitS2sAdmS2mReach2
-- FG circuit pilot S2s4: SELECTIVE port of ShippingFGCircuitS2mReach3.lean onto the context-predicate bundles (only the declarations that mention RefLawsAOps/AdmCtx/Laws/... or an already-ported name; the rest is taken from the imported original); rename-only script scripts/s2s_port2.py (suffix X, `AdmCtx O.quiet` -> `O.adm`). No sorry/axiom/native_decide/TRUSTED/law.
set_option autoImplicit false
-- FG circuit pilot S2m (part 3): the steps of the main induction at `JQHR` (core chain, `synthesizeChild` miss/hit, `closeInstsM/GM`, the machine body) and `hftCoreCloses_of_kidsR`. Every step is the S2h theorem at the strengthened bundle `ropsR`; the miss premise is `missR`. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED, no new law. Results: docs/FG-CIRCUIT-PILOT.md §39.

namespace Tools.ShippingFGCircuitS2mReach
open Lean Meta Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingChildInv (endW Res)
open Tools.ShippingChildBndCore (cv sv dv)
open Tools.ShippingChildInvA
open Tools.ShippingChildFresh (MkRefd)
open Tools.ShippingChildVCA (JQ)
open Tools.ShippingGen5Env (ReadsAt readsAt_self)
open Tools.ShippingGen5EnvFrame3 (CellPrem)
open Tools.ShippingEntryReadsLinked (envAt CoreSaved)
open Tools.ShippingFGCircuitS2hHist
open Tools.ShippingFGCircuitS1oHead (GetEnvProfileAt)
open Tools.ShippingGen2 (LawsX StartX)
open Tools.ShippingFGCircuitS1qLinked (coreHeadOff)
open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData Tools.ShippingMachineCloses
open Tools.ShippingFGCircuitS2dKids Tools.ShippingMachineEntry Tools.ShippingEntrySoundness
open Tools.ShippingChildInv Tools.ShippingChildCacheA Tools.ShippingChildRunAKids Tools.ShippingChildRunAMain
open Tools.ShippingCallsShape Tools.ShippingCallsRun Tools.ShippingCallsAssembly Tools.ShippingGateChildComb
open Tools.ShippingChildBndInit Tools.ShippingChildBndCore Tools.ShippingMixedEntrySoundness
open Tools.ShippingChildFresh Tools.ShippingChildVCA Tools.ShippingChildComposeC

open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData Tools.ShippingMachineCloses
open Tools.ShippingMixedEntrySoundness
open Tools.ShippingCallsShape Tools.ShippingCallsRun Tools.ShippingCallsAssembly
open Tools.ShippingGateChildComb Tools.ShippingChildInv Tools.ShippingRankRun
open Tools.ShippingMachineChildComb Tools.ShippingTransitionClosed Tools.ShippingCallsGate
open Tools.ShippingChildInvA Tools.ShippingChildVCA Tools.ShippingChildCacheA Tools.ShippingChildFresh
open Tools.ShippingChildRunA Tools.ShippingChildRunAKids Tools.ShippingChildRunAMain Tools.ShippingChildComposeC
open Tools.ShippingGen2 Tools.ShippingChildBndCore Tools.ShippingFGCircuitS1qLinked Tools.ShippingFGCircuitS1qHead
open Tools.ShippingFGCircuitLinked
open Tools.ShippingFGCircuitS1iHead (HeadAt)
open Tools.ShippingFGCircuitS1oHead (GetEnvProfileAt headAt_of_profileOff)
open Tools.ShippingFGCircuitCover Tools.ShippingFGCircuitFinal4
open Tools.ShippingEntryReadsLinked (envAt)
open Tools.ShippingGen5Env (ReadsAt)
open Tools.ShippingGen5EnvFrame3 (CellPrem)
open Tools.ShippingFGCircuitS1hFrame (getEnvFrame_of_cellPrem)
open Tools.ShippingFGCircuitS2dKids
open Tools.ShippingFGCircuitS1kRoot Tools.ShippingFGCircuitS1kStmt Tools.ShippingFGCircuitS1zClose Tools.ShippingFGCircuitS2aClose
open Sparkle.IP.Net.HTTP Sparkle.IP.Bus.PCIe
open Tools.ShippingFGCircuitS2hHist

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

section Steps
variable {O : RefLawsAOpsX MkRefd mref cref} {hcell : CellPrem MkRefd mref cref} {e : Environment}
  {w₀ : Void IO.RealWorld} {hD : DRowEnvRX O e w₀} {hG : DiagEnvRX O e w₀}
include hcell hD hG

/-- **The machine body keeps `JQHRX`** (the `bodyStepH` of the strengthened bundle; the telescope rows are `hT`) -/
theorem jqhr_bodyStepX (hT : TeleRX O e w₀) :
    BodyStepHX (ropsRX O hcell e w₀ hD hG) (KidEv mref cref e) :=
  bodyStepH_of_teleX (ropsRX O hcell e w₀ hD hG) hT


/-- **`synthesizeChild` keeps `JQHRX` (miss and hit), at every depth `D ≥ 1`**: a hit takes the saved reads out of the entry; a miss gets them from `missRX` (the invariant itself) and saves them -/
theorem jqhr_childKeepsX (hT : TeleRX O e w₀) (h0 : ProfOffW mref cref w₀) (hs : ProfStepRX O w₀) :
    ∀ D, 1 ≤ D → ChildKeepsHX (ropsRX O hcell e w₀ hD hG) (KidEv mref cref e) D :=
  childKeepsH_all_of_teleX (ropsRX O hcell e w₀ hD hG) hT (missRX h0 hs)


/-- the child entry as a triple on every outcome: the result is a `RealChildEX` carrying its saved reads, and the world is again `JQHRX` -/
theorem jqhr_synthesizeChildX (hT : TeleRX O e w₀) (h0 : ProfOffW mref cref w₀) (hs : ProfStepRX O w₀)
    (hA : O.adm mctx cctx) {D : Nat} (hDpos : 1 ≤ D) (n : Name) :
    Triple mctx mref cctx cref (JQHRX O hcell e w₀ hD hG D) (synthesizeChild n)
      (fun r w => RealChildEX (ropsRX O hcell e w₀ hD hG) (KidEv mref cref e) n r ∧
        JQHRX O hcell e w₀ hD hG D w)
      (EQHX (ropsRX O hcell e w₀ hD hG) (KidEv mref cref e) D) :=
  synthesizeChild_tripleH'X (ropsRX O hcell e w₀ hD hG) hA hDpos (missRX h0 hs)
    (fun {tenv} hl b ci isInst =>
      jqhr_bodyStepX hT (D + 1) (by omega) (jqhr_childKeepsX hT h0 hs (D + 1) (by omega))
        mctx cctx hA n tenv b ci isInst)


/-- the one-output closing keeps `JQHRX`, whatever it returns -/
theorem jqhr_closeInstsMX (hT : TeleRX O e w₀) (h0 : ProfOffW mref cref w₀) (hs : ProfStepRX O w₀)
    (hA : O.adm mctx cctx) {D : Nat} (hDpos : 1 ≤ D)
    {shape : MachineShape} {t m₀ : Sparkle.IR.AST.Module} {d₀ : Sparkle.IR.AST.Design}
    {r : Option (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)} {w w' : Void IO.RealWorld}
    (hw : JQHRX O hcell e w₀ hD hG D w)
    (hr : RunsTo (closeInstsM shape t m₀ d₀) mctx mref cctx cref w r w') :
    ∃ children, r = Sparkle.IR.Machine.closeInsts (machNIn shape) shape.insts.length
        shape.layout.slots.length (t.inputs.map (·.name)) (shape.insts.map (·.2.1))
        children (m₀, d₀) ∧
      ChildrenRealEX (ropsRX O hcell e w₀ hD hG) (KidEv mref cref e) shape children ∧
      JQHRX O hcell e w₀ hD hG D w' :=
  closeInstsM_runHX (ropsRX O hcell e w₀ hD hG) (jqhr_bodyStepX hT) (missRX h0 hs) hA hDpos hw hr


/-- the general closing keeps `JQHRX`, whatever it returns -/
theorem jqhr_closeInstsGMX (hT : TeleRX O e w₀) (h0 : ProfOffW mref cref w₀) (hs : ProfStepRX O w₀)
    (hA : O.adm mctx cctx) {D : Nat} (hDpos : 1 ≤ D)
    {shape : MachineShape} {t m₀ : Sparkle.IR.AST.Module} {d₀ : Sparkle.IR.AST.Design}
    {r : Option (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)} {w w' : Void IO.RealWorld}
    (hw : JQHRX O hcell e w₀ hD hG D w)
    (hr : RunsTo (closeInstsGM shape t m₀ d₀) mctx mref cctx cref w r w') :
    ∃ children, r = Sparkle.IR.Machine.closeInstsG (machNIn shape) shape.insts.length
        shape.layout.slots.length (t.inputs.map (·.name)) (shape.insts.map (·.2.1))
        shape.instFields children (m₀, d₀) ∧ MemChildren shape children ∧
      ChildrenRealEX (ropsRX O hcell e w₀ hD hG) (KidEv mref cref e) shape children ∧
      JQHRX O hcell e w₀ hD hG D w' :=
  closeInstsGM_runHX (ropsRX O hcell e w₀ hD hG) (jqhr_bodyStepX hT) (missRX h0 hs) hA hDpos hw hr


/-- the core entry keeps `JQHRX` at every depth, on every outcome (the body premise of the core chain is `jqhr_bodyStepX`) -/
theorem jqhr_coreX (hT : TeleRX O e w₀) (h0 : ProfOffW mref cref w₀) (hs : ProfStepRX O w₀)
    (hA : O.adm mctx cctx) {D : Nat} (hDpos : 1 ≤ D) (c : Name) :
    Triple mctx mref cctx cref (JQHRX O hcell e w₀ hD hG D) (synthesizeCombinational c)
      (fun _ => JQHRX O hcell e w₀ hD hG D)
      (EQHX (ropsRX O hcell e w₀ hD hG) (KidEv mref cref e) D) :=
  hentryT_of_bodyHX (ropsRX O hcell e w₀ hD hG) hA
    (fun {tenv} hl b ci isInst =>
      jqhr_bodyStepX hT (D + 1) (by omega) (jqhr_childKeepsX hT h0 hs (D + 1) (by omega))
        mctx cctx hA c tenv b ci isInst)

end Steps


/-- **`hftCoreCloses_of_kidsHX` with the miss premise `MissEX` replaced by the reachability / environment invariant** `JQHRX` from the start world `w` of the target root run. Premise list, replacing `hmiss : MissEX L.O (KidEv mref cref (envAt cref w))`:
`hadm` (FG D.T-4m6: the root context is admissible for the strengthened quiet predicate), `hdown` (D.T-4m7), `hD` (D.T-4m1, class-D rows), `hG` (D.T-4m2, diagnostic rows), `hT` (D.T-4m3, telescope rows), `hs` (D.T-4m4, profile lookup along leaf steps), `h0` (D.T-4m5, profile lookup unset at the root start world). `L.T` is not used. -/
theorem hftCoreCloses_of_kidsRX (L : LawsX mref cref) {w : Void IO.RealWorld}
    (hstart : StartX L mctx cctx w) (hcell : CellPrem MkRefd mref cref) {lvl : Lean.Expr → Nat}
    (hrH : RootReader lvl (envAt cref w) hftHttp httpGetByte.machineData)
    (hrT : RootReader lvl (envAt cref w) hftTlp tlpCplByte.machineData)
    (hg : HftKidsGates (envAt cref w))
    (hadm : L.O.adm mctx cctx)
    (hD : DRowEnvRX L.O (envAt cref w) w)
    (hG : DiagEnvRX L.O (envAt cref w) w) (hT : TeleRX L.O (envAt cref w) w)
    (hs : ProfStepRX L.O w) (h0 : ProfOffW mref cref w) :
    HftCoreCloses mctx mref cctx cref w := by
  intro raw D₀ w1 hr s wh w2 w3 w4 envR ci hh hgetX henv hbody envR' w8 w10 r henv' hrun
  have hw1 := jqhr_headX (hcell := hcell) (hD := hD) (hG := hG) hadm hstart.2.1 hh
  have hw2 := triple_runsX (keeps_iff.mp (keepsA_framedX (ropsRX L.O hcell (envAt cref w) w hD hG) hadm
    (stableA_JQHX _ _ (0 + 1)) (FramedA.constInfo _))) hw1 hgetX
  have hw3 := triple_runsX (keeps_iff.mp (keepsA_framedX (ropsRX L.O hcell (envAt cref w) w hD hG) hadm
    (stableA_JQHX _ _ (0 + 1)) FramedA.env)) hw2 henv
  have hw8 := triple_runsX (keeps_iff.mp (keepsA_framedX (ropsRX L.O hcell (envAt cref w) w hD hG) hadm
    (stableA_JQHX _ _ (0 + 1)) FramedA.env)) hw3 henv'
  exact hft_closesAtHX (ropsRX L.O hcell (envAt cref w) w hD hG) hT hadm hcell hrH hrT hg
    (missRX h0 hs) false (0 + 1) w8 r w10 hw8 (by omega) hrun

end Tools.ShippingFGCircuitS2mReach

#print axioms Tools.ShippingFGCircuitS2mReach.jqhr_synthesizeChildX
#print axioms Tools.ShippingFGCircuitS2mReach.jqhr_closeInstsMX
#print axioms Tools.ShippingFGCircuitS2mReach.jqhr_closeInstsGMX
#print axioms Tools.ShippingFGCircuitS2mReach.jqhr_coreX
#print axioms Tools.ShippingFGCircuitS2mReach.hftCoreCloses_of_kidsRX

