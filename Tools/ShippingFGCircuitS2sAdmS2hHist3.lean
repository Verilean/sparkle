import Tools.ShippingFGCircuitS2hHist3
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
-- FG circuit pilot S2s4: SELECTIVE port of ShippingFGCircuitS2hHist3.lean onto the context-predicate bundles (only the declarations that mention RefLawsAOps/AdmCtx/Laws/... or an already-ported name; the rest is taken from the imported original); rename-only script scripts/s2s_port2.py (suffix X, `AdmCtx O.quiet` -> `O.adm`). No sorry/axiom/native_decide/TRUSTED/law.
set_option autoImplicit false
-- FG circuit pilot S2h (part 3): the root's children from the HISTORY — the consumers of `RealChildE` (the saved reads), the cache initialisation at the head of the root run, `hftCoreCloses_of_kidsH`, and the final statement whose children premise is the miss premise `MissE` (no universal `KidStartEnv`). No `sorry`, no `axiom`, no `native_decide`, no TRUSTED, no new law. Results: docs/FG-CIRCUIT-PILOT.md §34.

namespace Tools.ShippingFGCircuitS2hHist
open Lean Meta Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
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

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- `machineChild_of_realKX` for a HISTORY entry: the start-world evidence is the one saved in the entry (`RealChildEX.run … ev`), not a universal premise -/
theorem machineChild_of_realEX (O : RefLawsAOpsX MkRefd mref cref) (T : RefLawsATeleX O.quiet O.adm mref cref)
    (hcell : CellPrem MkRefd mref cref) {lvl : Lean.Expr → Nat} {e : Environment}
    {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hS : d.gateCallsOk nDecl = true) (hK : d.shape.layout.lets ≠ 0)
    (hno : d.shape.insts = []) (hsl : d.shape.layout.slots = [])
    (houts : ∃ o, d.shape.layout.outs = [o] ∧ o.name = "out")
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hRead : RootReader lvl e c d) (hgates : EntryGates e c)
    (closes : ∀ (mctx' : Meta.Context) (cctx' : Core.Context),
      MachineCloses mctx' mref cctx' cref c d.shape)
    {y : Res} (h : RealChildEX O (KidEv mref cref e) c y) :
    ChildIface c ((d.shape.binders.take nDecl).filter fun x => x.2 != .domain).length y.1 y.2 := by
  cases h with
  | run mctx' cctx' w w' adm cache synth quiet hr ev =>
    obtain ⟨hRA, hprof⟩ := ev
    exact machineChild_ifaceKX O T adm d ok hbody hS hK hno hsl houts outTy
      ⟨⟨quiet, synth, rfl⟩, fun c' r' h' => (cache c' r' h').toA⟩ hr
      (fun _ => machineDefinesLinked_of_readerE hRA (headAt_of_profileOff c hcell hprof)
        (getEnvFrame_of_cellPrem hcell) hRead hgates) (closes mctx' cctx')


theorem hft_kid_ifaceHX (O : RefLawsAOpsX MkRefd mref cref) (T : RefLawsATeleX O.quiet O.adm mref cref)
    (hcell : CellPrem MkRefd mref cref) {lvl : Lean.Expr → Nat} {e : Environment}
    (hrH : RootReader lvl e hftHttp httpGetByte.machineData) (hrT : RootReader lvl e hftTlp tlpCplByte.machineData)
    (hg : HftKidsGates e) {c : Name}
    (hc : c = ``Sparkle.IP.Net.HTTP.httpGetByte ∨ c = ``Sparkle.IP.Bus.PCIe.tlpCplByte) {y : Res}
    (h : RealChildEX O (KidEv mref cref e) c y) : ChildIface c (nkOf c) y.1 y.2 := by
  rcases hc with rfl | rfl
  · have := machineChild_of_realEX O T hcell (nDecl := httpGetByte.machineData.nIn) httpGetByte.machineData httpGetByte.machine_ok httpGetByte.machine_body
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ⟨_, rfl, rfl⟩ (by decide +kernel)
      hrH hg.1 (fun mc cc => httpGetByte.machine_closes mc _ cc _) h
    simpa [nkOf, hftHttp, hftTlp] using this
  · have := machineChild_of_realEX O T hcell (nDecl := tlpCplByte.machineData.nIn) tlpCplByte.machineData tlpCplByte.machine_ok tlpCplByte.machine_body
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ⟨_, rfl, rfl⟩ (by decide +kernel)
      hrT hg.2 (fun mc cc => tlpCplByte.machine_closes mc _ cc _) h
    simpa [nkOf, hftHttp, hftTlp] using this


theorem hft_closesAtHX (O : RefLawsAOpsX MkRefd mref cref) (T : RefLawsATeleX O.quiet O.adm mref cref)
    (hA : O.adm mctx cctx) (hcell : CellPrem MkRefd mref cref) {lvl : Lean.Expr → Nat} {e : Environment}
    (hrH : RootReader lvl e hftHttp httpGetByte.machineData) (hrT : RootReader lvl e hftTlp tlpCplByte.machineData)
    (hg : HftKidsGates e) (hmiss : MissEX O (KidEv mref cref e)) :
    MachineClosesAtHX (mref := mref) (cref := cref) O (KidEv mref cref e) mctx cctx hftRoot synth_hftPcieOutByte.machineData.shape :=
  machineClosesAtH_of_gateKidsX O T hmiss hA synth_hftPcieOutByte.machineData
    synth_hftPcieOutByte.machine_ok synth_hftPcieOutByte.machine_body hft_alias hft_gateCalls
    (fun k => nkOf ((synth_hftPcieOutByte.machineData.shape.insts[k]?.map (·.1)).getD Name.anonymous))
    (fun x hx => (hft_nomem x hx).1)
    (fun k hk' y h => by
      have hmem := hft_kids_names _ (List.getElem_mem hk')
      have := hft_kid_ifaceHX O T hcell hrH hrT hg hmem h
      simpa [List.getElem?_eq_getElem hk'] using this)
    (fun k hk' => by
      have := hft_argsN _ (List.getElem_mem hk')
      simpa [List.getElem?_eq_getElem hk'] using this)
    (Tools.ShippingNameDischarge.names_inj _) hft_nodup
    (Tools.ShippingNameDischarge.parent_ne _ _ hft_noparent)
    (fun k _ o ho => Tools.ShippingCallsGate.instName_ne_of_head (hft_outs_head o ho) k _)

open Tools.ShippingChildDepthC Tools.ShippingChildCoreC Tools.ShippingChildVertA in

/-- **Cache initialisation at the head of the root run** (the depth-0 branch of `coreHeadOff_jqcAX`): the head clears the cache, so the history invariant holds at its end world for ANY evidence predicate -/
theorem coreHeadOff_jqhAX (O : RefLawsAOpsX MkRefd mref cref) (hA : O.adm mctx cctx) {E : StartEv} {X : Name}
    {w w1 : Void IO.RealWorld} {s : Tools.ShippingEntryReadsLinked.CoreSaved}
    (hw : JQ O.quiet 0 w)
    (hh : RunsTo (coreHeadOff X) mctx mref cctx cref w s w1) :
    JQHX O E (0 + 1) w1 := by
  have h := hh
  unfold coreHeadOff at h
  obtain ⟨d, wc, s3, h⟩ := RunsTo.bind h
  have hd := triple_runsX (tripleA_depthGetX O hA (stableA_JQ _ 0)) hw s3
  have hdD : d = 0 := hd.2.trans hd.1.2.2
  have hw := hd.1
  subst hdD
  rcases RunsTo.ite h with h | h
  · obtain ⟨_, _, ht, _⟩ := RunsTo.bind h
    exact (throwError_not_runs _ ht).elim
  simp only [↓reduceIte, beq_self_eq_true] at h
  peelPX h; peelPX h; peelPX h; peelPX h; peelPX h; peelPX h; peelPX h
  peelFX O hA (stableA_JQ _ 0) h hw; peelFX O hA (stableA_JQ _ 0) h hw
  peelFX O hA (stableA_JQ _ 0) h hw; peelFX O hA (stableA_JQ _ 0) h hw
  obtain ⟨_, _, step, h⟩ := RunsTo.bind h
  have hw := triple_runsX (tripleH_clearX (E := E) O hA 0 (R := fun _ _ => False)) hw step
  clear step
  peelFX O hA (stableA_JQHX O E 0) h hw; peelFX O hA (stableA_JQHX O E 0) h hw
  peelFX O hA (stableA_JQHX O E 0) h hw; peelFX O hA (stableA_JQHX O E 0) h hw
  peelFX O hA (stableA_JQHX O E 0) h hw; peelFX O hA (stableA_JQHX O E 0) h hw
  peelFX O hA (stableA_JQHX O E 0) h hw
  obtain ⟨_, _, step, h⟩ := RunsTo.bind h
  have hw := triple_runsX (tripleH_depthSetX O hA 0 (0 + 1) (R := fun _ _ => False)) hw step
  clear step
  obtain ⟨-, rfl⟩ := RunsTo.pure_world h
  exact hw


/-- `hftCoreCloses_of_kidsKX` with the universal `hkenv` replaced by the miss premise on the HISTORY (`hmiss`) -/
theorem hftCoreCloses_of_kidsHX (L : LawsX mref cref) {w : Void IO.RealWorld}
    (hstart : StartX L mctx cctx w) (hcell : CellPrem MkRefd mref cref) {lvl : Lean.Expr → Nat}
    (hrH : RootReader lvl (envAt cref w) hftHttp httpGetByte.machineData)
    (hrT : RootReader lvl (envAt cref w) hftTlp tlpCplByte.machineData)
    (hg : HftKidsGates (envAt cref w)) (hmiss : MissEX L.O (KidEv mref cref (envAt cref w))) :
    HftCoreCloses mctx mref cctx cref w := by
  intro raw D₀ w1 hr s wh w2 w3 w4 envR ci hh hgetX henv hbody envR' w8 w10 r henv' hrun
  have hw1 := coreHeadOff_jqhAX (E := KidEv mref cref (envAt cref w)) L.O hstart.1 hstart.2.1 hh
  have hw2 := triple_runsX (keeps_iff.mp (keepsA_framedX L.O hstart.1 (stableA_JQHX L.O _ (0 + 1)) (FramedA.constInfo _))) hw1 hgetX
  have hw3 := triple_runsX (keeps_iff.mp (keepsA_framedX L.O hstart.1 (stableA_JQHX L.O _ (0 + 1)) FramedA.env)) hw2 henv
  have hw8 := triple_runsX (keeps_iff.mp (keepsA_framedX L.O hstart.1 (stableA_JQHX L.O _ (0 + 1)) FramedA.env)) hw3 henv'
  exact hft_closesAtHX L.O L.T hstart.1 hcell hrH hrT hg hmiss false (0 + 1) w8 r w10 hw8 (by omega) hrun

/-! ## the final statement: `hkenv` replaced by the miss premise on the history -/
section Final

open Lean Sparkle.Compiler.Elab Sparkle.Core Sparkle.Core.Domain Tools.ShippingGen2 Tools.ShippingGen5DeclConnect Tools.ShippingGen5FG
open Tools.ShippingFGCircuit Tools.ShippingFGCircuitRoots Tools.ShippingFGCircuitArtifact Tools.ShippingFGCircuitCover Tools.ShippingFGCircuitBridge
open Tools.ShippingGenFGLedgerPremises Tools.ShippingFGCircuitS1iEnv
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingFGCircuitS1kPkg
open Tools.ShippingFGCircuitS1qEndpoint
open Tools.ShippingFGCircuitS1mCD Tools.ShippingFGCircuitS1pCD Tools.ShippingFGCircuitS1rCD
open Tools.ShippingFGCircuitS1tFinal Tools.ShippingFGCircuitS1uSrc Tools.ShippingFGCircuitS1xNoRaw
open Tools.ShippingFGCircuitRunLocal


/-- `HftFinalStmtOffLNKKX` (S2d) with `hkenv : HftKidsStartEnvX L.O (envAt cref w)` (the universal `KidStartEnvX`) replaced by `hmiss : MissEX L.O (KidEv mref cref (envAt cref w))` (FG D.T-4h, the miss premise on the history: asked only where a child run is created, in worlds whose cache entries all carry their own saved reads); `hkgates` is unchanged (14 explicit hypotheses) -/
def HftFinalStmtOffLNKHX (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ∀ (hlink : HftRootLink) {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : LawsX mref cref) (lvl : Lean.Expr → Nat) (env₀ : Environment)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (hstart : StartX L mctx cctx w)
    (hr : RunsTo (synthesizeCombinationalOff hftRoot) mctx mref cctx cref w (b, D') w')
    (hcell : CellPrem Tools.ShippingChildFresh.MkRefd mref cref)
    (hchk : CheckedStart lvl env₀ cref w hftRoot hftRootType hftRootValue synth_hftPcieOutByte.machineData)
    (hreadH : RootReader lvl (envAt cref w) hftHttp Sparkle.IP.Net.HTTP.httpGetByte.machineData)
    (hreadT : RootReader lvl (envAt cref w) hftTlp Sparkle.IP.Bus.PCIe.tlpCplByte.machineData)
    (hcd : Ob (envAt cref w))
    (htop : ∀ p : Pkg ι (fun _ => defaultDomain), GPt (ι := ι) lvl (envAt cref w) hftRoot = some p → HftObTopCoreOff mctx mref cctx cref w b D' p)
    (hmiss : MissEX L.O (KidEv mref cref (envAt cref w)))
    (hkgates : HftKidsGates (envAt cref w)),
    (∃ raw, PostRunOff mctx mref cctx cref w hftRoot D' b raw) ∧
    ∃ (mm : MonoTy shHft) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMonoV CV (envAt cref w) (GPt (ι := ι) lvl (envAt cref w))
        (PostRunOff mctx mref cctx cref w hftRoot D') hftRoot shHft mm b D' p


theorem synth_hftPcieOutByte_finalOffLNKHX (CV : CDRel) (Ob : Environment → Prop) (hOb : ∀ env, Ob env → HftObOf CV env) :
    HftFinalStmtOffLNKHX Ob CV := by
  intro hlink ι mref cref L lvl env₀ mctx cctx w w' b D' hstart hr hcell hchk hRdH hRdT hCD hTop hmiss hkgates
  exact synth_hftPcieOutByte_finalOffLNLX CV Ob hOb hlink L lvl env₀ hstart hr hcell hchk hRdH hRdT hCD hTop
    (hftCoreCloses_of_kidsHX L hstart hcell hRdH hRdT hkgates hmiss)


theorem synth_hftPcieOutByte_finalOffLNKH_ZX : HftFinalStmtOffLNKHX HftObCDZ cdvZ := synth_hftPcieOutByte_finalOffLNKHX cdvZ _ (fun _ h => h)

theorem synth_hftPcieOutByte_finalOffLNKH_YX : HftFinalStmtOffLNKHX HftObCDY cdvY := synth_hftPcieOutByte_finalOffLNKHX cdvY _ (fun _ h => h)

theorem synth_hftPcieOutByte_finalOffLNKH_XX : HftFinalStmtOffLNKHX HftObCDX cdvX := synth_hftPcieOutByte_finalOffLNKHX cdvX _ (fun _ h => h)

end Final

end Tools.ShippingFGCircuitS2hHist

#print axioms Tools.ShippingFGCircuitS2hHist.machineChild_of_realEX
#print axioms Tools.ShippingFGCircuitS2hHist.coreHeadOff_jqhAX
#print axioms Tools.ShippingFGCircuitS2hHist.hftCoreCloses_of_kidsHX
#print axioms Tools.ShippingFGCircuitS2hHist.synth_hftPcieOutByte_finalOffLNKH_ZX

