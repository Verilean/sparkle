import Tools.ShippingFGCircuitS2hHist2
import Tools.ShippingFGCircuitS2dKids
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

/-- **The evidence a child run saves** (what `KidStartEnv` asked of EVERY admissible start world): the Core environment the start world reads agrees with `e` (`ReadsAt e cref w`), and the profile lookup from it is the profile-off branch (`GetEnvProfileAt`, which `synthesizeCombinational`'s `coreHead` passes — it is not the diagnostic entry). Here it is a field of one history entry. -/
def KidEv (mref : ST.Ref IO.RealWorld Meta.State) (cref : ST.Ref IO.RealWorld Core.State) (e : Environment) : StartEv :=
  fun mctx cctx w => ReadsAt e cref w ∧ GetEnvProfileAt mctx mref cctx cref w

/-- `machineChild_of_realK` for a HISTORY entry: the start-world evidence is the one saved in the entry (`RealChildE.run … ev`), not a universal premise -/
theorem machineChild_of_realE (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
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
    {y : Res} (h : RealChildE O (KidEv mref cref e) c y) :
    ChildIface c ((d.shape.binders.take nDecl).filter fun x => x.2 != .domain).length y.1 y.2 := by
  cases h with
  | run mctx' cctx' w w' adm cache synth quiet hr ev =>
    obtain ⟨hRA, hprof⟩ := ev
    exact machineChild_ifaceK O T adm d ok hbody hS hK hno hsl houts outTy
      ⟨⟨quiet, synth, rfl⟩, fun c' r' h' => (cache c' r' h').toA⟩ hr
      (fun _ => machineDefinesLinked_of_readerE hRA (headAt_of_profileOff c hcell hprof)
        (getEnvFrame_of_cellPrem hcell) hRead hgates) (closes mctx' cctx')

theorem hft_kid_ifaceH (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hcell : CellPrem MkRefd mref cref) {lvl : Lean.Expr → Nat} {e : Environment}
    (hrH : RootReader lvl e hftHttp httpGetByte.machineData) (hrT : RootReader lvl e hftTlp tlpCplByte.machineData)
    (hg : HftKidsGates e) {c : Name}
    (hc : c = ``Sparkle.IP.Net.HTTP.httpGetByte ∨ c = ``Sparkle.IP.Bus.PCIe.tlpCplByte) {y : Res}
    (h : RealChildE O (KidEv mref cref e) c y) : ChildIface c (nkOf c) y.1 y.2 := by
  rcases hc with rfl | rfl
  · have := machineChild_of_realE O T hcell (nDecl := httpGetByte.machineData.nIn) httpGetByte.machineData httpGetByte.machine_ok httpGetByte.machine_body
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ⟨_, rfl, rfl⟩ (by decide +kernel)
      hrH hg.1 (fun mc cc => httpGetByte.machine_closes mc _ cc _) h
    simpa [nkOf, hftHttp, hftTlp] using this
  · have := machineChild_of_realE O T hcell (nDecl := tlpCplByte.machineData.nIn) tlpCplByte.machineData tlpCplByte.machine_ok tlpCplByte.machine_body
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ⟨_, rfl, rfl⟩ (by decide +kernel)
      hrT hg.2 (fun mc cc => tlpCplByte.machine_closes mc _ cc _) h
    simpa [nkOf, hftHttp, hftTlp] using this

theorem hft_nodup : (synth_hftPcieOutByte.machineData.shape.insts.map (·.1)).Nodup := by decide +kernel

theorem hft_closesAtH (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx) (hcell : CellPrem MkRefd mref cref) {lvl : Lean.Expr → Nat} {e : Environment}
    (hrH : RootReader lvl e hftHttp httpGetByte.machineData) (hrT : RootReader lvl e hftTlp tlpCplByte.machineData)
    (hg : HftKidsGates e) (hmiss : MissE O (KidEv mref cref e)) :
    MachineClosesAtH (mref := mref) (cref := cref) O (KidEv mref cref e) mctx cctx hftRoot synth_hftPcieOutByte.machineData.shape :=
  machineClosesAtH_of_gateKids O T hmiss hA synth_hftPcieOutByte.machineData
    synth_hftPcieOutByte.machine_ok synth_hftPcieOutByte.machine_body hft_alias hft_gateCalls
    (fun k => nkOf ((synth_hftPcieOutByte.machineData.shape.insts[k]?.map (·.1)).getD Name.anonymous))
    (fun x hx => (hft_nomem x hx).1)
    (fun k hk' y h => by
      have hmem := hft_kids_names _ (List.getElem_mem hk')
      have := hft_kid_ifaceH O T hcell hrH hrT hg hmem h
      simpa [List.getElem?_eq_getElem hk'] using this)
    (fun k hk' => by
      have := hft_argsN _ (List.getElem_mem hk')
      simpa [List.getElem?_eq_getElem hk'] using this)
    (Tools.ShippingNameDischarge.names_inj _) hft_nodup
    (Tools.ShippingNameDischarge.parent_ne _ _ hft_noparent)
    (fun k _ o ho => Tools.ShippingCallsGate.instName_ne_of_head (hft_outs_head o ho) k _)

open Tools.ShippingChildDepthC Tools.ShippingChildCoreC Tools.ShippingChildVertA in
/-- **Cache initialisation at the head of the root run** (the depth-0 branch of `coreHeadOff_jqcA`): the head clears the cache, so the history invariant holds at its end world for ANY evidence predicate -/
theorem coreHeadOff_jqhA (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx) {E : StartEv} {X : Name}
    {w w1 : Void IO.RealWorld} {s : Tools.ShippingEntryReadsLinked.CoreSaved}
    (hw : JQ O.quiet 0 w)
    (hh : RunsTo (coreHeadOff X) mctx mref cctx cref w s w1) :
    JQH O E (0 + 1) w1 := by
  have h := hh
  unfold coreHeadOff at h
  obtain ⟨d, wc, s3, h⟩ := RunsTo.bind h
  have hd := triple_runs (tripleA_depthGet O hA (stableA_JQ _ 0)) hw s3
  have hdD : d = 0 := hd.2.trans hd.1.2.2
  have hw := hd.1
  subst hdD
  rcases RunsTo.ite h with h | h
  · obtain ⟨_, _, ht, _⟩ := RunsTo.bind h
    exact (throwError_not_runs _ ht).elim
  simp only [↓reduceIte, beq_self_eq_true] at h
  peelP h; peelP h; peelP h; peelP h; peelP h; peelP h; peelP h
  peelF O hA (stableA_JQ _ 0) h hw; peelF O hA (stableA_JQ _ 0) h hw
  peelF O hA (stableA_JQ _ 0) h hw; peelF O hA (stableA_JQ _ 0) h hw
  obtain ⟨_, _, step, h⟩ := RunsTo.bind h
  have hw := triple_runs (tripleH_clear (E := E) O hA 0 (R := fun _ _ => False)) hw step
  clear step
  peelF O hA (stableA_JQH O E 0) h hw; peelF O hA (stableA_JQH O E 0) h hw
  peelF O hA (stableA_JQH O E 0) h hw; peelF O hA (stableA_JQH O E 0) h hw
  peelF O hA (stableA_JQH O E 0) h hw; peelF O hA (stableA_JQH O E 0) h hw
  peelF O hA (stableA_JQH O E 0) h hw
  obtain ⟨_, _, step, h⟩ := RunsTo.bind h
  have hw := triple_runs (tripleH_depthSet O hA 0 (0 + 1) (R := fun _ _ => False)) hw step
  clear step
  obtain ⟨-, rfl⟩ := RunsTo.pure_world h
  exact hw

/-- `hftCoreCloses_of_kidsK` with the universal `hkenv` replaced by the miss premise on the HISTORY (`hmiss`) -/
theorem hftCoreCloses_of_kidsH (L : Laws mref cref) {w : Void IO.RealWorld}
    (hstart : Start L mctx cctx w) (hcell : CellPrem MkRefd mref cref) {lvl : Lean.Expr → Nat}
    (hrH : RootReader lvl (envAt cref w) hftHttp httpGetByte.machineData)
    (hrT : RootReader lvl (envAt cref w) hftTlp tlpCplByte.machineData)
    (hg : HftKidsGates (envAt cref w)) (hmiss : MissE L.O (KidEv mref cref (envAt cref w))) :
    HftCoreCloses mctx mref cctx cref w := by
  intro raw D₀ w1 hr s wh w2 w3 w4 envR ci hh hget henv hbody envR' w8 w10 r henv' hrun
  have hw1 := coreHeadOff_jqhA (E := KidEv mref cref (envAt cref w)) L.O hstart.1 hstart.2.1 hh
  have hw2 := triple_runs (keeps_iff.mp (keepsA_framed L.O hstart.1 (stableA_JQH L.O _ (0 + 1)) (FramedA.constInfo _))) hw1 hget
  have hw3 := triple_runs (keeps_iff.mp (keepsA_framed L.O hstart.1 (stableA_JQH L.O _ (0 + 1)) FramedA.env)) hw2 henv
  have hw8 := triple_runs (keeps_iff.mp (keepsA_framed L.O hstart.1 (stableA_JQH L.O _ (0 + 1)) FramedA.env)) hw3 henv'
  exact hft_closesAtH L.O L.T hstart.1 hcell hrH hrT hg hmiss false (0 + 1) w8 r w10 hw8 (by omega) hrun

end Tools.ShippingFGCircuitS2hHist

#print axioms Tools.ShippingFGCircuitS2hHist.machineChild_of_realE
#print axioms Tools.ShippingFGCircuitS2hHist.coreHeadOff_jqhA
#print axioms Tools.ShippingFGCircuitS2hHist.hftCoreCloses_of_kidsH
