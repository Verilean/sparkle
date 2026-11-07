import Tools.ShippingFGCircuitS2dKids
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
-- FG circuit pilot S2s4: SELECTIVE port of ShippingFGCircuitS2dKids.lean onto the context-predicate bundles (only the declarations that mention RefLawsAOps/AdmCtx/Laws/... or an already-ported name; the rest is taken from the imported original); rename-only script scripts/s2s_port2.py (suffix X, `AdmCtx O.quiet` -> `O.adm`). No sorry/axiom/native_decide/TRUSTED/law.
set_option autoImplicit false
-- FG circuit pilot S2d: the children's reflection (`HftKidsDefine`) narrowed run-locally. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED, no new law. Results: docs/FG-CIRCUIT-PILOT.md §32.

namespace Tools.ShippingFGCircuitS2dKids
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

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 2000000 in
/-- **`machineChild_ifaceA` with the all-world `MachineDefines` replaced by the run-local linked boundary** (the machine run is taken by `machine_run_of_coreCX` on the run's own core chain; `entry` is asked only of THIS child run's core run, at its start world `w`) ( `synthesizeMachineCertified_runsAX`; the rest of the proof is the old one) -/
theorem machineChild_ifaceKX (O : RefLawsAOpsX MkRefd mref cref) (T : RefLawsATeleX O.quiet O.adm mref cref)
    (hA : O.adm mctx cctx) {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hS : d.gateCallsOk nDecl = true) (hK : d.shape.layout.lets ≠ 0)
    (hno : d.shape.insts = []) (hsl : d.shape.layout.slots = [])
    (houts : ∃ o, d.shape.layout.outs = [o] ∧ o.name = "out")
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Design}
    (hw : JQCX O (dv w) w)
    (hr : RunsTo (synthesizeCombinational c) mctx mref cctx cref w (b, design) w')
    (entry : ∀ {M : Sparkle.IR.AST.Module} {D : Design} {w1 : Void IO.RealWorld},
      RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1 →
      MachineDefinesLinked mctx mref cctx cref c d.shape w M D w1)
    (closes : MachineCloses mctx mref cctx cref c d.shape) :
    ChildComb b ∧
      b.inputs.length = ((d.shape.binders.take nDecl).filter fun x => x.2 != .domain).length ∧
      b.name = (Sparkle.IR.ModuleName.ofDecl c) ∧ design.modules = [] := by
  obtain ⟨M, D, w1, hcore, hpost, hdesM⟩ := synthesizeCombinational_parts hr
  obtain ⟨tenv, bb, r, w9, w10, hrun9, hw9, hres⟩ :=
    machine_run_of_coreCX O hA hcore (entry hcore) hw.1 (Or.inr hw.2)
  have hne := closes (profLogIO bb) w9 r w10 hrun9
  cases r with
  | none => exact absurd rfl hne
  | some res =>
  have hres' := hres res rfl
  subst hres'
  obtain ⟨t, t', d₀, run, hcl, hmt⟩ :=
    synthesizeMachineCertified_runsAX O (bodyStepC_of_teleX O T) hA (htr_of_teleX O hA T (dv w) tenv) hw9 hrun9
  rcases hmt with ⟨-, hMeq, hDeq⟩ | ⟨hne', -⟩
  rotate_left
  · exact absurd hno hne'
  simp only [MachineData.gateCallsOk, MachineData.callsOk, Bool.and_eq_true, decide_eq_true_eq,
    List.isEmpty_iff] at hS
  obtain ⟨⟨⟨⟨⟨⟨hnIn, hargs⟩, hfields⟩, hcoreR⟩, hslots⟩, hdomB⟩, -⟩ := hS
  simp only [MachineData.ok, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at ok
  obtain ⟨hlen, hlets, positive, _, _, _, outsOk, outsNodup, hwf, hb, hv,
    _, _, hscoped, _, _, _, _, _, _, _, _⟩ := ok
  obtain ⟨hfitL, -⟩ := scoped_fit d.letBs d.letFields _ hscoped
  have hlsLen : d.letFields.length = d.ls.length := by simp [MachineData.letFields]
  have hletBs : d.letBs.length = d.shape.binders.length - (d.nIn + d.ss.length) := by
    simp [MachineData.letBs]
  have hposv : PositiveBinders d.shape.binders := by
    intro name n hmem
    have := List.all_eq_true.mp positive _ hmem
    simpa using this
  have hb' : ∀ j, j < d.kb → ∃ name, d.shape.binders[d.bpos j]? = some (name, .bool) := by
    intro j hj
    have := hb j hj
    cases h : d.shape.binders[d.bpos j]? with
    | none => rw [h] at this; cases this
    | some b =>
      obtain ⟨name, k⟩ := b
      rw [h] at this
      simp only [Option.map_some, Option.some.injEq] at this
      exact ⟨name, by rw [← this]⟩
  have hv' : ∀ j, j < d.kv → ∃ name, d.shape.binders[d.vpos j]? = some (name, .bits (d.vw j)) := by
    intro j hj
    have := hv j hj
    cases h : d.shape.binders[d.vpos j]? with
    | none => rw [h] at this; cases this
    | some b =>
      obtain ⟨name, k⟩ := b
      rw [h] at this
      simp only [Option.map_some, Option.some.injEq] at this
      exact ⟨name, by rw [← this]⟩
  obtain ⟨ids, cache, returned, st, nd, len, hrun, hm, hD, nameLegal⟩ :=
    synthesizeMixedCertified_returns run
  have hA : (d.shape.binders.take nDecl).length = nDecl := by
    rw [List.length_take]
    omega
  have hsplit : d.shape.binders = d.shape.binders.take nDecl ++ d.shape.binders.drop nDecl :=
    (List.take_append_drop ..).symm
  have hKne : d.letBs.length ≠ 0 := by rw [← hlets]; exact hK
  have hBlen : (d.shape.binders.drop nDecl).length =
      d.shape.insts.length + d.ss.length + d.letBs.length := by
    rw [List.length_drop]
    omega
  have hcoreWF := core_wf d.core.2 d.letFields hwf
  obtain ⟨PI, ls, bodyB, w, P, bnd, hin, hPI, hlsL, hndI, hinW, hwAlloc, hbodyT, hacy, hnamed, hnw,
      hP, hF, hdes, hname⟩ :=
    transition_calls_facts (cs := d.callBounds) nd len hrun hm nameLegal hposv d.letFields d.core.2
      hwf hb' hv' hbody hsplit hdomB hBlen hfitL
      (by rw [hA]; exact fieldsOK_of_B d.letFields 0 d.core.2 hfields hwf)
      (by
        rw [hA, hlsLen]
        exact uses_of_reads (fun j hj hr => ⟨hj, posOk_rule hr⟩)
          (fun j hj hr => ⟨hj, posOk_rule hr⟩) d.core.2 hcoreWF hcoreR)
  obtain ⟨hclosedT, -, ⟨ow, pb⟩, ready, -, -⟩ :=
    transition_closed nd len hrun hm nameLegal hposv d.packed hwf hb' hv' hbody
  rw [hlets] at hcl
  have hss : d.ss.length = 0 := by rw [hslots, hsl]; rfl
  have h0 : d.shape.insts.length + d.ss.length = 0 := by rw [hno, hss]; rfl
  obtain ⟨hC, hI, hN⟩ := slotless_childComb_full (b := b) hKne hcl hin (by rw [hlsL, h0]; omega)
    hndI hinW hwAlloc hbodyT hacy hnamed
    (fun al core h => by
      obtain ⟨es, ws, hf, hal, hc⟩ := hF al core h
      rw [h0, List.drop_zero] at hal
      exact ⟨es, ws, hf, hal, hc⟩)
    hclosedT ready.typed ready.wiresNodup pb.wires outsOk outTy hsl houts (hMeq ▸ hpost)
  exact ⟨hC, by rw [hI, hPI], by rw [hN, hname], hdesM (by rw [hDeq, hD, hdes]; rfl)⟩



/-! ## the run-local supply: the linked boundary of ONE child run from the reader, the gates and the start environment of that run -/


/-- **`KidStartEnvX`** (NAMED HYPOTHESIS; FG D.T-4, the children's part, row `D.T-4k`): for EVERY run of the child `c`'s full entry in a `RealChildAX`-admissible start world `w` (the fields of `RealChildAX.run`: admissible contexts, cache invariant, the synthesis ref, quiet), (A) the Core environment that world reads agrees with `e` (`ReadsAt e cref w`), and (B) the profile lookup `IO.getEnv "SPARKLE_PROFILE"` from `w` returns `none` and keeps the Core environment (`GetEnvProfileAt`, the profile-off branch as for the root). It replaces the all-world `MachineDefines c shape` by two environment-frame facts at the child's own start world; no shape or gate content, no closing fact. -/
def KidStartEnvX (O : RefLawsAOpsX MkRefd mref cref) (e : Environment) (c : Name) : Prop :=
  ∀ (mctx' : Meta.Context) (cctx' : Core.Context) (w w' : Void IO.RealWorld) (y : Res),
    O.adm mctx' cctx' → (∀ c' r', (cv w).get? c' = some r' → RealChildAX O c' r') →
    sv w = some synthesizeChild → O.quiet w →
    RunsTo (synthesizeCombinational c) mctx' mref cctx' cref w y w' →
    ReadsAt e cref w ∧ GetEnvProfileAt mctx' mref cctx' cref w


/-- `machineChild_of_realA` with `MachineDefines` replaced by `KidStartEnvX` + the reader + the gates -/
theorem machineChild_of_realKX (O : RefLawsAOpsX MkRefd mref cref) (T : RefLawsATeleX O.quiet O.adm mref cref)
    (hcell : CellPrem MkRefd mref cref) {lvl : Lean.Expr → Nat} {e : Environment}
    {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hS : d.gateCallsOk nDecl = true) (hK : d.shape.layout.lets ≠ 0)
    (hno : d.shape.insts = []) (hsl : d.shape.layout.slots = [])
    (houts : ∃ o, d.shape.layout.outs = [o] ∧ o.name = "out")
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hRead : RootReader lvl e c d) (hgates : EntryGates e c) (hk : KidStartEnvX O e c)
    (closes : ∀ (mctx' : Meta.Context) (cctx' : Core.Context),
      MachineCloses mctx' mref cctx' cref c d.shape)
    {y : Res} (h : RealChildAX O c y) :
    ChildIface c ((d.shape.binders.take nDecl).filter fun x => x.2 != .domain).length y.1 y.2 := by
  cases h with
  | run mctx' cctx' w w' adm cache synth quiet hr =>
    obtain ⟨hRA, hprof⟩ := hk mctx' cctx' w w' _ adm cache synth quiet hr
    exact machineChild_ifaceKX O T adm d ok hbody hS hK hno hsl houts outTy ⟨⟨quiet, synth, rfl⟩, cache⟩ hr
      (fun _ => machineDefinesLinked_of_readerE hRA (headAt_of_profileOff c hcell hprof)
        (getEnvFrame_of_cellPrem hcell) hRead hgates) (closes mctx' cctx')

/-! ## the root: both calls -/
open Tools.ShippingFGCircuitS1kRoot Tools.ShippingFGCircuitS1kStmt Tools.ShippingFGCircuitS1zClose Tools.ShippingFGCircuitS2aClose
open Sparkle.IP.Net.HTTP Sparkle.IP.Bus.PCIe


/-- `KidStartEnvX` for both called declarations (NAMED HYPOTHESIS, FG D.T-4k) -/
def HftKidsStartEnvX (O : RefLawsAOpsX MkRefd mref cref) (e : Environment) : Prop :=
  KidStartEnvX O e hftHttp ∧ KidStartEnvX O e hftTlp


theorem hft_kid_ifaceKX (O : RefLawsAOpsX MkRefd mref cref) (T : RefLawsATeleX O.quiet O.adm mref cref)
    (hcell : CellPrem MkRefd mref cref) {lvl : Lean.Expr → Nat} {e : Environment}
    (hrH : RootReader lvl e hftHttp httpGetByte.machineData) (hrT : RootReader lvl e hftTlp tlpCplByte.machineData)
    (hg : HftKidsGates e) (hke : HftKidsStartEnvX O e) {c : Name}
    (hc : c = ``Sparkle.IP.Net.HTTP.httpGetByte ∨ c = ``Sparkle.IP.Bus.PCIe.tlpCplByte) {y : Res}
    (h : RealChildAX O c y) : ChildIface c (nkOf c) y.1 y.2 := by
  rcases hc with rfl | rfl
  · have := machineChild_of_realKX O T hcell (nDecl := httpGetByte.machineData.nIn) httpGetByte.machineData httpGetByte.machine_ok httpGetByte.machine_body
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ⟨_, rfl, rfl⟩ (by decide +kernel)
      hrH hg.1 hke.1 (fun mc cc => httpGetByte.machine_closes mc _ cc _) h
    simpa [nkOf, hftHttp, hftTlp] using this
  · have := machineChild_of_realKX O T hcell (nDecl := tlpCplByte.machineData.nIn) tlpCplByte.machineData tlpCplByte.machine_ok tlpCplByte.machine_body
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ⟨_, rfl, rfl⟩ (by decide +kernel)
      hrT hg.2 hke.2 (fun mc cc => tlpCplByte.machine_closes mc _ cc _) h
    simpa [nkOf, hftHttp, hftTlp] using this


theorem hft_closesAtKX (O : RefLawsAOpsX MkRefd mref cref) (T : RefLawsATeleX O.quiet O.adm mref cref)
    (hA : O.adm mctx cctx) (hcell : CellPrem MkRefd mref cref) {lvl : Lean.Expr → Nat} {e : Environment}
    (hrH : RootReader lvl e hftHttp httpGetByte.machineData) (hrT : RootReader lvl e hftTlp tlpCplByte.machineData)
    (hg : HftKidsGates e) (hke : HftKidsStartEnvX O e) :
    MachineClosesAtAX (mref := mref) (cref := cref) O mctx cctx hftRoot synth_hftPcieOutByte.machineData.shape :=
  Tools.ShippingCallsGatePinned.machineClosesAtA_of_gateKids'X O T hA synth_hftPcieOutByte.machineData
    synth_hftPcieOutByte.machine_ok synth_hftPcieOutByte.machine_body hft_alias hft_gateCalls
    (fun k => nkOf ((synth_hftPcieOutByte.machineData.shape.insts[k]?.map (·.1)).getD Name.anonymous))
    (fun x hx => (hft_nomem x hx).1)
    (fun k hk' y h => by
      have hmem := hft_kids_names _ (List.getElem_mem hk')
      have := hft_kid_ifaceKX O T hcell hrH hrT hg hke hmem h
      simpa [List.getElem?_eq_getElem hk'] using this)
    (fun k hk' => by
      have := hft_argsN _ (List.getElem_mem hk')
      simpa [List.getElem?_eq_getElem hk'] using this)
    (Tools.ShippingNameDischarge.names_inj _)
    (Tools.ShippingNameDischarge.parent_ne _ _ hft_noparent)
    (fun k _ o ho => Tools.ShippingCallsGate.instName_ne_of_head (hft_outs_head o ho) k _)


/-- `hftCoreCloses_of_kids` with `hkids` replaced by the run-local children's facts (`hrH hrT hg hke`) and `CellPrem` -/
theorem hftCoreCloses_of_kidsKX (L : LawsX mref cref) {w : Void IO.RealWorld}
    (hstart : StartX L mctx cctx w) (hcell : CellPrem MkRefd mref cref) {lvl : Lean.Expr → Nat}
    (hrH : RootReader lvl (envAt cref w) hftHttp httpGetByte.machineData)
    (hrT : RootReader lvl (envAt cref w) hftTlp tlpCplByte.machineData)
    (hg : HftKidsGates (envAt cref w)) (hke : HftKidsStartEnvX L.O (envAt cref w)) :
    HftCoreCloses mctx mref cctx cref w := by
  intro raw D₀ w1 hr s wh w2 w3 w4 envR ci hh hgetX henv hbody envR' w8 w10 r henv' hrun
  have hw1 := coreHeadOff_jqcAX L.O hstart.1 hstart.2.1 (Or.inl rfl) hh
  have hw2 := triple_runsX (keeps_iff.mp (keepsA_framedX L.O hstart.1 (stableA_JQCX L.O (0 + 1)) (FramedA.constInfo _))) hw1 hgetX
  have hw3 := triple_runsX (keeps_iff.mp (keepsA_framedX L.O hstart.1 (stableA_JQCX L.O (0 + 1)) FramedA.env)) hw2 henv
  have hw8 := triple_runsX (keeps_iff.mp (keepsA_framedX L.O hstart.1 (stableA_JQCX L.O (0 + 1)) FramedA.env)) hw3 henv'
  exact hft_closesAtKX L.O L.T hstart.1 hcell hrH hrT hg hke false (0 + 1) w8 r w10 hw8 (by omega) hrun

/-! ## the final statement: `hkids` replaced by the run-local children's facts -/
section Final

open Lean Sparkle.Compiler.Elab Sparkle.Core Sparkle.Core.Domain Tools.ShippingGen2 Tools.ShippingGen5DeclConnect Tools.ShippingGen5FG
open Tools.ShippingFGCircuit Tools.ShippingFGCircuitRoots Tools.ShippingFGCircuitArtifact Tools.ShippingFGCircuitCover Tools.ShippingFGCircuitBridge
open Tools.ShippingGenFGLedgerPremises Tools.ShippingFGCircuitS1iEnv
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingFGCircuitS1kRoot Tools.ShippingFGCircuitS1kStmt Tools.ShippingFGCircuitS1kPkg
open Tools.ShippingFGCircuitS1qEndpoint
open Tools.ShippingFGCircuitS1mCD Tools.ShippingFGCircuitS1pCD Tools.ShippingFGCircuitS1rCD
open Tools.ShippingFGCircuitS1tFinal Tools.ShippingFGCircuitS1uSrc Tools.ShippingFGCircuitS1xNoRaw
open Tools.ShippingFGCircuitRunLocal


/-- `HftFinalStmtOffLNK` (S2a) with `hkids : HftKidsDefine …` replaced by `hkenv : HftKidsStartEnvX L.O (envAt cref w)` (FG D.T-4k) and `hkgates : HftKidsGates (envAt cref w)` (FG D.T-4g) (14 explicit hypotheses; `hcell`, `hreadH`, `hreadT` are the existing ones) -/
def HftFinalStmtOffLNKKX (Ob : Environment → Prop) (CV : CDRel) : Prop :=
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
    (hkenv : HftKidsStartEnvX L.O (envAt cref w))
    (hkgates : HftKidsGates (envAt cref w)),
    (∃ raw, PostRunOff mctx mref cctx cref w hftRoot D' b raw) ∧
    ∃ (mm : MonoTy shHft) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMonoV CV (envAt cref w) (GPt (ι := ι) lvl (envAt cref w))
        (PostRunOff mctx mref cctx cref w hftRoot D') hftRoot shHft mm b D' p


theorem synth_hftPcieOutByte_finalOffLNKKX (CV : CDRel) (Ob : Environment → Prop) (hOb : ∀ env, Ob env → HftObOf CV env) :
    HftFinalStmtOffLNKKX Ob CV := by
  intro hlink ι mref cref L lvl env₀ mctx cctx w w' b D' hstart hr hcell hchk hRdH hRdT hCD hTop hkenv hkgates
  exact synth_hftPcieOutByte_finalOffLNLX CV Ob hOb hlink L lvl env₀ hstart hr hcell hchk hRdH hRdT hCD hTop
    (hftCoreCloses_of_kidsKX L hstart hcell hRdH hRdT hkgates hkenv)


theorem synth_hftPcieOutByte_finalOffLNKK_ZX : HftFinalStmtOffLNKKX HftObCDZ cdvZ := synth_hftPcieOutByte_finalOffLNKKX cdvZ _ (fun _ h => h)

theorem synth_hftPcieOutByte_finalOffLNKK_YX : HftFinalStmtOffLNKKX HftObCDY cdvY := synth_hftPcieOutByte_finalOffLNKKX cdvY _ (fun _ h => h)

theorem synth_hftPcieOutByte_finalOffLNKK_XX : HftFinalStmtOffLNKKX HftObCDX cdvX := synth_hftPcieOutByte_finalOffLNKKX cdvX _ (fun _ h => h)

end Final

end Tools.ShippingFGCircuitS2dKids

#print axioms Tools.ShippingFGCircuitS2dKids.machineDefinesLinked_of_readerE
#print axioms Tools.ShippingFGCircuitS2dKids.machineChild_ifaceKX
#print axioms Tools.ShippingFGCircuitS2dKids.machineChild_of_realKX
#print axioms Tools.ShippingFGCircuitS2dKids.hft_closesAtKX
#print axioms Tools.ShippingFGCircuitS2dKids.hftCoreCloses_of_kidsKX
#print axioms Tools.ShippingFGCircuitS2dKids.synth_hftPcieOutByte_finalOffLNKK_ZX

