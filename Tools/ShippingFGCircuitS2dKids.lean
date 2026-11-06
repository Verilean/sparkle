import Tools.ShippingFGCircuitS2aClose
import Tools.ShippingFGCircuitS1oHead
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
/-- **`machineChild_ifaceA` with the all-world `MachineDefines` replaced by the run-local linked boundary** (the machine run is taken by `machine_run_of_coreC` on the run's own core chain; `entry` is asked only of THIS child run's core run, at its start world `w`) ( `synthesizeMachineCertified_runsA`; the rest of the proof is the old one) -/
theorem machineChild_ifaceK (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx) {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hS : d.gateCallsOk nDecl = true) (hK : d.shape.layout.lets ≠ 0)
    (hno : d.shape.insts = []) (hsl : d.shape.layout.slots = [])
    (houts : ∃ o, d.shape.layout.outs = [o] ∧ o.name = "out")
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Design}
    (hw : JQC O (dv w) w)
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
    machine_run_of_coreC O hA hcore (entry hcore) hw.1 (Or.inr hw.2)
  have hne := closes (profLogIO bb) w9 r w10 hrun9
  cases r with
  | none => exact absurd rfl hne
  | some res =>
  have hres' := hres res rfl
  subst hres'
  obtain ⟨t, t', d₀, run, hcl, hmt⟩ :=
    synthesizeMachineCertified_runsA O (bodyStepC_of_tele O T) hA (htr_of_tele O hA T (dv w) tenv) hw9 hrun9
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

/-- **`MachineDefinesLinked` of a child's core run** from: `ReadsAt e` at the run's start world `w` (the environment the run reads agrees with `e`), the head fact `HeadAt` at `w`, `GetEnvFrame`, the reader (`RootReader lvl e X dd`: `entry₀`, `machineShape?`) and the two refusal facts (`EntryGates e X`). The same proof as `machineDefinesLinked_of_headAt`, with the lookup taken from the run's own `getConstInfo` instead of `RootInEnv`. -/
theorem machineDefinesLinked_of_readerE {lvl : Lean.Expr → Nat} {X : Name} {dd : MachineData} {e : Environment}
    {w w' : Void IO.RealWorld} {M : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hRA : ReadsAt e cref w) (hhead : HeadAt X mctx mref cctx cref w)
    (hg : Tools.ShippingEnvSnapshot.GetEnvFrame mctx mref cctx cref)
    (hRead : RootReader lvl e X dd) (hgates : EntryGates e X) :
    MachineDefinesLinked mctx mref cctx cref X dd.shape w M D w' := by
  intro _ s w1 w2 w3 w4 envR ci h0 h1 h2 _
  have r1 : ReadsAt e cref w1 := Tools.ShippingGen5Env.ReadsAt.of_envEq (hhead s w1 h0) hRA
  have r2 : ReadsAt e cref w2 :=
    Tools.ShippingGen5Env.ReadsAt.of_frame (Tools.ShippingEnvSnapshot.envFrame_getConstInfo X hg) h1 r1
  have r3 : ReadsAt e cref w3 := Tools.ShippingGen5Env.ReadsAt.of_frame hg h2 r2
  have hf := Tools.ShippingGen5Env.ci_of_readsAt h1 r1
  obtain ⟨E, hent, hsh, -⟩ := hRead
  have hgE := hgates E hent
  unfold Tools.ShippingGen5Acc.entry₀ at hent
  rw [hf] at hent
  simp only [Option.map_some, Option.some.injEq] at hent
  subst hent
  obtain ⟨-, hi, hu, hs⟩ := Tools.ShippingGen5Env.envR_of_readsAt h2 r2
  rw [hi, hu, hs]
  refine ⟨hgE.1, hgE.2, ?_⟩
  intro envR' w8 h3
  obtain ⟨-, -, -, hs'⟩ := Tools.ShippingGen5Env.envR_of_readsAt h3 r3
  rw [hs']
  exact hsh

/-- **`KidStartEnv`** (NAMED HYPOTHESIS; FG D.T-4, the children's part, row `D.T-4k`): for EVERY run of the child `c`'s full entry in a `RealChildA`-admissible start world `w` (the fields of `RealChildA.run`: admissible contexts, cache invariant, the synthesis ref, quiet), (A) the Core environment that world reads agrees with `e` (`ReadsAt e cref w`), and (B) the profile lookup `IO.getEnv "SPARKLE_PROFILE"` from `w` returns `none` and keeps the Core environment (`GetEnvProfileAt`, the profile-off branch as for the root). It replaces the all-world `MachineDefines c shape` by two environment-frame facts at the child's own start world; no shape or gate content, no closing fact. -/
def KidStartEnv (O : RefLawsAOps MkRefd mref cref) (e : Environment) (c : Name) : Prop :=
  ∀ (mctx' : Meta.Context) (cctx' : Core.Context) (w w' : Void IO.RealWorld) (y : Res),
    AdmCtx O.quiet mctx' cctx' → (∀ c' r', (cv w).get? c' = some r' → RealChildA O c' r') →
    sv w = some synthesizeChild → O.quiet w →
    RunsTo (synthesizeCombinational c) mctx' mref cctx' cref w y w' →
    ReadsAt e cref w ∧ GetEnvProfileAt mctx' mref cctx' cref w

/-- `machineChild_of_realA` with `MachineDefines` replaced by `KidStartEnv` + the reader + the gates -/
theorem machineChild_of_realK (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hcell : CellPrem MkRefd mref cref) {lvl : Lean.Expr → Nat} {e : Environment}
    {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hS : d.gateCallsOk nDecl = true) (hK : d.shape.layout.lets ≠ 0)
    (hno : d.shape.insts = []) (hsl : d.shape.layout.slots = [])
    (houts : ∃ o, d.shape.layout.outs = [o] ∧ o.name = "out")
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hRead : RootReader lvl e c d) (hgates : EntryGates e c) (hk : KidStartEnv O e c)
    (closes : ∀ (mctx' : Meta.Context) (cctx' : Core.Context),
      MachineCloses mctx' mref cctx' cref c d.shape)
    {y : Res} (h : RealChildA O c y) :
    ChildIface c ((d.shape.binders.take nDecl).filter fun x => x.2 != .domain).length y.1 y.2 := by
  cases h with
  | run mctx' cctx' w w' adm cache synth quiet hr =>
    obtain ⟨hRA, hprof⟩ := hk mctx' cctx' w w' _ adm cache synth quiet hr
    exact machineChild_ifaceK O T adm d ok hbody hS hK hno hsl houts outTy ⟨⟨quiet, synth, rfl⟩, cache⟩ hr
      (fun _ => machineDefinesLinked_of_readerE hRA (headAt_of_profileOff c hcell hprof)
        (getEnvFrame_of_cellPrem hcell) hRead hgates) (closes mctx' cctx')

/-! ## the root: both calls -/
open Tools.ShippingFGCircuitS1kRoot Tools.ShippingFGCircuitS1kStmt Tools.ShippingFGCircuitS1zClose Tools.ShippingFGCircuitS2aClose
open Sparkle.IP.Net.HTTP Sparkle.IP.Bus.PCIe

/-- `KidStartEnv` for both called declarations (NAMED HYPOTHESIS, FG D.T-4k) -/
def HftKidsStartEnv (O : RefLawsAOps MkRefd mref cref) (e : Environment) : Prop :=
  KidStartEnv O e hftHttp ∧ KidStartEnv O e hftTlp

/-- the two refusal facts of both called declarations' entry constants in the start environment `e` (NAMED HYPOTHESIS, FG D.T-4g; the gate half of what `hchk` gives the root) -/
def HftKidsGates (e : Environment) : Prop :=
  EntryGates e hftHttp ∧ EntryGates e hftTlp

theorem hft_kid_ifaceK (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hcell : CellPrem MkRefd mref cref) {lvl : Lean.Expr → Nat} {e : Environment}
    (hrH : RootReader lvl e hftHttp httpGetByte.machineData) (hrT : RootReader lvl e hftTlp tlpCplByte.machineData)
    (hg : HftKidsGates e) (hke : HftKidsStartEnv O e) {c : Name}
    (hc : c = ``Sparkle.IP.Net.HTTP.httpGetByte ∨ c = ``Sparkle.IP.Bus.PCIe.tlpCplByte) {y : Res}
    (h : RealChildA O c y) : ChildIface c (nkOf c) y.1 y.2 := by
  rcases hc with rfl | rfl
  · have := machineChild_of_realK O T hcell (nDecl := httpGetByte.machineData.nIn) httpGetByte.machineData httpGetByte.machine_ok httpGetByte.machine_body
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ⟨_, rfl, rfl⟩ (by decide +kernel)
      hrH hg.1 hke.1 (fun mc cc => httpGetByte.machine_closes mc _ cc _) h
    simpa [nkOf, hftHttp, hftTlp] using this
  · have := machineChild_of_realK O T hcell (nDecl := tlpCplByte.machineData.nIn) tlpCplByte.machineData tlpCplByte.machine_ok tlpCplByte.machine_body
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ⟨_, rfl, rfl⟩ (by decide +kernel)
      hrT hg.2 hke.2 (fun mc cc => tlpCplByte.machine_closes mc _ cc _) h
    simpa [nkOf, hftHttp, hftTlp] using this

theorem hft_closesAtK (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx) (hcell : CellPrem MkRefd mref cref) {lvl : Lean.Expr → Nat} {e : Environment}
    (hrH : RootReader lvl e hftHttp httpGetByte.machineData) (hrT : RootReader lvl e hftTlp tlpCplByte.machineData)
    (hg : HftKidsGates e) (hke : HftKidsStartEnv O e) :
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx hftRoot synth_hftPcieOutByte.machineData.shape :=
  Tools.ShippingCallsGatePinned.machineClosesAtA_of_gateKids' O T hA synth_hftPcieOutByte.machineData
    synth_hftPcieOutByte.machine_ok synth_hftPcieOutByte.machine_body hft_alias hft_gateCalls
    (fun k => nkOf ((synth_hftPcieOutByte.machineData.shape.insts[k]?.map (·.1)).getD Name.anonymous))
    (fun x hx => (hft_nomem x hx).1)
    (fun k hk' y h => by
      have hmem := hft_kids_names _ (List.getElem_mem hk')
      have := hft_kid_ifaceK O T hcell hrH hrT hg hke hmem h
      simpa [List.getElem?_eq_getElem hk'] using this)
    (fun k hk' => by
      have := hft_argsN _ (List.getElem_mem hk')
      simpa [List.getElem?_eq_getElem hk'] using this)
    (Tools.ShippingNameDischarge.names_inj _)
    (Tools.ShippingNameDischarge.parent_ne _ _ hft_noparent)
    (fun k _ o ho => Tools.ShippingCallsGate.instName_ne_of_head (hft_outs_head o ho) k _)

/-- `hftCoreCloses_of_kids` with `hkids` replaced by the run-local children's facts (`hrH hrT hg hke`) and `CellPrem` -/
theorem hftCoreCloses_of_kidsK (L : Laws mref cref) {w : Void IO.RealWorld}
    (hstart : Start L mctx cctx w) (hcell : CellPrem MkRefd mref cref) {lvl : Lean.Expr → Nat}
    (hrH : RootReader lvl (envAt cref w) hftHttp httpGetByte.machineData)
    (hrT : RootReader lvl (envAt cref w) hftTlp tlpCplByte.machineData)
    (hg : HftKidsGates (envAt cref w)) (hke : HftKidsStartEnv L.O (envAt cref w)) :
    HftCoreCloses mctx mref cctx cref w := by
  intro raw D₀ w1 hr s wh w2 w3 w4 envR ci hh hget henv hbody envR' w8 w10 r henv' hrun
  have hw1 := coreHeadOff_jqcA L.O hstart.1 hstart.2.1 (Or.inl rfl) hh
  have hw2 := triple_runs (keeps_iff.mp (keepsA_framed L.O hstart.1 (stableA_JQC L.O (0 + 1)) (FramedA.constInfo _))) hw1 hget
  have hw3 := triple_runs (keeps_iff.mp (keepsA_framed L.O hstart.1 (stableA_JQC L.O (0 + 1)) FramedA.env)) hw2 henv
  have hw8 := triple_runs (keeps_iff.mp (keepsA_framed L.O hstart.1 (stableA_JQC L.O (0 + 1)) FramedA.env)) hw3 henv'
  exact hft_closesAtK L.O L.T hstart.1 hcell hrH hrT hg hke false (0 + 1) w8 r w10 hw8 (by omega) hrun

end Tools.ShippingFGCircuitS2dKids
