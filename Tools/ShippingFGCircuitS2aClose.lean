import Tools.ShippingFGCircuitS1zClose
import Tools.ShippingCallsGatePinned
import Tools.ShippingMachineClosesAtGen
set_option autoImplicit false
-- FG circuit pilot S2a: the closing success of the root's certified machine run (`hclL`), supplied except for the children's declaration reflection. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED, no new law. Results: docs/FG-CIRCUIT-PILOT.md §29.

/-! # S2a: `hclL` from the root's data and the children's actual runs

The machine run `synthesizeMachineCertified` of the root `synth_hftPcieOutByte` (docs §29.1) returns `none` only if `closeLets` refuses the transition or `closeInsts` (the root has `instFields = []`) refuses the closing. Here:

* `closeLets`: `letsClose_of_data` on the root's `machineData` (`ok`, `machine_body`, `letsAliasOk`: kernel).
* `closeInsts`: `callsPureP_of_gateKids` (pinned: both calls' children are the cache-pinned results of the run's own `synth c`), whose child-side premise (`ChildIface` of the ACTUAL child output) is `machineChild_of_realA`, a port of `machineChild_of_real` to the `RealChildA` boundary, for the two slotless machine children.
* Left, named: `HftKidsDefine` — the reflection (`MachineDefines`) of the two called declarations, in the run's contexts. -/
namespace Tools.ShippingFGCircuitS2aClose
open Lean Meta Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData Tools.ShippingMachineCloses
open Tools.ShippingMixedEntrySoundness
open Tools.ShippingCallsShape Tools.ShippingCallsRun Tools.ShippingCallsAssembly
open Tools.ShippingGateChildComb Tools.ShippingChildInv Tools.ShippingRankRun
open Tools.ShippingInlineSoundness (EntryDefines)
open Tools.ShippingMachineChildComb Tools.ShippingTransitionClosed Tools.ShippingCallsGate
open Tools.ShippingChildInvA Tools.ShippingChildVCA Tools.ShippingChildCacheA Tools.ShippingChildFresh
open Tools.ShippingChildRunA Tools.ShippingChildRunAKids Tools.ShippingChildRunAMain Tools.ShippingChildComposeC
open Tools.ShippingGen2 Tools.ShippingChildBndCore Tools.ShippingFGCircuitS1qLinked Tools.ShippingFGCircuitS1qHead Tools.ShippingEntrySoundness Tools.ShippingMachineEntry

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 2000000 in
/-- **the interface of a slotless machine child's full-entry module, on the `RealChildA` boundary** (`machineChild_iface` with the machine run taken by `machine_run_of_coreA` and `synthesizeMachineCertified_runsA`; the rest of the proof is the old one) -/
theorem machineChild_ifaceA (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
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
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineCloses mctx mref cctx cref c d.shape) :
    ChildComb b ∧
      b.inputs.length = ((d.shape.binders.take nDecl).filter fun x => x.2 != .domain).length ∧
      b.name = (Sparkle.IR.ModuleName.ofDecl c) ∧ design.modules = [] := by
  obtain ⟨M, D, w1, hcore, hpost, hdesM⟩ := synthesizeCombinational_parts hr
  obtain ⟨tenv, bb, r, w9, w10, hrun9, hw9, hres⟩ :=
    machine_run_of_coreA O hA hcore entry hw.1 (Or.inr hw.2)
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


/-- **a `RealChildA` of a slotless machine declaration has the interface** (port of `machineChild_of_real`): the child's own run, its closing from `MachineCloses` in the run's contexts, the reflection moved to them -/
theorem machineChild_of_realA (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hS : d.gateCallsOk nDecl = true) (hK : d.shape.layout.lets ≠ 0)
    (hno : d.shape.insts = []) (hsl : d.shape.layout.slots = [])
    (houts : ∃ o, d.shape.layout.outs = [o] ∧ o.name = "out")
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : ∀ (mctx' : Meta.Context) (cctx' : Core.Context),
      MachineCloses mctx' mref cctx' cref c d.shape)
    {y : Res} (h : RealChildA O c y) :
    ChildIface c ((d.shape.binders.take nDecl).filter fun x => x.2 != .domain).length y.1 y.2 := by
  cases h with
  | run mctx' cctx' w w' adm cache synth quiet hr =>
    exact machineChild_ifaceA O T adm d ok hbody hS hK hno hsl houts outTy ⟨⟨quiet, synth, rfl⟩, cache⟩ hr
      (Tools.ShippingReflectCtx.MachineDefines.ctx entry) (closes mctx' cctx')

/-! ## the root: both calls are slotless machine children -/
open Tools.ShippingFGCircuitS1kRoot Tools.ShippingFGCircuitS1kStmt Tools.ShippingFGCircuitS1zClose
open Sparkle.IP.Net.HTTP Sparkle.IP.Bus.PCIe

/-- **`HftKidsDefine`** (NAMED HYPOTHESIS; FG D.T-4, the children's part): the reflection of the two called declarations in the run's contexts — the `MachineDefines` premise that the generated endpoints already take for each called declaration (`machine_closes_at`'s `hR`). "Run-local" means only that the contexts `mctx cctx` (and the ref cells) are fixed to those of the target run; the world is NOT fixed — `MachineDefines` is universally quantified over every world (including the children's own run worlds), so this is a strong, all-world premise, not a closing fact. -/
def HftKidsDefine (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
    (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State) : Prop :=
  MachineDefines mctx mref cctx cref ``Sparkle.IP.Net.HTTP.httpGetByte httpGetByte.machineData.shape ∧
  MachineDefines mctx mref cctx cref ``Sparkle.IP.Bus.PCIe.tlpCplByte tlpCplByte.machineData.shape

/-- the number of ports of a called child -/
noncomputable def nkOf (c : Name) : Nat :=
  if c = ``Sparkle.IP.Net.HTTP.httpGetByte then
    ((httpGetByte.machineData.shape.binders.take httpGetByte.machineData.nIn).filter fun x => x.2 != .domain).length
  else
    ((tlpCplByte.machineData.shape.binders.take tlpCplByte.machineData.nIn).filter fun x => x.2 != .domain).length

theorem hft_kids_names : ∀ x ∈ synth_hftPcieOutByte.machineData.shape.insts,
    x.1 = ``Sparkle.IP.Net.HTTP.httpGetByte ∨ x.1 = ``Sparkle.IP.Bus.PCIe.tlpCplByte := by decide +kernel
theorem hft_gateCalls : synth_hftPcieOutByte.machineData.gateCallsOk (Tools.ShippingGen5Sem.kDOf synth_hftPcieOutByte.machineData) = true := by decide +kernel
theorem hft_alias : synth_hftPcieOutByte.machineData.letsAliasOk = true := by decide +kernel
theorem hft_argsN : ∀ x ∈ synth_hftPcieOutByte.machineData.shape.insts, nkOf x.1 = x.2.1.length := by decide +kernel
theorem hft_noparent : ∀ c ∈ synth_hftPcieOutByte.machineData.shape.insts, c.1 ≠ hftRoot := by decide +kernel
theorem hft_outs_head : ∀ o ∈ synth_hftPcieOutByte.machineData.shape.layout.outs, o.name.toList.head? ≠ some 'i' := by decide +kernel


/-- **the child-side fact for the ACTUAL output**: a `RealChildA` of either called declaration has the interface the closing reads (`ChildComb`, port count, the declaration's module name, an empty design) -/
theorem hft_kid_iface (O : RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hk : HftKidsDefine mctx mref cctx cref) {c : Name}
    (hc : c = ``Sparkle.IP.Net.HTTP.httpGetByte ∨ c = ``Sparkle.IP.Bus.PCIe.tlpCplByte) {y : Res}
    (h : RealChildA O c y) : ChildIface c (nkOf c) y.1 y.2 := by
  rcases hc with rfl | rfl
  · have := machineChild_of_realA O T (nDecl := httpGetByte.machineData.nIn) httpGetByte.machineData httpGetByte.machine_ok httpGetByte.machine_body
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ⟨_, rfl, rfl⟩ (by decide +kernel)
      hk.1 (fun mc cc => httpGetByte.machine_closes mc _ cc _) h
    simpa [nkOf] using this
  · have := machineChild_of_realA O T (nDecl := tlpCplByte.machineData.nIn) tlpCplByte.machineData tlpCplByte.machine_ok tlpCplByte.machine_body
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ⟨_, rfl, rfl⟩ (by decide +kernel)
      hk.2 (fun mc cc => tlpCplByte.machine_closes mc _ cc _) h
    simpa [nkOf] using this

/-- **`MachineClosesAtA` of the root**: the machine run does not return `none` from any `JQC O n` world with `1 ≤ n` (`closeLets` by `letsClose_of_data`; `closeInsts` by the pinned gate-kids closing, whose child-side premise is `hft_kid_iface` on the ACTUAL outputs) -/
theorem hft_closesAtA (O : RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx) (hk : HftKidsDefine mctx mref cctx cref) :
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx hftRoot synth_hftPcieOutByte.machineData.shape :=
  Tools.ShippingCallsGatePinned.machineClosesAtA_of_gateKids' O T hA synth_hftPcieOutByte.machineData
    synth_hftPcieOutByte.machine_ok synth_hftPcieOutByte.machine_body hft_alias hft_gateCalls
    (fun k => nkOf ((synth_hftPcieOutByte.machineData.shape.insts[k]?.map (·.1)).getD Name.anonymous))
    (fun x hx => (hft_nomem x hx).1)
    (fun k hk' y h => by
      have hmem := hft_kids_names _ (List.getElem_mem hk')
      have := hft_kid_iface O T hk hmem h
      simpa [List.getElem?_eq_getElem hk'] using this)
    (fun k hk' => by
      have := hft_argsN _ (List.getElem_mem hk')
      simpa [List.getElem?_eq_getElem hk'] using this)
    (Tools.ShippingNameDischarge.names_inj _)
    (Tools.ShippingNameDischarge.parent_ne _ _ hft_noparent)
    (fun k _ o ho => Tools.ShippingCallsGate.instName_ne_of_head (hft_outs_head o ho) k _)

/-- **`hclL` from `Start L` and the children's reflection**: for every decomposition of the target core run, the machine run embedded in it (started at `w8`, the world of the second `getEnv`) does not return `none`. The `JQC (0+1)` invariant is carried to `w3` by the core chain (as in `coreOff_ranA`) and to `w8` by the `getEnv` frame; then `hft_closesAtA`. -/
theorem hftCoreCloses_of_kids (L : Laws mref cref) {w : Void IO.RealWorld}
    (hstart : Start L mctx cctx w) (hk : HftKidsDefine mctx mref cctx cref) :
    HftCoreCloses mctx mref cctx cref w := by
  intro raw D₀ w1 hr s wh w2 w3 w4 envR ci hh hget henv hbody envR' w8 w10 r henv' hrun
  have hw1 := coreHeadOff_jqcA L.O hstart.1 hstart.2.1 (Or.inl rfl) hh
  have hw2 := triple_runs (keeps_iff.mp (keepsA_framed L.O hstart.1 (stableA_JQC L.O (0 + 1)) (FramedA.constInfo _))) hw1 hget
  have hw3 := triple_runs (keeps_iff.mp (keepsA_framed L.O hstart.1 (stableA_JQC L.O (0 + 1)) FramedA.env)) hw2 henv
  have hw8 := triple_runs (keeps_iff.mp (keepsA_framed L.O hstart.1 (stableA_JQC L.O (0 + 1)) FramedA.env)) hw3 henv'
  exact hft_closesAtA L.O L.T hstart.1 hk false (0 + 1) w8 r w10 hw8 (by omega) hrun

/-! ## the final statement: `hclL` replaced by the children's reflection `hkids` -/
section Final

open Lean Sparkle.Compiler.Elab Sparkle.Core Sparkle.Core.Domain Tools.ShippingGen2 Tools.ShippingGen5DeclConnect Tools.ShippingGen5FG
open Tools.ShippingFGCircuit Tools.ShippingFGCircuitRoots Tools.ShippingFGCircuitArtifact Tools.ShippingFGCircuitCover Tools.ShippingFGCircuitBridge
open Tools.ShippingGenFGLedgerPremises Tools.ShippingFGCircuitS1iHead Tools.ShippingFGCircuitS1iEnv
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingEntryReadsLinked (envAt CoreSaved)
open Tools.ShippingGen5EnvFrame3 (CellPrem)
open Tools.ShippingFGCircuitS1kRoot Tools.ShippingFGCircuitS1kStmt Tools.ShippingFGCircuitS1kPkg
open Tools.ShippingFGCircuitS1qLinked Tools.ShippingFGCircuitS1qEndpoint Tools.ShippingFGCircuitS1qHead
open Tools.ShippingFGCircuitS1mCD Tools.ShippingFGCircuitS1pCD Tools.ShippingFGCircuitS1rCD
open Tools.ShippingFGCircuitS1tFinal Tools.ShippingFGCircuitS1uSrc Tools.ShippingFGCircuitS1xNoRaw
open Tools.ShippingHierMono (NoInstOf)
open Tools.ShippingGen5DCEntryD (PostEntry)
open Tools.ShippingMachineEntry Tools.ShippingFGCircuitRunLocal

/-- `HftFinalStmtOffLNL` (S1z) with `hclL : HftCoreCloses …` replaced by `hkids : HftKidsDefine …` (13 explicit hypotheses) -/
def HftFinalStmtOffLNK (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ∀ (hlink : HftRootLink) {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (lvl : Lean.Expr → Nat) (env₀ : Environment)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (hstart : Start L mctx cctx w)
    (hr : RunsTo (synthesizeCombinationalOff hftRoot) mctx mref cctx cref w (b, D') w')
    (hcell : CellPrem Tools.ShippingChildFresh.MkRefd mref cref)
    (hchk : CheckedStart lvl env₀ cref w hftRoot hftRootType hftRootValue synth_hftPcieOutByte.machineData)
    (hreadH : RootReader lvl (envAt cref w) hftHttp Sparkle.IP.Net.HTTP.httpGetByte.machineData)
    (hreadT : RootReader lvl (envAt cref w) hftTlp Sparkle.IP.Bus.PCIe.tlpCplByte.machineData)
    (hcd : Ob (envAt cref w))
    (htop : ∀ p : Pkg ι (fun _ => defaultDomain), GPt (ι := ι) lvl (envAt cref w) hftRoot = some p → HftObTopCoreOff mctx mref cctx cref w b D' p)
    (hkids : HftKidsDefine mctx mref cctx cref),
    (∃ raw, PostRunOff mctx mref cctx cref w hftRoot D' b raw) ∧
    ∃ (mm : MonoTy shHft) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMonoV CV (envAt cref w) (GPt (ι := ι) lvl (envAt cref w))
        (PostRunOff mctx mref cctx cref w hftRoot D') hftRoot shHft mm b D' p

theorem synth_hftPcieOutByte_finalOffLNK (CV : CDRel) (Ob : Environment → Prop) (hOb : ∀ env, Ob env → HftObOf CV env) :
    HftFinalStmtOffLNK Ob CV := by
  intro hlink ι mref cref L lvl env₀ mctx cctx w w' b D' hstart hr hcell hchk hRdH hRdT hCD hTop hkids
  exact synth_hftPcieOutByte_finalOffLNL CV Ob hOb hlink L lvl env₀ hstart hr hcell hchk hRdH hRdT hCD hTop
    (hftCoreCloses_of_kids L hstart hkids)

theorem synth_hftPcieOutByte_finalOffLNK_Z : HftFinalStmtOffLNK HftObCDZ cdvZ := synth_hftPcieOutByte_finalOffLNK cdvZ _ (fun _ h => h)
theorem synth_hftPcieOutByte_finalOffLNK_Y : HftFinalStmtOffLNK HftObCDY cdvY := synth_hftPcieOutByte_finalOffLNK cdvY _ (fun _ h => h)
theorem synth_hftPcieOutByte_finalOffLNK_X : HftFinalStmtOffLNK HftObCDX cdvX := synth_hftPcieOutByte_finalOffLNK cdvX _ (fun _ h => h)

end Final

end Tools.ShippingFGCircuitS2aClose

#print axioms Tools.ShippingFGCircuitS2aClose.machineChild_ifaceA
#print axioms Tools.ShippingFGCircuitS2aClose.hft_closesAtA
#print axioms Tools.ShippingFGCircuitS2aClose.hftCoreCloses_of_kids
#print axioms Tools.ShippingFGCircuitS2aClose.synth_hftPcieOutByte_finalOffLNK_Z
