import Tools.ShippingFGCircuitS1zClose
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
-- FG circuit pilot S2s4: SELECTIVE port of ShippingFGCircuitS1zClose.lean onto the context-predicate bundles (only the declarations that mention RefLawsAOps/AdmCtx/Laws/... or an already-ported name; the rest is taken from the imported original); rename-only script scripts/s2s_port2.py (suffix X, `AdmCtx O.quiet` -> `O.adm`). No sorry/axiom/native_decide/TRUSTED/law.
set_option autoImplicit false
-- FG circuit pilot S1z: `hcl` localised to the closing success of the certified machine run inside the target core run, and `hgate` derived from it. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED, no new law. Results: docs/FG-CIRCUIT-PILOT.md §28.

/-! # S1z: the localised closing

S1x took `hcl : MachineCloses …` (`∀ tenv logProf w r w′`, an existing strong premise) and `hgate : HftPostGate`. Here:

* `CoreCloses declName shape … w` (docs §28.2): for the machine run (`synthesizeMachineCertified`, `tenv := envR`, `profLogIO false`) that starts at the world `w8` read by the SECOND `getEnv` of the `synthesizeFromConst` of the given `core_chainOff` decomposition of the target core run, the result is not `none`. Nothing is said of other worlds, other `tenv`/loggers or other declarations.
* `coreOff_closed_local`: `coreOff_closed` from it.
* `coreOff_ranA`: from it and `Start L`, the embedded run is a `MachineRanA` (it returns `some (raw, D₀)`; `closeLets`; `CloseCalls` with `ChildrenRealA`).
* `hftPostGate_of_local`: `HftPostGate` from `MachineRanA` by `core_hierGate_anyA` (the body after the closing and the post-processing). -/
namespace Tools.ShippingFGCircuitS1zClose
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

section Proofs
open Tools.ShippingEntrySoundness
open Tools.ShippingChildInv Tools.ShippingChildBndInit Tools.ShippingChildBndCore Tools.ShippingChildInvA Tools.ShippingChildFresh
open Tools.ShippingChildVCA Tools.ShippingChildCacheA Tools.ShippingChildVertA Tools.ShippingChildCoreC Tools.ShippingChildRunA
open Tools.ShippingServedRealA Tools.ShippingChildRunAKids Tools.ShippingMachineClose Tools.ShippingMixedEntrySoundness Sparkle.IR.Machine
open Tools.ShippingChildComposeC Tools.ShippingChildRunAMain Tools.ShippingParentRanA
variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- `synthesizeFromConst_machine_invRX` with the START WORLD of the machine run exposed: it is the world `w6` read by the `getEnv` of the body -/
theorem synthesizeFromConst_machine_invWX (O : RefLawsAOpsX MkRefd mref cref)
    (hA : O.adm mctx cctx) {tenv : Lean.Environment}
    {logProf : String → IO Unit} {declName : Name} {n : Nat}
    {ci : ConstantInfo} {isInst : Lean.Expr → Bool} {m : Sparkle.IR.AST.Module}
    {d : Sparkle.IR.AST.Design} {w w' : Void IO.RealWorld}
    (old : certifiedShape? false [] ci = none)
    (miss : mixedCertifiedShape? false [] ci isInst = none) (hw : JQCX O n w)
    (hr : RunsTo (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) logProf
      declName [] false true ci isInst) mctx mref cctx cref w (m, d) w') :
    ∃ (envR : Environment) (w6 : Void IO.RealWorld),
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w envR w6 ∧ JQCX O n w6 ∧
      ∀ shape, machineShape? false [] ci (structEnv envR) = some shape →
        ∃ r w8, RunsTo (synthesizeMachineCertified
            (fun e hint top named => translateExprToWire tenv e hint top named) logProf declName
            shape) mctx mref cctx cref w6 r w8 ∧
          ∀ res, r = some res → res = (m, d) := by
  unfold synthesizeFromConst at hr
  simp only [↓reduceIte, old, miss, Bool.not_false, Bool.and_self, List.isEmpty_nil] at hr
  obtain ⟨envR, w1, henv, hr⟩ := RunsTo.bind hr
  have hw1 := triple_runsX (keeps_iff.mp (keepsA_framedX O hA (stableA_JQCX O n) FramedA.env)) hw henv
  obtain ⟨mach, w2, hp, hr⟩ := RunsTo.bind hr
  obtain ⟨hm, rfl⟩ := RunsTo.pure_world hp
  subst hm
  refine ⟨envR, _, henv, hw1, ?_⟩
  intro shape hs
  rw [hs] at hr
  dsimp only at hr
  obtain ⟨r, w3, hmach, hr⟩ := RunsTo.bind hr
  refine ⟨r, _, hmach, ?_⟩
  intro res hres
  subst hres
  dsimp only at hr
  have hr := hr.mreturns
  peel_bind hr
  peel_bind hr
  exact (MReturns.pure hr).symm


/-- **the embedded machine run is a `MachineRanA`** (it returns `some (M, D)`, `closeLets`, `CloseCalls` with `ChildrenRealAX`), from the localised closing and `StartX L` -/
theorem coreOff_ranAX (L : LawsX mref cref) {declName : Name} {shape : MachineShape} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (hstart : StartX L mctx cctx w)
    (hr : RunsTo (synthesizeCombinationalCoreOff declName) mctx mref cctx cref w (m, d) w')
    (entry : MachineDefinesLinkedOff mctx mref cctx cref declName shape w m d w')
    (hloc : CoreCloses declName shape mctx mref cctx cref w) :
    MachineRanA L.O mctx cctx declName shape m d := by
  obtain ⟨s, w1, envR, ci, w2, w3, w4, hh, hgetX, henv, hbody, -⟩ := core_chainOff hr
  have hw1 := coreHeadOff_jqcA L.O hstart.1 hstart.2.1 (Or.inl rfl) hh
  have hw2 := triple_runsX (keeps_iff.mp (keepsA_framedX L.O hstart.1 (stableA_JQCX L.O (0 + 1)) (FramedA.constInfo _))) hw1 hgetX
  have hw3 := triple_runsX (keeps_iff.mp (keepsA_framedX L.O hstart.1 (stableA_JQCX L.O (0 + 1)) FramedA.env)) hw2 henv
  obtain ⟨old, miss, hshape⟩ := entry hr s w1 w2 w3 w4 envR ci hh hgetX henv hbody
  obtain ⟨envR', w8, henv', hw8, hmach⟩ := synthesizeFromConst_machine_invWX L.O hstart.1 old miss hw3 hbody
  obtain ⟨r, w10, hrun, hres⟩ := hmach shape (hshape _ _ henv')
  have hne := hloc m d w' hr s w1 w2 w3 w4 envR ci hh hgetX henv hbody envR' w8 w10 r henv' hrun
  cases r with
  | none => exact absurd rfl hne
  | some res =>
    have := hres res rfl
    subst this
    obtain ⟨t, t', d₀, run, hcl, hmt⟩ :=
      synthesizeMachineCertified_runsAX (b := false) L.O (bodyStepC_of_teleX L.O L.T) hstart.1
        (htr_of_teleX L.O hstart.1 L.T 0 envR) hw8 hrun
    exact ⟨envR, false, w8, w10, hrun, t, t', d₀, run, hcl, hmt⟩


/-- the closing's last check, from the embedded run -/
theorem closed_of_ranAX {O : RefLawsAOpsX MkRefd mref cref} {c : Name} {shape : MachineShape} {M : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (ran : MachineRanA O mctx cctx c shape M D) (hI : shape.insts ≠ []) :
    NoInstOf M.name M.body ∧ ∀ g ∈ D.modules, NoInstOf M.name g.body := by
  obtain ⟨-, -, -, -, -, t, t', d₀, -, -, hmt⟩ := ran
  rcases hmt with ⟨hno, -, -⟩ | ⟨-, children, hcc, -⟩
  · exact absurd hno hI
  · rcases hcc with ⟨-, hc⟩ | ⟨-, hc, -⟩
    · obtain ⟨-, h1, h2, -⟩ := Tools.ShippingChildServe.closeInsts_acyclic hc
      exact ⟨h1, h2⟩
    · obtain ⟨-, h1, h2⟩ := Tools.ShippingChildServe.closeInstsG_acyclic hc
      exact ⟨h1, h2⟩

/-! ## the root's data facts and `hgate` -/
open Tools.ShippingGen5Sem (kDOf)


/-- **`HftPostGate` is derived** (it is no longer a hypothesis): the embedded closing run is a `MachineRanA`; the closed body is the instances plus the `seqStmtOk` statements of the closed machine, and the post-processing keeps that (`core_hierGate_anyA`) -/
theorem hftPostGate_of_localX (L : LawsX mref cref) {w : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (hstart : StartX L mctx cctx w)
    (hdRun : ∀ raw D₀ w1, MachineDefinesLinkedOff mctx mref cctx cref hftRoot synth_hftPcieOutByte.machineData.shape w raw D₀ w1)
    (hclL : HftCoreCloses mctx mref cctx cref w) :
    HftPostGate mctx mref cctx cref w b D' := by
  intro raw D₀ w1 hr hpe
  have ran := coreOff_ranAX L hstart hr (hdRun raw D₀ w1) hclL
  have hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw) :=
    hpe.imp And.left And.left
  exact Tools.ShippingParentDesignA.core_hierGate_anyA L.O synth_hftPcieOutByte.machineData synth_hftPcieOutByte.machine_ok
    synth_hftPcieOutByte.machine_body hft_callsOk hft_slots hft_domB hftShape_insts_ne hft_outTy hft_nomem hpost ran


/-- **`HftObNoRawOff` from the localised closing alone** -/
theorem hftObNoRawOff_of_localX (L : LawsX mref cref) {w : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (hstart : StartX L mctx cctx w)
    (hdRun : ∀ raw D₀ w1, MachineDefinesLinkedOff mctx mref cctx cref hftRoot synth_hftPcieOutByte.machineData.shape w raw D₀ w1)
    (hclL : HftCoreCloses mctx mref cctx cref w) :
    HftObNoRawOff mctx mref cctx cref w b D' := by
  intro raw D₀ w1 hr hpe
  obtain ⟨h1, h2⟩ := closed_of_ranAX (coreOff_ranAX L hstart hr (hdRun raw D₀ w1) hclL) hftShape_insts_ne
  exact ⟨fun n => Tools.ShippingGen5DCEntryS.noRawBelow_of_noInstOf h2 (n + 1) raw h1,
    fun n => noRawBelow_opt hpe h1 h2 (hftPostGate_of_localX L hstart hdRun hclL raw D₀ w1 hr hpe) (n + 1), noB_of_post hpe h1⟩

end Proofs

/-! ## the final statement: `hcl` and `hgate` replaced by the one localised `hclL` -/
section Final
open Sparkle.Compiler.Elab (synthesizeCombinationalCoreOff)


/-- `HftFinalStmtOffLN` (S1x) with `hcl hgate` replaced by `hclL : HftCoreCloses …` (13 explicit hypotheses) -/
def HftFinalStmtOffLNLX (Ob : Environment → Prop) (CV : CDRel) : Prop :=
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
    (hclL : HftCoreCloses mctx mref cctx cref w),
    (∃ raw, PostRunOff mctx mref cctx cref w hftRoot D' b raw) ∧
    ∃ (mm : MonoTy shHft) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMonoV CV (envAt cref w) (GPt (ι := ι) lvl (envAt cref w))
        (PostRunOff mctx mref cctx cref w hftRoot D') hftRoot shHft mm b D' p


theorem synth_hftPcieOutByte_finalOffLNLX (CV : CDRel) (Ob : Environment → Prop) (hOb : ∀ env, Ob env → HftObOf CV env) :
    HftFinalStmtOffLNLX Ob CV := by
  intro hlink ι mref cref L lvl env₀ mctx cctx w w' b D' hstart hr hcell hchk hRdH hRdT hCD hTop hclL
  have hhead : HeadAtOff hftRoot mctx mref cctx cref w := headAtOff_of_cellPrem _ hcell
  obtain ⟨raw, D₀, w1, hc, hpe⟩ := postEntryOff hr
  obtain ⟨hgates, ⟨d, hE⟩, hRead⟩ := startFacts_of_checked hchk (root_find_of_headAtOff hhead hc)
  have hdRun : ∀ raw D₀ w1, MachineDefinesLinkedOff mctx mref cctx cref hftRoot synth_hftPcieOutByte.machineData.shape w raw D₀ w1 :=
    fun _ _ _ => machineDefinesLinked_of_reader_headAtOff hhead (Tools.ShippingFGCircuitS1hFrame.getEnvFrame_of_readWorld hcell.2.2.2.2.2.2.2.2.1) hE hRead hgates
  exact synth_hftPcieOutByte_finalOffL CV Ob hOb hlink L lvl env₀ hstart hr hcell hchk hRdH hRdT hCD hTop
    (hftObNoRawOff_of_localX L hstart hdRun hclL)


theorem synth_hftPcieOutByte_finalOffLNL_ZX : HftFinalStmtOffLNLX HftObCDZ cdvZ := synth_hftPcieOutByte_finalOffLNLX cdvZ _ (fun _ h => h)

theorem synth_hftPcieOutByte_finalOffLNL_YX : HftFinalStmtOffLNLX HftObCDY cdvY := synth_hftPcieOutByte_finalOffLNLX cdvY _ (fun _ h => h)

theorem synth_hftPcieOutByte_finalOffLNL_XX : HftFinalStmtOffLNLX HftObCDX cdvX := synth_hftPcieOutByte_finalOffLNLX cdvX _ (fun _ h => h)

end Final

end Tools.ShippingFGCircuitS1zClose

#print axioms Tools.ShippingFGCircuitS1zClose.coreCloses_of_machineCloses
#print axioms Tools.ShippingFGCircuitS1zClose.coreOff_ranAX
#print axioms Tools.ShippingFGCircuitS1zClose.closed_of_ranAX
#print axioms Tools.ShippingFGCircuitS1zClose.hftPostGate_of_localX
#print axioms Tools.ShippingFGCircuitS1zClose.hftObNoRawOff_of_localX
#print axioms Tools.ShippingFGCircuitS1zClose.synth_hftPcieOutByte_finalOffLNL_ZX

