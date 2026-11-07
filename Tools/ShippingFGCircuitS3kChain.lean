import Tools.ShippingFGCircuitS3jFinal
set_option autoImplicit false
-- FG circuit pilot S3k, unit 1: the selective port of the chain behind v9 that consumes `Start` / `StartX` at the START world, with `hstart` split into `hadm` (the context predicate) and the JQ-only `hjq : JQ L.O.quiet 0 w` — NO cache invariant of the start world.  Each declaration is a copy of the original with `hstart` replaced (`hstart.1` ↦ `hadm`, `hstart.2.1` ↦ `hjq`); proofs are otherwise unchanged, names carry the suffix `_k`, the originals are untouched, everything else is reused.  No sorry/axiom/native_decide/TRUSTED/law. docs/FG-CIRCUIT-PILOT.md §61.
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace Tools.ShippingFGCircuitS1tFinal
open Tools.ShippingChildVCA (JQ)
open Lean Sparkle.Compiler.Elab Sparkle.Core Sparkle.Core.Domain Tools.ShippingGen2 Tools.ShippingGen5DeclConnect Tools.ShippingGen5FG
open Tools.ShippingFGCircuit Tools.ShippingFGCircuitRoots Tools.ShippingFGCircuitArtifact Tools.ShippingFGCircuitCover Tools.ShippingFGCircuitBridge
open Tools.ShippingGenFGLedgerPremises Tools.ShippingFGCircuitS1iHead Tools.ShippingFGCircuitS1iEnv
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingEntryReadsLinked (envAt)
open Tools.ShippingStRefCorrespondence (ReadWorld)
open Tools.ShippingGen5EnvFrame3 (CellPrem)
open Tools.ShippingFGCircuitS1kRoot Tools.ShippingFGCircuitS1kStmt Tools.ShippingFGCircuitS1kPkg
open Tools.ShippingFGCircuitS1qLinked Tools.ShippingFGCircuitS1qEndpoint Tools.ShippingFGCircuitS1qHead
open Tools.ShippingFGCircuitS1mCD Tools.ShippingFGCircuitS1pCD Tools.ShippingFGCircuitS1rCD
/-- **`HftFinalStmtOffX_k Ob CV`**: the final statement of the non-leaf root `synth_hftPcieOutByte`.
Top run: `synthesizeCombinationalOff hftRoot` (the guaranteed entry). `hcell : CellPrem` supplies the head (`HeadAtOff`) and `ReadWorld`; there is no `hhead`.
`hcd : Ob (envAt cref w)`: the carrier obligation in the start environment (`Ob` is any of `HftObCDX/Y/Z` or a future family). The conclusion: the package from the table, the source meaning over `CV` (read in the SAME start environment), the observation
correspondence, and `TopShips` for every `raw` of `PostRunOff`. The children's own entry (`synthesizeChild`) is NOT changed and is not mentioned in the type. -/
def HftFinalStmtOffX_k (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ∀ {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : LawsX mref cref) (lvl : Lean.Expr → Nat) (env₀ : Environment)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (hadm : L.O.adm mctx cctx) (hjq : JQ L.O.quiet 0 w)
    (hr : RunsTo (synthesizeCombinationalOff hftRoot) mctx mref cctx cref w (b, D') w')
    (hcell : CellPrem Tools.ShippingChildFresh.MkRefd mref cref)
    (hchk : CheckedStart lvl env₀ cref w hftRoot hftRootType hftRootValue synth_hftPcieOutByte.machineData)
    (hreadH : RootReader lvl (envAt cref w) hftHttp Sparkle.IP.Net.HTTP.httpGetByte.machineData)
    (hreadT : RootReader lvl (envAt cref w) hftTlp Sparkle.IP.Bus.PCIe.tlpCplByte.machineData)
    (hcd : Ob (envAt cref w)) (hsrc : HftObSrc (ι := ι) lvl (envAt cref w))
    (htop : ∀ p : Pkg ι (fun _ => defaultDomain), GPt (ι := ι) lvl (envAt cref w) hftRoot = some p → HftObTopCoreOff mctx mref cctx cref w b D' p)
    (hnoraw : HftObNoRawOff mctx mref cctx cref w b D'),
    (∃ raw, PostRunOff mctx mref cctx cref w hftRoot D' b raw) ∧
    ∃ (mm : MonoTy shHft) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMonoV CV (envAt cref w) (GPt (ι := ι) lvl (envAt cref w))
        (PostRunOff mctx mref cctx cref w hftRoot D') hftRoot shHft mm b D' p

/-! ## 4. the assembly (the analogue of `synth_hftPcieOutByte_final`, on `Off` and the new carrier) -/


/-- **`synth_hftPcieOutByte_finalOffX_k`**: for every carrier `CV` and every obligation `Ob` that gives the root-value derivation in `CV` (`hOb`), the statement holds. The proof is S1k's assembly with: `HeadAtOff` from `CellPrem`
(S1q), `postEntryOff`, `MachineDefinesLinkedOff`, `PostRunOff`; the only carrier-specific step is `hOb`. -/
theorem synth_hftPcieOutByte_finalOffX_k (CV : CDRel) (Ob : Environment → Prop) (hOb : ∀ env, Ob env → HftObOf CV env) : HftFinalStmtOffX_k Ob CV := by
  intro ι mref cref L lvl env₀ mctx cctx w w' b D' hadm hjq hr hcell hchk hRdH hRdT hCD hSrc hTop hNoRaw
  have hhead : HeadAtOff hftRoot mctx mref cctx cref w := headAtOff_of_cellPrem _ hcell
  obtain ⟨raw, D₀, w1, hc, hpe⟩ := postEntryOff hr
  obtain ⟨hgates, ⟨d, hE⟩, hRead⟩ := startFacts_of_checked hchk (root_find_of_headAtOff hhead hc)
  have hdRun : ∀ raw D₀ w1, MachineDefinesLinkedOff mctx mref cctx cref hftRoot synth_hftPcieOutByte.machineData.shape w raw D₀ w1 :=
    fun _ _ _ => machineDefinesLinked_of_reader_headAtOff hhead (Tools.ShippingFGCircuitS1hFrame.getEnvFrame_of_readWorld hcell.2.2.2.2.2.2.2.2.1) hE hRead hgates
  obtain ⟨E, hEnt, hsh, hdat⟩ := hRead
  obtain ⟨g, hg, hgd⟩ := canon_row (lvl := lvl) (env := envAt cref w) root_wf hsh hdat
  obtain ⟨Eh, hEh, hshh, hdath⟩ := hRdH
  obtain ⟨gh, hgh, hghd⟩ := canon_row (lvl := lvl) (env := envAt cref w) http_wf hshh hdath
  obtain ⟨Et, hEt, hsht, hdatt⟩ := hRdT
  obtain ⟨gt, hgt, hgtd⟩ := canon_row (lvl := lvl) (env := envAt cref w) tlp_wf hsht hdatt
  have hkids : ∀ c ∈ g.d.shape.insts.map (·.1), ∃ (Ec : ConstantInfo) (gc : Tools.ShippingGen5Sem.GenData (Tools.ShippingGen5DataOf.dataOfAt lvl) Ec (structEnv (envAt cref w))),
      Tools.ShippingGen5Acc.entry₀ (envAt cref w) c = some Ec ∧ canonGD lvl (envAt cref w) Ec = some gc ∧ gc.d.shape.insts = [] := by
    intro c hc
    rw [hgd, root_insts] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact ⟨Eh, gh, hEh, hgh, by rw [hghd]; exact http_leaf⟩
    · exact ⟨Et, gt, hEt, hgt, by rw [hgtd]; exact tlp_leaf⟩
  obtain ⟨p, hP, hdecl, hpd, hkp⟩ := genGP_root_kids (ι := ι) (dom := fun _ => defaultDomain) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) (envAt cref w) hEnt hg hkids
  rw [hgd] at hpd
  have hkD : p.kD = 5 := by rw [hkp, hgd]; exact root_kD
  have hl : EndpointLink synth_hftPcieOutByte.machineData 5 (fun _ bools bits => monoObs shHft synth_hftPcieOutByte bools bits) p :=
    ⟨hpd, hkD, hSrc p hP⟩
  have hpost : ∃ raw, PostRunOff mctx mref cctx cref w hftRoot D' b raw := ⟨raw, D₀, w1, hc, hpe⟩
  refine ⟨hpost, synth_hftPcieOutByte, p, hP, ?_, observationsEqualMono_of_link root_shape hl, ?_⟩
  · obtain ⟨hf, hlv, ht, hv⟩ := hE
    refine ⟨rfl, d, hf, hlv, ?_, ?_⟩
    · show (if d.levelParams.isEmpty = true then monoGo [] d.type else none) = some shHft
      rw [hlv, ht]; simpa using hftRootType_shape
    · rw [hv]; exact hOb _ hCD
  · intro raw' ⟨D₀', w1', hr', hpe'⟩
    obtain ⟨n, hn⟩ := hTop p hP hdRun raw' D₀' w1' hr' hpe'
    obtain ⟨h1, h2, h3⟩ := hNoRaw raw' D₀' w1' hr' hpe'
    exact ⟨n, hdecl, Tools.ShippingFGCircuitS1iChild.topShips_transport p n hftRoot hpe' (h1 n) (h2 n) h3 hn⟩


end Tools.ShippingFGCircuitS1tFinal

namespace Tools.ShippingFGCircuitS1uSrc
open Tools.ShippingChildVCA (JQ)
open Lean Sparkle.Compiler.Elab Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingMachineDenote Tools.ShippingMachineAuto Tools.ShippingMachineSource
open Tools.ShippingGen5Sem Tools.ShippingGen2
open Tools.ShippingUnifiedSource (eval)
section Final
open Tools.ShippingFGCircuitS1tFinal
open Tools.ShippingFGCircuitS1kStmt Tools.ShippingFGCircuitS1kRoot Tools.ShippingFGCircuitS1kPkg
open Tools.ShippingFGCircuitS1iHead Tools.ShippingFGCircuitS1iEnv Tools.ShippingFGCircuitS1qHead Tools.ShippingFGCircuitS1qLinked
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingEntryReadsLinked (envAt)
open Tools.ShippingGen5EnvFrame3 (CellPrem)
open Tools.ShippingFGCircuitCover Tools.ShippingGenFGLedgerPremises Tools.ShippingFGCircuitArtifact Tools.ShippingGen5FG
open Tools.ShippingFGCircuit Tools.ShippingFGCircuitRoots Tools.ShippingFGCircuitBridge Tools.ShippingGen5DeclConnect
open Tools.ShippingFGCircuitS1qEndpoint Tools.ShippingFGCircuitS1mCD Tools.ShippingFGCircuitS1pCD Tools.ShippingFGCircuitS1rCD
open Tools.ShippingStRefCorrespondence (ReadWorld)
def HftFinalStmtOffLX_k (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ∀ (hlink : HftRootLink) {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : LawsX mref cref) (lvl : Lean.Expr → Nat) (env₀ : Environment)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (hadm : L.O.adm mctx cctx) (hjq : JQ L.O.quiet 0 w)
    (hr : RunsTo (synthesizeCombinationalOff hftRoot) mctx mref cctx cref w (b, D') w')
    (hcell : CellPrem Tools.ShippingChildFresh.MkRefd mref cref)
    (hchk : CheckedStart lvl env₀ cref w hftRoot hftRootType hftRootValue synth_hftPcieOutByte.machineData)
    (hreadH : RootReader lvl (envAt cref w) hftHttp Sparkle.IP.Net.HTTP.httpGetByte.machineData)
    (hreadT : RootReader lvl (envAt cref w) hftTlp Sparkle.IP.Bus.PCIe.tlpCplByte.machineData)
    (hcd : Ob (envAt cref w))
    (htop : ∀ p : Pkg ι (fun _ => defaultDomain), GPt (ι := ι) lvl (envAt cref w) hftRoot = some p → HftObTopCoreOff mctx mref cctx cref w b D' p)
    (hnoraw : HftObNoRawOff mctx mref cctx cref w b D'),
    (∃ raw, PostRunOff mctx mref cctx cref w hftRoot D' b raw) ∧
    ∃ (mm : MonoTy shHft) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMonoV CV (envAt cref w) (GPt (ι := ι) lvl (envAt cref w))
        (PostRunOff mctx mref cctx cref w hftRoot D') hftRoot shHft mm b D' p


/-- **`synth_hftPcieOutByte_finalOffLX_k`**: S1t's assembly with `hsrc` supplied by `hftObSrc_of_rootLink` -/
theorem synth_hftPcieOutByte_finalOffLX_k (CV : CDRel) (Ob : Environment → Prop) (hOb : ∀ env, Ob env → HftObOf CV env) :
    HftFinalStmtOffLX_k Ob CV := by
  intro hlink ι mref cref L lvl env₀ mctx cctx w w' b D' hadm hjq hr hcell hchk hRdH hRdT hCD hTop hNoRaw
  have hhead : HeadAtOff hftRoot mctx mref cctx cref w := headAtOff_of_cellPrem _ hcell
  obtain ⟨raw, D₀, w1, hc, hpe⟩ := postEntryOff hr
  obtain ⟨hgates, ⟨d, hE⟩, hRead⟩ := startFacts_of_checked hchk (root_find_of_headAtOff hhead hc)
  exact synth_hftPcieOutByte_finalOffX_k CV Ob hOb L lvl env₀ hadm hjq hr hcell hchk hRdH hRdT hCD
    (hftObSrc_of_rootLink hlink lvl (envAt cref w) hRead hRdH hRdT) hTop hNoRaw


end Final
end Tools.ShippingFGCircuitS1uSrc

namespace Tools.ShippingFGCircuitS1zClose
open Tools.ShippingChildVCA (JQ)
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

/-- **the embedded machine run is a `MachineRanAX`** (it returns `some (M, D)`, `closeLets`, `CloseCalls` with `ChildrenRealAX`), from the localised closing and `StartX L` -/
theorem coreOff_ranAX_k (L : LawsX mref cref) {declName : Name} {shape : MachineShape} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (hadm : L.O.adm mctx cctx) (hjq : JQ L.O.quiet 0 w)
    (hr : RunsTo (synthesizeCombinationalCoreOff declName) mctx mref cctx cref w (m, d) w')
    (entry : MachineDefinesLinkedOff mctx mref cctx cref declName shape w m d w')
    (hloc : CoreCloses declName shape mctx mref cctx cref w) :
    MachineRanAX L.O mctx cctx declName shape m d := by
  obtain ⟨s, w1, envR, ci, w2, w3, w4, hh, hgetX, henv, hbody, -⟩ := core_chainOffX hr
  have hw1 := coreHeadOff_jqcAX L.O hadm hjq (Or.inl rfl) hh
  have hw2 := triple_runsX (keeps_iff.mp (keepsA_framedX L.O hadm (stableA_JQCX L.O (0 + 1)) (FramedA.constInfo _))) hw1 hgetX
  have hw3 := triple_runsX (keeps_iff.mp (keepsA_framedX L.O hadm (stableA_JQCX L.O (0 + 1)) FramedA.env)) hw2 henv
  obtain ⟨old, miss, hshape⟩ := entry hr s w1 w2 w3 w4 envR ci hh hgetX henv hbody
  obtain ⟨envR', w8, henv', hw8, hmach⟩ := synthesizeFromConst_machine_invWX L.O hadm old miss hw3 hbody
  obtain ⟨r, w10, hrun, hres⟩ := hmach shape (hshape _ _ henv')
  have hne := hloc m d w' hr s w1 w2 w3 w4 envR ci hh hgetX henv hbody envR' w8 w10 r henv' hrun
  cases r with
  | none => exact absurd rfl hne
  | some res =>
    have := hres res rfl
    subst this
    obtain ⟨t, t', d₀, run, hcl, hmt⟩ :=
      synthesizeMachineCertified_runsAX (b := false) L.O (bodyStepC_of_teleX L.O L.T) hadm
        (htr_of_teleX L.O hadm L.T 0 envR) hw8 hrun
    exact ⟨envR, false, w8, w10, hrun, t, t', d₀, run, hcl, hmt⟩


/-- **`HftPostGate` is derived** (it is no longer a hypothesis): the embedded closing run is a `MachineRanAX`; the closed body is the instances plus the `seqStmtOk` statements of the closed machine, and the post-processing keeps that (`core_hierGate_anyAX`) -/
theorem hftPostGate_of_localX_k (L : LawsX mref cref) {w : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (hadm : L.O.adm mctx cctx) (hjq : JQ L.O.quiet 0 w)
    (hdRun : ∀ raw D₀ w1, MachineDefinesLinkedOff mctx mref cctx cref hftRoot synth_hftPcieOutByte.machineData.shape w raw D₀ w1)
    (hclL : HftCoreCloses mctx mref cctx cref w) :
    HftPostGate mctx mref cctx cref w b D' := by
  intro raw D₀ w1 hr hpe
  have ran := coreOff_ranAX_k L hadm hjq hr (hdRun raw D₀ w1) hclL
  have hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw) :=
    hpe.imp And.left And.left
  exact Tools.ShippingParentDesignA.core_hierGate_anyAX L.O synth_hftPcieOutByte.machineData synth_hftPcieOutByte.machine_ok
    synth_hftPcieOutByte.machine_body hft_callsOk hft_slots hft_domB hftShape_insts_ne hft_outTy hft_nomem hpost ran


/-- **`HftObNoRawOff` from the localised closing alone** -/
theorem hftObNoRawOff_of_localX_k (L : LawsX mref cref) {w : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (hadm : L.O.adm mctx cctx) (hjq : JQ L.O.quiet 0 w)
    (hdRun : ∀ raw D₀ w1, MachineDefinesLinkedOff mctx mref cctx cref hftRoot synth_hftPcieOutByte.machineData.shape w raw D₀ w1)
    (hclL : HftCoreCloses mctx mref cctx cref w) :
    HftObNoRawOff mctx mref cctx cref w b D' := by
  intro raw D₀ w1 hr hpe
  obtain ⟨h1, h2⟩ := closed_of_ranAX (coreOff_ranAX_k L hadm hjq hr (hdRun raw D₀ w1) hclL) hftShape_insts_ne
  exact ⟨fun n => Tools.ShippingGen5DCEntryS.noRawBelow_of_noInstOf h2 (n + 1) raw h1,
    fun n => noRawBelow_opt hpe h1 h2 (hftPostGate_of_localX_k L hadm hjq hdRun hclL raw D₀ w1 hr hpe) (n + 1), noB_of_post hpe h1⟩

end Proofs
section Final
open Sparkle.Compiler.Elab (synthesizeCombinationalCoreOff)
/-- `HftFinalStmtOffLN` (S1x) with `hcl hgate` replaced by `hclL : HftCoreCloses …` (13 explicit hypotheses) -/
def HftFinalStmtOffLNLX_k (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ∀ (hlink : HftRootLink) {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : LawsX mref cref) (lvl : Lean.Expr → Nat) (env₀ : Environment)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (hadm : L.O.adm mctx cctx) (hjq : JQ L.O.quiet 0 w)
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


theorem synth_hftPcieOutByte_finalOffLNLX_k (CV : CDRel) (Ob : Environment → Prop) (hOb : ∀ env, Ob env → HftObOf CV env) :
    HftFinalStmtOffLNLX_k Ob CV := by
  intro hlink ι mref cref L lvl env₀ mctx cctx w w' b D' hadm hjq hr hcell hchk hRdH hRdT hCD hTop hclL
  have hhead : HeadAtOff hftRoot mctx mref cctx cref w := headAtOff_of_cellPrem _ hcell
  obtain ⟨raw, D₀, w1, hc, hpe⟩ := postEntryOff hr
  obtain ⟨hgates, ⟨d, hE⟩, hRead⟩ := startFacts_of_checked hchk (root_find_of_headAtOff hhead hc)
  have hdRun : ∀ raw D₀ w1, MachineDefinesLinkedOff mctx mref cctx cref hftRoot synth_hftPcieOutByte.machineData.shape w raw D₀ w1 :=
    fun _ _ _ => machineDefinesLinked_of_reader_headAtOff hhead (Tools.ShippingFGCircuitS1hFrame.getEnvFrame_of_readWorld hcell.2.2.2.2.2.2.2.2.1) hE hRead hgates
  exact synth_hftPcieOutByte_finalOffLX_k CV Ob hOb hlink L lvl env₀ hadm hjq hr hcell hchk hRdH hRdT hCD hTop
    (hftObNoRawOff_of_localX_k L hadm hjq hdRun hclL)


end Final
end Tools.ShippingFGCircuitS1zClose

namespace Tools.ShippingFGCircuitS2mReach
open Tools.ShippingChildVCA (JQ)
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
/-- **`hftCoreCloses_of_kidsHX` with the miss premise `MissEX` replaced by the reachability / environment invariant** `JQHRX` from the start world `w` of the target root run. Premise list, replacing `hmiss : MissEX L.O (KidEv mref cref (envAt cref w))`:
`hadm` (FG D.T-4m6: the root context is admissible, `L.O.adm = AdmCtx L.O.quiet` for the original quiet predicate), (`hdown` (D.T-4m7) of the original S2m theorem is NOT a premise of this port: `L.O.adm` is kept by `ropsRX` as it is), `hD` (D.T-4m1, class-D rows), `hG` (D.T-4m2, diagnostic rows), `hT` (D.T-4m3, telescope rows), `hs` (D.T-4m4, profile lookup along leaf steps), `h0` (D.T-4m5, profile lookup unset at the root start world). `L.T` is not used. -/
theorem hftCoreCloses_of_kidsRX_k (L : LawsX mref cref) {w : Void IO.RealWorld}
    (hjq : JQ L.O.quiet 0 w) (hcell : CellPrem MkRefd mref cref) {lvl : Lean.Expr → Nat}
    (hrH : RootReader lvl (envAt cref w) hftHttp httpGetByte.machineData)
    (hrT : RootReader lvl (envAt cref w) hftTlp tlpCplByte.machineData)
    (hg : HftKidsGates (envAt cref w))
    (hadm : L.O.adm mctx cctx)
    (hD : DRowEnvRX L.O (envAt cref w) w)
    (hG : DiagEnvRX L.O (envAt cref w) w) (hT : TeleRX L.O (envAt cref w) w)
    (hs : ProfStepRX L.O w) (h0 : ProfOffW mref cref w) :
    HftCoreCloses mctx mref cctx cref w := by
  intro raw D₀ w1 hr s wh w2 w3 w4 envR ci hh hgetX henv hbody envR' w8 w10 r henv' hrun
  have hw1 := jqhr_headX (hcell := hcell) (hD := hD) (hG := hG) hadm hjq hh
  have hw2 := triple_runsX (keeps_iff.mp (keepsA_framedX (ropsRX L.O hcell (envAt cref w) w hD hG) hadm
    (stableA_JQHX _ _ (0 + 1)) (FramedA.constInfo _))) hw1 hgetX
  have hw3 := triple_runsX (keeps_iff.mp (keepsA_framedX (ropsRX L.O hcell (envAt cref w) w hD hG) hadm
    (stableA_JQHX _ _ (0 + 1)) FramedA.env)) hw2 henv
  have hw8 := triple_runsX (keeps_iff.mp (keepsA_framedX (ropsRX L.O hcell (envAt cref w) w hD hG) hadm
    (stableA_JQHX _ _ (0 + 1)) FramedA.env)) hw3 henv'
  exact hft_closesAtHX (ropsRX L.O hcell (envAt cref w) w hD hG) hT hadm hcell hrH hrT hg
    (missRX h0 hs) false (0 + 1) w8 r w10 hw8 (by omega) hrun

end Tools.ShippingFGCircuitS2mReach

namespace Tools.ShippingFGCircuitS2sAdmS2nAdm
open Tools.ShippingChildVCA (JQ)
open Lean Meta Sparkle.Compiler.Elab
open Tools.ShippingChildInvA Tools.ShippingChildCacheA
open Tools.ShippingChildFresh (MkRefd)
open Tools.ShippingGen5EnvFrame3 (CellPrem)
open Tools.ShippingEntryReadsLinked (envAt)
open Tools.ShippingFGCircuitS2mReach
open Tools.ShippingGen2 (LawsX StartX)
open Tools.ShippingFGCircuitS1zClose (HftCoreCloses)
open Tools.ShippingFGCircuitCover (RootReader)
open Tools.ShippingFGCircuitS2dKids (HftKidsGates)
open Tools.ShippingFGCircuitS1kStmt (hftHttp hftTlp)
open Sparkle.IP.Net.HTTP Sparkle.IP.Bus.PCIe

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- **`hftCoreCloses_of_kidsR''_k`: `hftCoreCloses_of_kidsR` (S2m) WITHOUT `hdown`; `hadm` is its root-context argument (not a separate binder of the final statement).** The context predicate `L.O.adm` is a field of the bundle, kept in every context update (`CtxClosed`), so the strengthened quiet predicate (`quietRX`) no longer needs `AdmDownR`; the root context is `hadm`. Remaining named premises: `hD` (class-D rows), `hG` (diagnostic rows), `hT` (telescope rows), `hs` (profile lookup along leaf steps), `h0` (profile lookup unset at the root start world). -/
theorem hftCoreCloses_of_kidsR''_k (L : LawsX mref cref) {w : Void IO.RealWorld}
    (hadm : L.O.adm mctx cctx) (hjq : JQ L.O.quiet 0 w) (hcell : CellPrem MkRefd mref cref) {lvl : Lean.Expr → Nat}
    (hrH : RootReader lvl (envAt cref w) hftHttp httpGetByte.machineData)
    (hrT : RootReader lvl (envAt cref w) hftTlp tlpCplByte.machineData)
    (hg : HftKidsGates (envAt cref w))
    (hD : DRowEnvRX L.O (envAt cref w) w)
    (hG : DiagEnvRX L.O (envAt cref w) w) (hT : TeleRX L.O (envAt cref w) w)
    (hs : ProfStepRX L.O w) (h0 : ProfOffW mref cref w) :
    HftCoreCloses mctx mref cctx cref w :=
  hftCoreCloses_of_kidsRX_k L hjq hcell hrH hrT hg hadm hD hG hT hs h0

end Tools.ShippingFGCircuitS2sAdmS2nAdm

namespace Tools.ShippingFGCircuitS3cTop
open Tools.ShippingChildVCA (JQ)
open Lean Sparkle.Compiler.Elab Sparkle.Core Sparkle.Core.Domain Tools.ShippingGen2 Tools.ShippingGen5DeclConnect Tools.ShippingGen5FG
open Tools.ShippingFGCircuit Tools.ShippingFGCircuitRoots Tools.ShippingFGCircuitArtifact Tools.ShippingFGCircuitCover Tools.ShippingFGCircuitBridge
open Tools.ShippingGenFGLedgerPremises Tools.ShippingFGCircuitS1iHead Tools.ShippingFGCircuitS1iEnv
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingEntryReadsLinked (envAt)
open Tools.ShippingGen5EnvFrame3 (CellPrem)
open Tools.ShippingChildFresh (MkRefd)
open Tools.ShippingChildBndCore (cv dv)
open Tools.ShippingChildCacheA (RealChildA)
open Tools.ShippingFGCircuitS1kRoot Tools.ShippingFGCircuitS1kStmt Tools.ShippingFGCircuitS1kPkg
open Tools.ShippingFGCircuitS1qLinked Tools.ShippingFGCircuitS1qEndpoint Tools.ShippingFGCircuitS1qHead
open Tools.ShippingFGCircuitS1tFinal Tools.ShippingFGCircuitS1uSrc Tools.ShippingFGCircuitS1zClose Tools.ShippingFGCircuitS2aClose
open Tools.ShippingFGCircuitS2dKids Tools.ShippingFGCircuitS2gGates Tools.ShippingFGCircuitS2jKid Tools.ShippingFGCircuitS2jTop
open Tools.ShippingFGCircuitS2hHist Tools.ShippingFGCircuitS2kRun
open Tools.ShippingFGCircuitS1oHead (GetEnvProfileAt headAt_of_profileOff)
open Tools.ShippingFGCircuitS1hFrame (getEnvFrame_of_cellPrem)
open Sparkle.IP.Net.HTTP Sparkle.IP.Bus.PCIe
open Meta Sparkle.IR.AST Sparkle.IR.Machine Tools.ShippingMachineEntry Tools.ShippingMachineAuto Tools.ShippingMixedSourceBridge Tools.ShippingUnifiedSource
open Tools.ShippingChildInvA (RefLawsAOps RefLawsATele AdmCtx)
open Tools.ShippingChildInv (Res)
open Tools.ShippingFGCircuitFinal4 (EntryGates)

open Tools.ShippingFGCircuitS2mReach
open Tools.ShippingFGCircuitS2kFinal (servedP_mono)
open Tools.ShippingFGCircuitS2lDec (hftCallDec_of_checked)
open Tools.ShippingChildCacheA (JQC CacheInvA)
open Tools.ShippingChildVCA (JQ)
open Tools.ShippingGen5Env (readsAt_self)

open Tools.ShippingFGCircuitS2hHist Tools.ShippingFGCircuitS2kRun Tools.ShippingFGCircuitS2jKid
open Tools.ShippingGen2 (Laws LawsX Start StartX)
open Tools.ShippingChildInvA Tools.ShippingChildCacheA
open Tools.ShippingFGCircuitS2sAdmS2nAdm
section Main
variable {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

/-- **`htop` from the run, X version** (`hftTop_of_runR` of S2r on the context-predicate bundle): the premises are `hadm hjq hcell hchk hreadH hreadT hkgfacts` and the run-local hypotheses `hD hG hT hs h0`, each with its own range: `hD` and `hG` are the X forms `DRowEnvRX`, `DiagEnvRX` at `L.toX.O`; `hs` is `ProfStepRX`, a leaf step from a reached world keeps the profile lookup unset; `hT` is `TeleRX`, a quantification over the telescope law (not a single run-local fact); `h0` is `ProfOffW`, the profile lookup is unset at the start world `w` itself; the run and the served children are at the history bundle `ropsRX L.toX.O`, whose context predicate is `AdmCtx L.O.quiet` itself, so there is no `hadm` and no `hdown`. `hdec` is not a premise: it is `hftCallDec_of_checked` with `hfind` from the core run `hrun` of the actual root run (`root_find_of_headAtOff` of the `hcell`-derived `HeadAtOff`). -/
theorem hftTop_of_runRX_k (L : Laws mref cref) (lvl : Lean.Expr → Nat) (env₀ : Environment)
    {mctx : Meta.Context} {cctx : Core.Context} {w : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (hadm : AdmCtx L.O.quiet mctx cctx) (hjq : JQ L.O.quiet 0 w) (hcell : CellPrem MkRefd mref cref)
    (hchk : CheckedStart lvl env₀ cref w hftRoot hftRootType hftRootValue synth_hftPcieOutByte.machineData)
    (hreadH : RootReader lvl (envAt cref w) hftHttp httpGetByte.machineData)
    (hreadT : RootReader lvl (envAt cref w) hftTlp tlpCplByte.machineData)
    (hkgfacts : HftKidsGateFacts (envAt cref w))
    (hD : DRowEnvRX L.toX.O (envAt cref w) w)
    (hG : DiagEnvRX L.toX.O (envAt cref w) w) (hT : TeleRX L.toX.O (envAt cref w) w)
    (hs : ProfStepRX L.toX.O w) (h0 : ProfOffW mref cref w) :
    ∀ p : Pkg ι (fun _ => defaultDomain), GPt (ι := ι) lvl (envAt cref w) hftRoot = some p → HftObTopCoreOff mctx mref cctx cref w b D' p := by
  intro p hP hdRun raw D₀ w1 hrun hpe
  have hg : HftKidsGates (envAt cref w) := hftKidsGates_of_facts hkgfacts
  have hhead : HeadAtOff hftRoot mctx mref cctx cref w := headAtOff_of_cellPrem _ hcell
  obtain ⟨hgates, ⟨d, hE⟩, hRead⟩ := startFacts_of_checked hchk (root_find_of_headAtOff hhead hrun)
  obtain ⟨E, hEnt, hsh, hdat⟩ := hRead
  obtain ⟨g, hgr, hgd⟩ := canon_row (lvl := lvl) (env := envAt cref w) root_wf hsh hdat
  obtain ⟨Eh, hEh, hshh, hdath⟩ := id hreadH
  obtain ⟨gh, hgh, hghd⟩ := canon_row (lvl := lvl) (env := envAt cref w) http_wf hshh hdath
  obtain ⟨Et, hEt, hsht, hdatt⟩ := id hreadT
  obtain ⟨gt, hgt, hgtd⟩ := canon_row (lvl := lvl) (env := envAt cref w) tlp_wf hsht hdatt
  have hkids : ∀ c ∈ g.d.shape.insts.map (·.1), ∃ (Ec : ConstantInfo) (gc : Tools.ShippingGen5Sem.GenData (Tools.ShippingGen5DataOf.dataOfAt lvl) Ec (structEnv (envAt cref w))),
      Tools.ShippingGen5Acc.entry₀ (envAt cref w) c = some Ec ∧ canonGD lvl (envAt cref w) Ec = some gc ∧ gc.d.shape.insts = [] := by
    intro c hc
    rw [hgd, root_insts] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact ⟨Eh, gh, hEh, hgh, by rw [hghd]; exact http_leaf⟩
    · exact ⟨Et, gt, hEt, hgt, by rw [hgtd]; exact tlp_leaf⟩
  obtain ⟨p', hP', hdecl, hpd, hkp⟩ := genGP_root_kids (ι := ι) (dom := fun _ => defaultDomain) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) (envAt cref w) hEnt hgr hkids
  obtain rfl : p' = p := Option.some.inj (hP'.symm.trans hP)
  rw [hgd] at hpd
  have hkD : p'.kD = 5 := by rw [hkp, hgd]; exact root_kD
  -- the two children's packages are `.comb` rows of the same table
  obtain ⟨cpH, hPH, hdeclH, hdH, hkH⟩ := kid_pkg (ι := ι) lvl (envAt cref w) hreadH http_wf http_leaf http_ss
  obtain ⟨cpT, hPT, hdeclT, hdT, hkT⟩ := kid_pkg (ι := ι) lvl (envAt cref w) hreadT tlp_wf tlp_leaf tlp_ss
  -- the children's actual results ship (from the reads their own run saved)
  have hkidH : ∀ y, RealChildEX (ropsRX L.toX.O hcell (envAt cref w) w hD hG) (KidEv mref cref (envAt cref w)) hftHttp y → ShipsRes L (GPt (ι := ι) lvl (envAt cref w)) hftHttp y := fun y h =>
    kid_shipsResWX (lvl := lvl) (e := envAt cref w) L (ropsRX L.toX.O hcell (envAt cref w) w hD hG) hT (fun _ h => h.1) (fun _ _ h => h) hcell (nDecl := httpGetByte.machineData.nIn) httpGetByte.machineData httpGetByte.machine_ok httpGetByte.machine_body
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ⟨_, rfl, rfl⟩ (by decide +kernel)
      hreadH hg.1 (fun mc cc => httpGetByte.machine_closes mc _ cc _) (GPt (ι := ι) lvl (envAt cref w)) cpH hPH hdeclH hdH
      (leafDataOk_comb cpH hdH hkH http_leafData) h
  have hkidT : ∀ y, RealChildEX (ropsRX L.toX.O hcell (envAt cref w) w hD hG) (KidEv mref cref (envAt cref w)) hftTlp y → ShipsRes L (GPt (ι := ι) lvl (envAt cref w)) hftTlp y := fun y h =>
    kid_shipsResWX (lvl := lvl) (e := envAt cref w) L (ropsRX L.toX.O hcell (envAt cref w) w hD hG) hT (fun _ h => h.1) (fun _ _ h => h) hcell (nDecl := tlpCplByte.machineData.nIn) tlpCplByte.machineData tlpCplByte.machine_ok tlpCplByte.machine_body
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ⟨_, rfl, rfl⟩ (by decide +kernel)
      hreadT hg.2 (fun mc cc => tlpCplByte.machine_closes mc _ cc _) (GPt (ι := ι) lvl (envAt cref w)) cpT hPT hdeclT hdT
      (leafDataOk_comb cpT hdT hkT tlp_leafData) h
  -- the names of the calls
  have hmapP : p'.d.shape.insts.map (·.1) = [hftHttp, hftTlp] := by rw [hpd]; exact root_insts
  have hk01 : ∀ (k : Nat) (hk : k < p'.d.shape.insts.length),
      ((p'.d.shape.insts[k]).1 = hftHttp ∧ k = 0) ∨ ((p'.d.shape.insts[k]).1 = hftTlp ∧ k = 1) := by
    intro k hk
    have hlen : p'.d.shape.insts.length = 2 := by have := congrArg List.length hmapP; simpa using this
    have h1 := congrArg (fun l => l[k]?) hmapP
    simp only [List.getElem?_map, List.getElem?_eq_getElem hk] at h1
    have hk2 : k < 2 := hlen ▸ hk
    rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
    · left; exact ⟨Option.some.inj (by simpa using h1), rfl⟩
    · right; exact ⟨Option.some.inj (by simpa using h1), rfl⟩
  have hkid : ∀ (k : Nat) (hk : k < p'.d.shape.insts.length) (mc : Sparkle.IR.AST.Module) (Dc : Sparkle.IR.AST.Design),
      RealChildEX (ropsRX L.toX.O hcell (envAt cref w) w hD hG) (KidEv mref cref (envAt cref w)) (p'.d.shape.insts[k]).1 (mc, Dc) → ShipsRes L (GPt (ι := ι) lvl (envAt cref w)) (p'.d.shape.insts[k]).1 (mc, Dc) := by
    intro k hk mc Dc h
    rcases hk01 k hk with ⟨hn, -⟩ | ⟨hn, -⟩
    · rw [hn] at h ⊢; exact hkidH _ h
    · rw [hn] at h ⊢; exact hkidT _ h
  -- the machine run of the root, from the history world at the head of the run
  have hdv : dv w = 0 := hjq.2.2
  have ranH : MachineRunJQHX (ropsRX L.toX.O hcell (envAt cref w) w hD hG) (KidEv mref cref (envAt cref w)) mctx cctx (0 + 1) hftRoot synth_hftPcieOutByte.machineData.shape raw D₀ :=
    machineRunJQH_of_closesHOffX (ropsRX L.toX.O hcell (envAt cref w) w hD hG) hadm hrun (hdRun raw D₀ w1)
      (hft_closesAtHX (ropsRX L.toX.O hcell (envAt cref w) w hD hG) hT hadm hcell hreadH hreadT hg (missRX h0 hs))
      ⟨⟨hjq.1, readsAt_self cref w, .start⟩, hjq.2⟩
  have ranR : MachineTaken L mctx cctx (dv w + 1) hftRoot synth_hftPcieOutByte.machineData.shape raw D₀ := by
    rw [hdv]
    obtain ⟨tenv, b', w9, w10, hrun9, hw9⟩ := ranH.toCX
    exact ⟨tenv, b', w9, w10, hrun9, jqcX_weak (O' := ropsRX L.toX.O hcell (envAt cref w) w hD hG) (O := L.O) (fun _ h => h.1) (fun _ _ h => h) hw9⟩
  have ranP : MachineTaken L mctx cctx (dv w + 1) p'.decl p'.d.shape raw D₀ := by rw [hdecl, hpd]; exact ranR
  have ranHP : MachineRunJQHX (ropsRX L.toX.O hcell (envAt cref w) w hD hG) (KidEv mref cref (envAt cref w)) mctx cctx (0 + 1) p'.decl p'.d.shape raw D₀ := by rw [hdecl, hpd]; exact ranH
  -- the trace with the served children shipping
  have hL : Tools.ShippingMachineTraceX.MachineTraceLBX (ServedP (ShipsRes L (GPt (ι := ι) lvl (envAt cref w))) p'.decl p'.d.shape raw D₀)
      p'.decl p'.d raw D₀ (fun _ => defaultDomain) p'.src p'.extS p'.extBS p'.lsrc :=
    traceLBX_mono (fun _ _ hX => servedP_mono hkid hX)
      (Pkg.traceX p' (soundX_served_EX (ropsRX L.toX.O hcell (envAt cref w) w hD hG) hT (missRX h0 hs) hadm (by omega) ranHP))
  -- the one-output widths
  have hW : ∀ k, OneOutWidth (GPt (ι := ι) lvl (envAt cref w)) p' k := by
    intro k hk q hq o ho
    rw [hpd, hkD]
    rcases hk01 k hk with ⟨hn, rfl⟩ | ⟨hn, rfl⟩
    · rw [hn] at hq
      obtain rfl : q = Pkg.comb cpH := (Option.some.inj ((show GPt (ι := ι) lvl (envAt cref w) hftHttp = some (Pkg.comb cpH) from hPH).symm.trans hq)).symm
      exact hft_width0 o (by have : (Pkg.comb cpH).d.shape.layout.outs = [o] := ho; rw [show (Pkg.comb cpH).d = cpH.d from rfl, hdH] at this; rw [this]; exact List.mem_singleton_self o)
    · rw [hn] at hq
      obtain rfl : q = Pkg.comb cpT := (Option.some.inj ((show GPt (ι := ι) lvl (envAt cref w) hftTlp = some (Pkg.comb cpT) from hPT).symm.trans hq)).symm
      exact hft_width1 o (by have : (Pkg.comb cpT).d.shape.layout.outs = [o] := ho; rw [show (Pkg.comb cpT).d = cpT.d from rfl, hdT] at this; rw [this]; exact List.mem_singleton_self o)
  have hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw) :=
    hpe.imp And.left And.left
  have key := oneOut_topShipsOff L (GPt (ι := ι) lvl (envAt cref w)) p' (mctx := mctx) (cctx := cctx) (w := w) (w1 := w1) (raw := raw) (b := b) (D := D₀)
    (by unfold MemParentDataOk MemParentDataOkB; rw [hpd, hkD]; exact hft_memData)
    (fun k hk => by rw [hpd]; exact hft_ord k (by rw [← hpd]; exact hk))
    (by rw [hpd]; exact hft_insts_ne) (by rw [hpd]; exact hft_instFields) (by rw [hpd]; exact hft_slots_ne) hadm
    (by rw [hdecl]; exact hrun) hpost (by rw [hdecl, hpd]; exact hdRun raw D₀ w1) ranP (hftCallDec_of_checked (ι := ι) (mref := mref) lvl env₀ hchk (root_find_of_headAtOff hhead hrun) hreadH hreadT p' hP) hL hW 0
  exact ⟨0 + 1, by rw [← hdecl]; exact key⟩

end Main
end Tools.ShippingFGCircuitS3cTop

namespace Tools.ShippingFGCircuitS3cFinal
open Tools.ShippingChildVCA (JQ)
open Lean Sparkle.Compiler.Elab Sparkle.Core Sparkle.Core.Domain Tools.ShippingGen2 Tools.ShippingGen5DeclConnect Tools.ShippingGen5FG
open Tools.ShippingFGCircuit Tools.ShippingFGCircuitRoots Tools.ShippingFGCircuitArtifact Tools.ShippingFGCircuitCover Tools.ShippingFGCircuitBridge
open Tools.ShippingGenFGLedgerPremises Tools.ShippingFGCircuitS1iHead Tools.ShippingFGCircuitS1iEnv
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingEntryReadsLinked (envAt)
open Tools.ShippingGen5EnvFrame3 (CellPrem)
open Tools.ShippingChildFresh (MkRefd)
open Tools.ShippingChildBndCore (cv dv)
open Tools.ShippingChildCacheA (RealChildA)
open Tools.ShippingFGCircuitS1kRoot Tools.ShippingFGCircuitS1kStmt Tools.ShippingFGCircuitS1kPkg
open Tools.ShippingFGCircuitS1qLinked Tools.ShippingFGCircuitS1qEndpoint Tools.ShippingFGCircuitS1qHead
open Tools.ShippingFGCircuitS1tFinal Tools.ShippingFGCircuitS1uSrc Tools.ShippingFGCircuitS1zClose Tools.ShippingFGCircuitS2aClose
open Tools.ShippingFGCircuitS2dKids Tools.ShippingFGCircuitS2gGates Tools.ShippingFGCircuitS2jKid Tools.ShippingFGCircuitS2jTop
open Tools.ShippingFGCircuitS2hHist Tools.ShippingFGCircuitS2kRun
open Tools.ShippingFGCircuitS1oHead (GetEnvProfileAt headAt_of_profileOff)
open Tools.ShippingFGCircuitS1hFrame (getEnvFrame_of_cellPrem)
open Sparkle.IP.Net.HTTP Sparkle.IP.Bus.PCIe
open Meta Sparkle.IR.AST Sparkle.IR.Machine Tools.ShippingMachineEntry Tools.ShippingMachineAuto Tools.ShippingMixedSourceBridge Tools.ShippingUnifiedSource
open Tools.ShippingChildInvA (RefLawsAOps RefLawsATele AdmCtx)
open Tools.ShippingChildInv (Res)
open Tools.ShippingFGCircuitFinal4 (EntryGates)

open Tools.ShippingFGCircuitS1xNoRaw Tools.ShippingFGCircuitS1mCD Tools.ShippingFGCircuitS1pCD Tools.ShippingFGCircuitS1rCD
open Tools.ShippingFGCircuitS2mReach
open Tools.ShippingFGCircuitS2rFinal (synth_hftPcieOutByte_finalOffCombined2 HftFinalStmtOffCombined2)

open Tools.ShippingFGCircuitS2vLink (HftFinalStmtOffCombined3 synth_hftPcieOutByte_finalOffCombined3)
open Tools.ShippingFGCircuitS2tHft (hftObCDT_T)
open Tools.ShippingFGCircuitS1wTbl (RecFact)
open Tools.ShippingFGCircuitS2iTbl

open Tools.ShippingFGCircuitS2yFinal (cdvT HftFinalStmtOffCombined4 synth_hftPcieOutByte_finalOffCombined4)
open Tools.ShippingFGCircuitS1qLinked (core_envOkOff)
open Tools.ShippingFGCircuitS1qEndpoint (postEntryOff)
open Tools.ShippingFGCircuitS1qHead (headAtOff_of_cellPrem)
open Tools.ShippingEnvSnapshot (envFrame_getConstInfo)
open Tools.ShippingFGCircuitS1hFrame (getEnvFrame_of_cellPrem)

open Tools.ShippingFGCircuitS2zFinal (HftFinalStmtOffCombined5 synth_hftPcieOutByte_finalOffCombined5 startEnvOk_of_run)

open Tools.ShippingFGCircuitS3aFinal (startKidsOk_of_run)
open Tools.ShippingFGCircuitS3cTop
open Tools.ShippingFGCircuitS2sAdmS2nAdm
open Tools.ShippingFGCircuitS2zFinal (startEnvOk_of_run)
open Tools.ShippingFGCircuitS1zClose (synth_hftPcieOutByte_finalOffLNLX)
open Tools.ShippingGen2 (LawsX StartX)
open Tools.ShippingChildInvA Tools.ShippingChildCacheA
/-- **v7**: v6 with `hadm` and `hdown` REMOVED (14 binders). `hD hG hs` keep their v6 propositions; `hT` is the telescope law in its context-predicate form `TeleRX` (contexts `AdmCtx quiet`, not `AdmCtx (quietR ..)`): this is the one premise whose proposition differs from v6's `TeleR` (docs S52) -/
def HftFinalStmtOffCombined7_k : Prop :=
  ∀ {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (lvl : Lean.Expr → Nat) (env₀ : Environment)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (hadm : AdmCtx L.O.quiet mctx cctx) (hjq : JQ L.O.quiet 0 w)
    (hr : RunsTo (synthesizeCombinationalOff hftRoot) mctx mref cctx cref w (b, D') w')
    (hcell : CellPrem Tools.ShippingChildFresh.MkRefd mref cref)
    (hchk : CheckedStart lvl env₀ cref w hftRoot hftRootType hftRootValue synth_hftPcieOutByte.machineData)
    (hreadH : RootReader lvl (envAt cref w) hftHttp Sparkle.IP.Net.HTTP.httpGetByte.machineData)
    (hreadT : RootReader lvl (envAt cref w) hftTlp Sparkle.IP.Bus.PCIe.tlpCplByte.machineData)
    (hD : DRowEnvR L.O (envAt cref w) w)
    (hG : DiagEnvR L.O (envAt cref w) w) (hT : TeleRX L.toX.O (envAt cref w) w)
    (hs : ProfStepR L.O w) (h0 : ProfOffW mref cref w),
    (∃ raw, PostRunOff mctx mref cctx cref w hftRoot D' b raw) ∧
    ∃ (mm : MonoTy shHft) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMonoV cdvT (envAt cref w) (GPt (ι := ι) lvl (envAt cref w))
        (PostRunOff mctx mref cctx cref w hftRoot D') hftRoot shHft mm b D' p

theorem synth_hftPcieOutByte_finalOffCombined7_k : HftFinalStmtOffCombined7_k := by
  intro ι mref cref L lvl env₀ mctx cctx w w' b D' hadm hjq hr hcell hchk hRdH hRdT hD hG hT hs h0
  have hkg := Tools.ShippingFGCircuitS3aKids.startKidsOk_sound (startKidsOk_of_run hcell hr)
  obtain ⟨hΔ, hΓ, hrec⟩ := Tools.ShippingFGCircuitS2zPin.startEnvOk_sound (startEnvOk_of_run hcell hr)
  have hD' := drowEnvRX_of_R L hD
  have hG' := diagEnvRX_of_R L hG
  have hs' := profStepRX_of_R L hs
  exact synth_hftPcieOutByte_finalOffLNLX_k cdvT Tools.ShippingFGCircuitS2oOb.HftObCDT (fun _ h => h)
    Tools.ShippingFGCircuitS2kLink.hftRootLink L.toX lvl env₀ hadm hjq hr hcell hchk hRdH hRdT
    (hftObCDT_T _ hΔ hΓ hrec)
    (hftTop_of_runRX_k L lvl env₀ hadm hjq hcell hchk hRdH hRdT hkg hD' hG' hT hs' h0)
    (hftCoreCloses_of_kidsR''_k L.toX hadm hjq hcell hRdH hRdT (hftKidsGates_of_facts hkg) hD' hG' hT hs' h0)

end Tools.ShippingFGCircuitS3cFinal

namespace Tools.ShippingFGCircuitS3f2Final
open Tools.ShippingChildVCA (JQ)
open Lean Sparkle.Compiler.Elab Sparkle.Core Sparkle.Core.Domain Tools.ShippingGen2 Tools.ShippingGen5DeclConnect Tools.ShippingGen5FG
open Tools.ShippingFGCircuit Tools.ShippingFGCircuitRoots Tools.ShippingFGCircuitArtifact Tools.ShippingFGCircuitCover Tools.ShippingFGCircuitBridge
open Tools.ShippingGenFGLedgerPremises Tools.ShippingFGCircuitS1iHead Tools.ShippingFGCircuitS1iEnv
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingEntryReadsLinked (envAt)
open Tools.ShippingGen5EnvFrame3 (CellPrem)
open Tools.ShippingChildFresh (MkRefd)
open Tools.ShippingChildBndCore (cv dv)
open Tools.ShippingChildCacheA (RealChildA)
open Tools.ShippingFGCircuitS1kRoot Tools.ShippingFGCircuitS1kStmt Tools.ShippingFGCircuitS1kPkg
open Tools.ShippingFGCircuitS1qLinked Tools.ShippingFGCircuitS1qEndpoint Tools.ShippingFGCircuitS1qHead
open Tools.ShippingFGCircuitS1tFinal Tools.ShippingFGCircuitS1uSrc Tools.ShippingFGCircuitS1zClose Tools.ShippingFGCircuitS2aClose
open Tools.ShippingFGCircuitS2dKids Tools.ShippingFGCircuitS2gGates Tools.ShippingFGCircuitS2jKid Tools.ShippingFGCircuitS2jTop
open Tools.ShippingFGCircuitS2hHist Tools.ShippingFGCircuitS2kRun
open Tools.ShippingFGCircuitS1oHead (GetEnvProfileAt headAt_of_profileOff)
open Tools.ShippingFGCircuitS1hFrame (getEnvFrame_of_cellPrem)
open Sparkle.IP.Net.HTTP Sparkle.IP.Bus.PCIe
open Meta Sparkle.IR.AST Sparkle.IR.Machine Tools.ShippingMachineEntry Tools.ShippingMachineAuto Tools.ShippingMixedSourceBridge Tools.ShippingUnifiedSource
open Tools.ShippingChildInvA (RefLawsAOps RefLawsATele AdmCtx)
open Tools.ShippingChildInv (Res)
open Tools.ShippingFGCircuitFinal4 (EntryGates)

open Tools.ShippingFGCircuitS1xNoRaw Tools.ShippingFGCircuitS1mCD Tools.ShippingFGCircuitS1pCD Tools.ShippingFGCircuitS1rCD
open Tools.ShippingFGCircuitS2mReach
open Tools.ShippingFGCircuitS2rFinal (synth_hftPcieOutByte_finalOffCombined2 HftFinalStmtOffCombined2)

open Tools.ShippingFGCircuitS2vLink (HftFinalStmtOffCombined3 synth_hftPcieOutByte_finalOffCombined3)
open Tools.ShippingFGCircuitS2tHft (hftObCDT_T)
open Tools.ShippingFGCircuitS1wTbl (RecFact)
open Tools.ShippingFGCircuitS2iTbl

open Tools.ShippingFGCircuitS2yFinal (cdvT HftFinalStmtOffCombined4 synth_hftPcieOutByte_finalOffCombined4)
open Tools.ShippingFGCircuitS1qLinked (core_envOkOff)
open Tools.ShippingFGCircuitS1qEndpoint (postEntryOff)
open Tools.ShippingFGCircuitS1qHead (headAtOff_of_cellPrem)
open Tools.ShippingEnvSnapshot (envFrame_getConstInfo)
open Tools.ShippingFGCircuitS1hFrame (getEnvFrame_of_cellPrem)

open Tools.ShippingFGCircuitS2zFinal (HftFinalStmtOffCombined5 synth_hftPcieOutByte_finalOffCombined5 startEnvOk_of_run)

open Tools.ShippingFGCircuitS3aFinal (startKidsOk_of_run)
open Tools.ShippingFGCircuitS3cTop
open Tools.ShippingFGCircuitS2sAdmS2nAdm
open Tools.ShippingFGCircuitS2zFinal (startEnvOk_of_run)
open Tools.ShippingFGCircuitS1zClose (synth_hftPcieOutByte_finalOffLNLX)
open Tools.ShippingGen2 (LawsX StartX)
open Tools.ShippingChildInvA Tools.ShippingChildCacheA
open Tools.ShippingFGCircuitS3b2Reader (lvl₀ rootReaderB rootReaderB_sound)
open Tools.ShippingFGCircuitS1hGates (entryGatesB entryGatesB_sound)
open Tools.ShippingFGCircuitS3f2Exp (rootMD rootMD_eq)
open Tools.ShippingFGCircuitS3b2Final (pilotReaderOk pilotReaderOk_sound readerOk_of_run)
open Tools.ShippingFGCircuitS3b2Core (offR_to_off)
open Tools.ShippingFGCircuitS3cFinal (synth_hftPcieOutByte_finalOffCombined7_k)

/-- **v9, copied (`_k`)** (10 binders: v9 with `hstart` split into `hadm` and the JQ-only `hjq`): the pilot entry `pilotReaderOk2` (`hr` is a run of `synthesizeCombinationalOffR pilotReaderOk2 hftRoot`) at the concrete `lvl₀`, WITHOUT `env₀` and `hchk`: `env₀` is `envAt cref w` and `hchk` is supplied by the run's own guard.  Binders: `L hadm hjq hr hcell hD hG hT hs h0`. -/
def HftFinalStmtOffCombined9_k : Prop :=
  ∀ {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (hadm : AdmCtx L.O.quiet mctx cctx) (hjq : JQ L.O.quiet 0 w)
    (hr : RunsTo (synthesizeCombinationalOffR pilotReaderOk2 hftRoot) mctx mref cctx cref w (b, D') w')
    (hcell : CellPrem Tools.ShippingChildFresh.MkRefd mref cref)
    (hD : DRowEnvR L.O (envAt cref w) w)
    (hG : DiagEnvR L.O (envAt cref w) w) (hT : TeleRX L.toX.O (envAt cref w) w)
    (hs : ProfStepR L.O w) (h0 : ProfOffW mref cref w),
    (∃ raw, PostRunOff mctx mref cctx cref w hftRoot D' b raw) ∧
    ∃ (mm : MonoTy shHft) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMonoV cdvT (envAt cref w) (GPt (ι := ι) lvl₀ (envAt cref w))
        (PostRunOff mctx mref cctx cref w hftRoot D') hftRoot shHft mm b D' p

/-- **v9 from v7**: `env₀ := envAt cref w`, so `ReadsAt` is `readsAt_self`; `CheckedEnv` and the children's readers come from `pilotReaderOk2_sound` at the run's own start environment (`readerOk_of_run`); the run is the existing Off run (`offR_to_off`) -/
theorem synth_hftPcieOutByte_finalOffCombined9_k : HftFinalStmtOffCombined9_k := by
  intro ι mref cref L mctx cctx w w' b D' hadm hjq hr hcell hD hG hT hs h0
  obtain ⟨-, hH, hT', hCE⟩ := pilotReaderOk2_sound (readerOk_of_run hcell hr)
  exact synth_hftPcieOutByte_finalOffCombined7_k L lvl₀ (envAt cref w) hadm hjq (offR_to_off hr) hcell ⟨hCE, Tools.ShippingGen5Env.readsAt_self cref w⟩ hH hT' hD hG hT hs h0

end Tools.ShippingFGCircuitS3f2Final

#print axioms Tools.ShippingFGCircuitS1tFinal.synth_hftPcieOutByte_finalOffX_k
#print axioms Tools.ShippingFGCircuitS1uSrc.synth_hftPcieOutByte_finalOffLX_k
#print axioms Tools.ShippingFGCircuitS1zClose.coreOff_ranAX_k
#print axioms Tools.ShippingFGCircuitS1zClose.hftPostGate_of_localX_k
#print axioms Tools.ShippingFGCircuitS1zClose.hftObNoRawOff_of_localX_k
#print axioms Tools.ShippingFGCircuitS1zClose.synth_hftPcieOutByte_finalOffLNLX_k
#print axioms Tools.ShippingFGCircuitS2mReach.hftCoreCloses_of_kidsRX_k
#print axioms Tools.ShippingFGCircuitS2sAdmS2nAdm.hftCoreCloses_of_kidsR''_k
#print axioms Tools.ShippingFGCircuitS3cTop.hftTop_of_runRX_k
#print axioms Tools.ShippingFGCircuitS3cFinal.synth_hftPcieOutByte_finalOffCombined7_k
#print axioms Tools.ShippingFGCircuitS3f2Final.synth_hftPcieOutByte_finalOffCombined9_k
