import Tools.ShippingFGCircuitS1uSrc
import Tools.ShippingGen5DCEntryS
import Tools.ShippingChecksDepthGate
set_option autoImplicit false
-- FG circuit pilot S1x: `hnoraw` for the non-leaf root `synth_hftPcieOutByte`, from the run of `synthesizeCombinationalCoreOff`. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED, no new law. Results: docs/FG-CIRCUIT-PILOT.md §26.

/-! # S1x: `NoRawBelow` (at every depth) from the run

`HftObNoRawOff` (S1t) asks, for the core run `(raw, D₀)` and the printed pair `(b, D')`:
(1) `∀ n, NoRawBelow D₀ raw.name (n+1) raw`, (2) `∀ n, NoRawBelow D₀ raw.name (n+1) (checkedOptimize b)`, (3) no instance of `b.body` names `raw.name`.

* **Part A (the run)**: the core run of a machine with calls ends in `closeInsts`/`closeInstsG`, whose last check is `noInstOfB m.name body && d'.modules.all (noInstOfB m.name ·.body)`.
  `coreOff_closed`: from the run, the machine boundary `MachineDefinesLinkedOff` and `MachineCloses` (the closing is not `none`), the result `(raw, D₀)` satisfies `NoInstOf raw.name raw.body` and `NoInstOf raw.name g.body` for every `g ∈ D₀.modules`.
  Hence `NoRawBelow` at EVERY depth (`noRawBelow_of_noInstOf`), not a snapshot.
* **Part B (the post-processing)**: `b` is `dropZeroWidthModule raw` or the checked merge of it; both keep the instance targets (`post_inst_target`). `checkedOptimize b` keeps `b`'s instance statements under the statement gate `hierGate b`
  (`checkedOptimize_inst_iff_gate`). `hierGate b` is a named premise (`HftPostGate`).
* **Part C**: `hftObNoRawOff_of_run`, and the final statement `HftFinalStmtOffLN` with `hnoraw` replaced by `hcl` and `hgate`. -/
namespace Tools.ShippingFGCircuitS1xNoRaw
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
open Tools.ShippingFGCircuitS1tFinal Tools.ShippingFGCircuitS1uSrc
open Tools.ShippingGen5DCEntryR (NoRawBelow)
open Tools.ShippingGen5DCEntryD (PostEntry)
open Tools.ShippingHierMono (NoInstOf)
open Tools.ShippingMachineEntry Tools.ShippingFGCircuitRunLocal

/-! ## Part A: the run -/
section RunPart
variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- **the core run of a machine with calls ends in the closing**: its result `(m, d)` has no instance of `m.name`, in `m` and in every module of `d`.
Premises: the run, the machine boundary of that run (`MachineDefinesLinkedOff`), `MachineCloses` (the closing is not `none`), and `shape.insts ≠ []` -/
theorem coreOff_closed {declName : Name} {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design} {shape : MachineShape}
    (hr : RunsTo (synthesizeCombinationalCoreOff declName) mctx mref cctx cref w (m, d) w')
    (entry : MachineDefinesLinkedOff mctx mref cctx cref declName shape w m d w')
    (closes : MachineCloses mctx mref cctx cref declName shape)
    (hI : shape.insts ≠ []) :
    NoInstOf m.name m.body ∧ ∀ g ∈ d.modules, NoInstOf m.name g.body := by
  obtain ⟨s, w1, envR, ci, w2, w3, w4, hh, hget, henv, hbody, -⟩ := core_chainOff hr
  obtain ⟨old, miss, hshape⟩ := entry hr s w1 w2 w3 w4 envR ci hh hget henv hbody
  obtain ⟨envR', w8, henv', hmach⟩ := synthesizeFromConst_machineR old miss hbody
  obtain ⟨r, w9, w10, hrun, hres⟩ := hmach shape (hshape _ _ henv')
  have hne := closes _ _ _ _ hrun
  cases r with
  | none => exact absurd rfl hne
  | some res =>
    have := hres res rfl
    subst this
    obtain ⟨t, t', d₀, -, -, hcase⟩ := synthesizeMachineCertified_returns hrun.mreturns
    rcases hcase with ⟨hi, -⟩ | ⟨-, children, hcc⟩
    · exact absurd hi hI
    · rcases hcc with ⟨-, hc⟩ | ⟨-, hc, -⟩
      · obtain ⟨-, h1, h2, -⟩ := Tools.ShippingChildServe.closeInsts_acyclic hc
        exact ⟨h1, h2⟩
      · obtain ⟨-, h1, h2⟩ := Tools.ShippingChildServe.closeInstsG_acyclic hc
        exact ⟨h1, h2⟩

/-- **`NoRawBelow` at every depth, from the run** -/
theorem coreOff_noRawBelow {declName : Name} {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design} {shape : MachineShape}
    (hr : RunsTo (synthesizeCombinationalCoreOff declName) mctx mref cctx cref w (m, d) w')
    (entry : MachineDefinesLinkedOff mctx mref cctx cref declName shape w m d w')
    (closes : MachineCloses mctx mref cctx cref declName shape)
    (hI : shape.insts ≠ []) :
    ∀ k, NoRawBelow d m.name k m := by
  obtain ⟨h1, h2⟩ := coreOff_closed hr entry closes hI
  exact fun k => Tools.ShippingGen5DCEntryS.noRawBelow_of_noInstOf h2 k m h1

end RunPart

/-! ## Part B: the post-processing keeps the instance targets -/

/-- the zero-width cleanup keeps the targets of the instance statements -/
theorem dropZeroWidth_inst_target (raw : Sparkle.IR.AST.Module) {mn iname : String} {conns : List (String × Sparkle.IR.AST.Expr)}
    (h : Sparkle.IR.AST.Stmt.inst mn iname conns ∈ (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw).body) :
    ∃ i' c', Sparkle.IR.AST.Stmt.inst mn i' c' ∈ raw.body := by
  unfold Sparkle.IR.ZeroWidth.dropZeroWidthModule at h
  split at h
  · exact ⟨iname, conns, h⟩
  · dsimp only at h
    obtain ⟨a, ha, hsa⟩ := List.mem_filterMap.mp h
    cases a with
    | assign l r =>
      unfold Sparkle.IR.ZeroWidth.dzStmt at hsa
      split at hsa <;> simp at hsa
    | register o c rs i iv => simp [Sparkle.IR.ZeroWidth.dzStmt] at hsa
    | memory .. => simp [Sparkle.IR.ZeroWidth.dzStmt] at hsa
    | inst mn' i' c' =>
      simp only [Sparkle.IR.ZeroWidth.dzStmt, Option.some.injEq, Sparkle.IR.AST.Stmt.inst.injEq] at hsa
      obtain ⟨rfl, -, -⟩ := hsa
      exact ⟨i', c', ha⟩

/-- **the printed top keeps the instance targets of the core module** -/
theorem post_inst_target {b raw : Sparkle.IR.AST.Module} {D D' : Sparkle.IR.AST.Design} (hpe : PostEntry b raw D D')
    {mn iname : String} {conns : List (String × Sparkle.IR.AST.Expr)}
    (h : Sparkle.IR.AST.Stmt.inst mn iname conns ∈ b.body) :
    ∃ i' c', Sparkle.IR.AST.Stmt.inst mn i' c' ∈ raw.body := by
  rcases hpe with ⟨hb, -⟩ | ⟨hb, -⟩
  · subst hb
    exact dropZeroWidth_inst_target raw h
  · have hI : Tools.ShippingMachineShipsHier.hasInst b := ⟨mn, iname, conns, h⟩
    have e := Tools.ShippingMachineShipsHier.mergeChecked_inst hb hI
    rw [e] at h
    exact dropZeroWidth_inst_target raw h

/-- no instance of `b` names the top, from the core module's `NoInstOf` -/
theorem noB_of_post {b raw : Sparkle.IR.AST.Module} {D D' : Sparkle.IR.AST.Design} (hpe : PostEntry b raw D D')
    (hraw : NoInstOf raw.name raw.body) :
    ∀ mn iname conns, Sparkle.IR.AST.Stmt.inst mn iname conns ∈ b.body → mn ≠ raw.name := by
  intro mn iname conns h
  obtain ⟨i', c', h'⟩ := post_inst_target hpe h
  exact hraw mn i' c' h'

/-- `NoRawBelow` for the printed module `checkedOptimize b`, under the statement gate of `b` -/
theorem noRawBelow_opt {b raw : Sparkle.IR.AST.Module} {D D₀ D' : Sparkle.IR.AST.Design} (hpe : PostEntry b raw D₀ D')
    (hraw : NoInstOf raw.name raw.body) (hD : ∀ g ∈ D.modules, NoInstOf raw.name g.body)
    (hg : Sparkle.IR.RefineCheck.hierGate b = true) :
    ∀ k, NoRawBelow D raw.name k (Sparkle.IR.OptCheck.checkedOptimize b) := by
  refine fun k => Tools.ShippingGen5DCEntryS.noRawBelow_of_noInstOf hD k _ ?_
  intro mn iname conns h
  exact noB_of_post hpe hraw mn iname conns
    ((Tools.ShippingChecksDepthGate.checkedOptimize_inst_iff_gate hg mn iname conns).mp h)

/-! ## Part C: `hnoraw` -/
section Supply
open Sparkle.Compiler.Elab (synthesizeCombinationalCoreOff)

/-- **the one premise on the post-processing**: the printed top `b` passes the statement gate of `checkedOptimize` (`hierGate b`: some statement is an instance and every statement is an instance or a normal-form one). Run-local, named (FG D.T-4) -/
def HftPostGate (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State) (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State)
    (w : Void IO.RealWorld) (b : Sparkle.IR.AST.Module) (D' : Sparkle.IR.AST.Design) : Prop :=
  ∀ (raw : Sparkle.IR.AST.Module) (D₀ : Sparkle.IR.AST.Design) (w1 : Void IO.RealWorld),
    RunsTo (synthesizeCombinationalCoreOff hftRoot) mctx mref cctx cref w (raw, D₀) w1 →
    PostEntry b raw D₀ D' → Sparkle.IR.RefineCheck.hierGate b = true

theorem hftShape_insts_ne : synth_hftPcieOutByte.machineData.shape.insts ≠ [] := by
  intro h
  have := root_insts_nonempty
  rw [h] at this
  exact absurd this (by decide)

/-- **`HftObNoRawOff` from the run**: the machine boundary of the core run (`MachineDefinesLinkedOff`), `MachineCloses` of the root's shape, and the gate of the printed top -/
theorem hftObNoRawOff_of_run {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {w : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (hdRun : ∀ raw D₀ w1, MachineDefinesLinkedOff mctx mref cctx cref hftRoot synth_hftPcieOutByte.machineData.shape w raw D₀ w1)
    (hcl : MachineCloses mctx mref cctx cref hftRoot synth_hftPcieOutByte.machineData.shape)
    (hgate : HftPostGate mctx mref cctx cref w b D') :
    HftObNoRawOff mctx mref cctx cref w b D' := by
  intro raw D₀ w1 hr hpe
  obtain ⟨h1, h2⟩ := coreOff_closed hr (hdRun raw D₀ w1) hcl hftShape_insts_ne
  refine ⟨fun n => Tools.ShippingGen5DCEntryS.noRawBelow_of_noInstOf h2 (n + 1) raw h1,
    fun n => noRawBelow_opt hpe h1 h2 (hgate raw D₀ w1 hr hpe) (n + 1), noB_of_post hpe h1⟩

/-- the final statement of S1u (`HftFinalStmtOffL`) with `hnoraw` replaced by `hcl` and `hgate` -/
def HftFinalStmtOffLN (Ob : Environment → Prop) (CV : CDRel) : Prop :=
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
    (hcl : MachineCloses mctx mref cctx cref hftRoot synth_hftPcieOutByte.machineData.shape)
    (hgate : HftPostGate mctx mref cctx cref w b D'),
    (∃ raw, PostRunOff mctx mref cctx cref w hftRoot D' b raw) ∧
    ∃ (mm : MonoTy shHft) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMonoV CV (envAt cref w) (GPt (ι := ι) lvl (envAt cref w))
        (PostRunOff mctx mref cctx cref w hftRoot D') hftRoot shHft mm b D' p

theorem synth_hftPcieOutByte_finalOffLN (CV : CDRel) (Ob : Environment → Prop) (hOb : ∀ env, Ob env → HftObOf CV env) :
    HftFinalStmtOffLN Ob CV := by
  intro hlink ι mref cref L lvl env₀ mctx cctx w w' b D' hstart hr hcell hchk hRdH hRdT hCD hTop hcl hgate
  have hhead : HeadAtOff hftRoot mctx mref cctx cref w := headAtOff_of_cellPrem _ hcell
  obtain ⟨raw, D₀, w1, hc, hpe⟩ := postEntryOff hr
  obtain ⟨hgates, ⟨d, hE⟩, hRead⟩ := startFacts_of_checked hchk (root_find_of_headAtOff hhead hc)
  have hdRun : ∀ raw D₀ w1, MachineDefinesLinkedOff mctx mref cctx cref hftRoot synth_hftPcieOutByte.machineData.shape w raw D₀ w1 :=
    fun _ _ _ => machineDefinesLinked_of_reader_headAtOff hhead (Tools.ShippingFGCircuitS1hFrame.getEnvFrame_of_readWorld hcell.2.2.2.2.2.2.2.2.1) hE hRead hgates
  exact synth_hftPcieOutByte_finalOffL CV Ob hOb hlink L lvl env₀ hstart hr hcell hchk hRdH hRdT hCD hTop
    (hftObNoRawOff_of_run hdRun hcl hgate)

theorem synth_hftPcieOutByte_finalOffLN_Z : HftFinalStmtOffLN HftObCDZ cdvZ := synth_hftPcieOutByte_finalOffLN cdvZ _ (fun _ h => h)
theorem synth_hftPcieOutByte_finalOffLN_Y : HftFinalStmtOffLN HftObCDY cdvY := synth_hftPcieOutByte_finalOffLN cdvY _ (fun _ h => h)
theorem synth_hftPcieOutByte_finalOffLN_X : HftFinalStmtOffLN HftObCDX cdvX := synth_hftPcieOutByte_finalOffLN cdvX _ (fun _ h => h)

end Supply

end Tools.ShippingFGCircuitS1xNoRaw

#print axioms Tools.ShippingFGCircuitS1xNoRaw.coreOff_closed
#print axioms Tools.ShippingFGCircuitS1xNoRaw.coreOff_noRawBelow
#print axioms Tools.ShippingFGCircuitS1xNoRaw.post_inst_target
#print axioms Tools.ShippingFGCircuitS1xNoRaw.noRawBelow_opt
#print axioms Tools.ShippingFGCircuitS1xNoRaw.hftObNoRawOff_of_run
#print axioms Tools.ShippingFGCircuitS1xNoRaw.synth_hftPcieOutByte_finalOffLN
#print axioms Tools.ShippingFGCircuitS1xNoRaw.synth_hftPcieOutByte_finalOffLN_Z
