import Tools.ShippingFGCircuitS1xNoRaw
import Tools.ShippingParentDesignA
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

/-- **the localised hcl** (docs §28.2): the machine run embedded in the given decomposition of the target core run does not return `none` -/
def CoreCloses (declName : Name) (shape : MachineShape)
    (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State) (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State)
    (w : Void IO.RealWorld) : Prop :=
  ∀ (raw : Sparkle.IR.AST.Module) (D₀ : Sparkle.IR.AST.Design) (w1 : Void IO.RealWorld),
    RunsTo (synthesizeCombinationalCoreOff declName) mctx mref cctx cref w (raw, D₀) w1 →
    ∀ (s : CoreSaved) (wh w2 w3 w4 : Void IO.RealWorld) (envR : Environment) (ci : ConstantInfo),
      RunsTo (coreHeadOff declName) mctx mref cctx cref w s wh →
      RunsTo (getConstInfo declName) mctx mref cctx cref wh ci w2 →
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w2 envR w3 →
      RunsTo (synthesizeFromConst (fun e h t n => translateExprToWire envR e h t n) (Tools.ShippingChildInv.profLogIO false) declName [] false true
        (entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR)) (instancePredicate envR))
        mctx mref cctx cref w3 (raw, D₀) w4 →
      ∀ (envR' : Environment) (w8 w10 : Void IO.RealWorld) (r : Option Tools.ShippingChildInv.Res),
        RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w3 envR' w8 →
        RunsTo (synthesizeMachineCertified (fun e hint top named => translateExprToWire envR e hint top named)
          (Tools.ShippingChildInv.profLogIO false) declName shape) mctx mref cctx cref w8 r w10 →
        r ≠ none

/-- the root's localised closing -/
abbrev HftCoreCloses (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State) (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State)
    (w : Void IO.RealWorld) : Prop :=
  CoreCloses hftRoot synth_hftPcieOutByte.machineData.shape mctx mref cctx cref w

/-! ## the run -/
section Proofs
open Tools.ShippingEntrySoundness
open Tools.ShippingChildInv Tools.ShippingChildBndInit Tools.ShippingChildBndCore Tools.ShippingChildInvA Tools.ShippingChildFresh
open Tools.ShippingChildVCA Tools.ShippingChildCacheA Tools.ShippingChildVertA Tools.ShippingChildCoreC Tools.ShippingChildRunA
open Tools.ShippingServedRealA Tools.ShippingChildRunAKids Tools.ShippingMachineClose Tools.ShippingMixedEntrySoundness Sparkle.IR.Machine
open Tools.ShippingChildComposeC Tools.ShippingChildRunAMain Tools.ShippingParentRanA
variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- `synthesizeFromConst_machine_invR` with the START WORLD of the machine run exposed: it is the world `w6` read by the `getEnv` of the body -/
theorem synthesizeFromConst_machine_invW (O : RefLawsAOps MkRefd mref cref)
    (hA : AdmCtx O.quiet mctx cctx) {tenv : Lean.Environment}
    {logProf : String → IO Unit} {declName : Name} {n : Nat}
    {ci : ConstantInfo} {isInst : Lean.Expr → Bool} {m : Sparkle.IR.AST.Module}
    {d : Sparkle.IR.AST.Design} {w w' : Void IO.RealWorld}
    (old : certifiedShape? false [] ci = none)
    (miss : mixedCertifiedShape? false [] ci isInst = none) (hw : JQC O n w)
    (hr : RunsTo (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) logProf
      declName [] false true ci isInst) mctx mref cctx cref w (m, d) w') :
    ∃ (envR : Environment) (w6 : Void IO.RealWorld),
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w envR w6 ∧ JQC O n w6 ∧
      ∀ shape, machineShape? false [] ci (structEnv envR) = some shape →
        ∃ r w8, RunsTo (synthesizeMachineCertified
            (fun e hint top named => translateExprToWire tenv e hint top named) logProf declName
            shape) mctx mref cctx cref w6 r w8 ∧
          ∀ res, r = some res → res = (m, d) := by
  unfold synthesizeFromConst at hr
  simp only [↓reduceIte, old, miss, Bool.not_false, Bool.and_self, List.isEmpty_nil] at hr
  obtain ⟨envR, w1, henv, hr⟩ := RunsTo.bind hr
  have hw1 := triple_runs (keeps_iff.mp (keepsA_framed O hA (stableA_JQC O n) FramedA.env)) hw henv
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

/-- **the embedded machine run is a `MachineRanA`** (it returns `some (M, D)`, `closeLets`, `CloseCalls` with `ChildrenRealA`), from the localised closing and `Start L` -/
theorem coreOff_ranA (L : Laws mref cref) {declName : Name} {shape : MachineShape} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (hstart : Start L mctx cctx w)
    (hr : RunsTo (synthesizeCombinationalCoreOff declName) mctx mref cctx cref w (m, d) w')
    (entry : MachineDefinesLinkedOff mctx mref cctx cref declName shape w m d w')
    (hloc : CoreCloses declName shape mctx mref cctx cref w) :
    MachineRanA L.O mctx cctx declName shape m d := by
  obtain ⟨s, w1, envR, ci, w2, w3, w4, hh, hget, henv, hbody, -⟩ := core_chainOff hr
  have hw1 := coreHeadOff_jqcA L.O hstart.1 hstart.2.1 (Or.inl rfl) hh
  have hw2 := triple_runs (keeps_iff.mp (keepsA_framed L.O hstart.1 (stableA_JQC L.O (0 + 1)) (FramedA.constInfo _))) hw1 hget
  have hw3 := triple_runs (keeps_iff.mp (keepsA_framed L.O hstart.1 (stableA_JQC L.O (0 + 1)) FramedA.env)) hw2 henv
  obtain ⟨old, miss, hshape⟩ := entry hr s w1 w2 w3 w4 envR ci hh hget henv hbody
  obtain ⟨envR', w8, henv', hw8, hmach⟩ := synthesizeFromConst_machine_invW L.O hstart.1 old miss hw3 hbody
  obtain ⟨r, w10, hrun, hres⟩ := hmach shape (hshape _ _ henv')
  have hne := hloc m d w' hr s w1 w2 w3 w4 envR ci hh hget henv hbody envR' w8 w10 r henv' hrun
  cases r with
  | none => exact absurd rfl hne
  | some res =>
    have := hres res rfl
    subst this
    obtain ⟨t, t', d₀, run, hcl, hmt⟩ :=
      synthesizeMachineCertified_runsA (b := false) L.O (bodyStepC_of_tele L.O L.T) hstart.1
        (htr_of_tele L.O hstart.1 L.T 0 envR) hw8 hrun
    exact ⟨envR, false, w8, w10, hrun, t, t', d₀, run, hcl, hmt⟩

/-- the closing's last check, from the embedded run -/
theorem closed_of_ranA {O : RefLawsAOps MkRefd mref cref} {c : Name} {shape : MachineShape} {M : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
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

end Proofs

end Tools.ShippingFGCircuitS1zClose
