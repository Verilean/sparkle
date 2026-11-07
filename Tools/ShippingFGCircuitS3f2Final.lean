import Tools.ShippingFGCircuitS3dFinal
import Tools.ShippingFGCircuitS3f2Exp
set_option autoImplicit false
-- FG circuit pilot S3f2: the checked pilot entry `pilotReaderOk2` (pilotReaderOk plus the ROOT checks), its soundness onto `CheckedEnv`, the bridge RootReader → ReaderAt, and the final statement v9 = v8 WITHOUT `env₀` and `hchk` (9 binders): `env₀` is specialised to `envAt cref w` (so `ReadsAt` is `readsAt_self`), and `CheckedEnv` comes from the run's own guard.  `pilotReaderOk` / v7r / v8 are untouched.  No sorry/axiom/native_decide/TRUSTED/law. docs/FG-CIRCUIT-PILOT.md §56.
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace Tools.ShippingFGCircuitS3f2Final
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
open Tools.ShippingFGCircuitS3cFinal (synth_hftPcieOutByte_finalOffCombined7)

local instance : DecidableEq Lean.Expr := fun a b => Sparkle.Compiler.ExprDecEq.exprDecEq a b

/-- the root's declaration in the environment, as a Bool: `X` is a `defnInfo` with no universe parameters and exactly the pinned closed type and value (`Expr` equality by the structural decision procedure) -/
def rootDefB (env : Environment) (X : Name) (ty val : Lean.Expr) : Bool :=
  match env.find? X with
  | some (.defnInfo d) => d.levelParams.isEmpty && decide (d.type = ty) && decide (d.value = val)
  | _ => false

theorem rootDefB_sound {env : Environment} {X : Name} {ty val : Lean.Expr} (h : rootDefB env X ty val = true) :
    ∃ d : DefinitionVal, RootInEnv env X ty val d := by
  unfold rootDefB at h
  split at h
  · rename_i d hd
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.isEmpty_iff] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    exact ⟨d, hd, h1, h2, h3⟩
  · cases h

/-- **the bridge `RootReader → ReaderAt`**: the root reader's data at a found entry are those of every entry found (`entry₀` is a function) -/
theorem readerAt_of_rootReader {lvl : Lean.Expr → Nat} {env : Environment} {X : Name} {d : Tools.ShippingMachineAuto.MachineData}
    (h : RootReader lvl env X d) : Tools.ShippingFGCircuitFinal4.ReaderAt lvl env X d := by
  obtain ⟨E, hE, hs, hd⟩ := h
  intro E' hE'
  rw [hE] at hE'
  cases Option.some.inj hE'
  exact ⟨hs, hd⟩

/-- **the concrete checker of the S3f2 pilot entry**: `pilotReaderOk` (the pilot root and the two children's real `dataOfAt` at `lvl₀`) AND, on the same environment, the root's own checks: the definition (`defnInfo`, no level parameters, type, value), the two refusal gates `entryGatesB`, and the real `dataOfAt` for the root at `lvl₀` against the executable copy `rootMD` of `synth_hftPcieOutByte.machineData` -/
def pilotReaderOk2 (env : Environment) (X : Name) : Bool :=
  pilotReaderOk env X && rootDefB env X hftRootType hftRootValue && entryGatesB env X &&
    rootReaderB lvl₀ env X rootMD

/-- (1) **soundness of the check**: the children's readers as before, and `CheckedEnv lvl₀ env hftRoot …` for the root at the SAME environment (`root` from `rootDefB`, `gates` from `entryGatesB`, `reader` from `rootReaderB` through `rootMD_eq` and the bridge) -/
theorem pilotReaderOk2_sound {env : Environment} {X : Name} (h : pilotReaderOk2 env X = true) :
    X = hftRoot ∧
    RootReader lvl₀ env Tools.ShippingFGCircuitS1kStmt.hftHttp Sparkle.IP.Net.HTTP.httpGetByte.machineData ∧
    RootReader lvl₀ env Tools.ShippingFGCircuitS1kStmt.hftTlp Sparkle.IP.Bus.PCIe.tlpCplByte.machineData ∧
    CheckedEnv lvl₀ env hftRoot hftRootType hftRootValue synth_hftPcieOutByte.machineData := by
  unfold pilotReaderOk2 at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := h
  obtain ⟨hX, hH, hT⟩ := pilotReaderOk_sound h0
  subst hX
  refine ⟨rfl, hH, hT, rootDefB_sound h1, h2, ?_⟩
  rw [← rootMD_eq]
  exact readerAt_of_rootReader (rootReaderB_sound h3)

/-- the S3f2 pilot entry: the profile-free entry with `pilotReaderOk2` as its extra guard (false: an explicit error, no fallback) -/
def pilotEntry2 (declName : Name) : MetaM (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design) :=
  synthesizeCombinationalOffR pilotReaderOk2 declName

/-- **v9** (9 binders): the pilot entry `pilotReaderOk2` (`hr` is a run of `synthesizeCombinationalOffR pilotReaderOk2 hftRoot`) at the concrete `lvl₀`, WITHOUT `env₀` and `hchk`: `env₀` is `envAt cref w` and `hchk` is supplied by the run's own guard.  Binders: `L hstart hr hcell hD hG hT hs h0`. -/
def HftFinalStmtOffCombined9 : Prop :=
  ∀ {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (hstart : Start L mctx cctx w)
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
theorem synth_hftPcieOutByte_finalOffCombined9 : HftFinalStmtOffCombined9 := by
  intro ι mref cref L mctx cctx w w' b D' hstart hr hcell hD hG hT hs h0
  obtain ⟨-, hH, hT', hCE⟩ := pilotReaderOk2_sound (readerOk_of_run hcell hr)
  exact synth_hftPcieOutByte_finalOffCombined7 L lvl₀ (envAt cref w) hstart (offR_to_off hr) hcell ⟨hCE, Tools.ShippingGen5Env.readsAt_self cref w⟩ hH hT' hD hG hT hs h0

/-! ## the command of the S3f2 pilot entry: it prints the artifact THIS run returned (no second synthesis) -/

def pilotArtifact2 (declName : Name) : MetaM (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design × String) := do
  let (module, design) ← pilotEntry2 declName
  return (module, design, verilogOf module)

open Lean Elab Command in
elab "#synthesizeVerilogPilot2 " id:ident : command => do
  let declName ← liftCoreM do Lean.resolveGlobalConstNoOverload id
  liftTermElabM do
    inlinerFuelGuard declName
    let (module, _, verilog) ← pilotArtifact2 declName
    let warnings := Sparkle.Compiler.DRC.checkRegisteredOutputs module
    for w in warnings do
      Lean.logWarning m!"{w}"
    IO.println verilog
    IO.println "\n-- Verilog successfully generated (pilot entry 2)!"

end Tools.ShippingFGCircuitS3f2Final

#print axioms Tools.ShippingFGCircuitS3f2Final.rootDefB_sound
#print axioms Tools.ShippingFGCircuitS3f2Final.readerAt_of_rootReader
#print axioms Tools.ShippingFGCircuitS3f2Final.pilotReaderOk2_sound
#print axioms Tools.ShippingFGCircuitS3f2Final.synth_hftPcieOutByte_finalOffCombined9
