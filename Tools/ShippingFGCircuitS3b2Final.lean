import Tools.ShippingFGCircuitS3aFinal
import Tools.ShippingFGCircuitS3b2Core
import Tools.ShippingFGCircuitS3b2Reader
import Tools.ShippingFGCircuitS3b2Exp
set_option autoImplicit false
-- FG circuit pilot S3b2 (route B): the PILOT ENTRY `pilotEntry` = `synthesizeCombinationalOffR pilotReaderOk` with the concrete reader check, the theorems that hand the check's result to the final statement (soundness, guard from the run, bridge to the existing entry), and the final statement v7r = v6 at `lvl₀` WITHOUT `lvl hreadH hreadT`, for THIS entry only.  The existing v6 and the existing entries are untouched.  No sorry/axiom/native_decide/TRUSTED/law. docs/FG-CIRCUIT-PILOT.md §53.
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace Tools.ShippingFGCircuitS3b2Final
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
open Tools.ShippingFGCircuitS3b2Core

open Tools.ShippingFGCircuitS3aFinal (HftFinalStmtOffCombined6 synth_hftPcieOutByte_finalOffCombined6)
open Tools.ShippingFGCircuitS3b2Reader (lvl₀ rootReaderB rootReaderB_sound)
open Tools.ShippingFGCircuitS3b2Exp (httpMD tlpMD httpMD_eq tlpMD_eq)
open Tools.ShippingFGCircuitS3b2Core (offR_to_off coreR_chain)

/-- **the concrete reader check of the pilot entry**: the root is the pilot root, and the REAL `dataOfAt` at `lvl₀`, on the same environment, returns for each of the two children a `MachineData` structurally equal to that child's `machineData` (compiled copy, `httpMD_eq` / `tlpMD_eq`) -/
def pilotReaderOk (env : Environment) (X : Name) : Bool :=
  X == hftRoot && rootReaderB lvl₀ env hftHttp httpMD && rootReaderB lvl₀ env hftTlp tlpMD

/-- (1) **soundness of the check**: it gives the two `RootReader`s, at `lvl₀`, at the SAME environment, from the real `dataOfAt`, for the children's `machineData` -/
theorem pilotReaderOk_sound {env : Environment} {X : Name} (h : pilotReaderOk env X = true) :
    X = hftRoot ∧
    RootReader lvl₀ env hftHttp Sparkle.IP.Net.HTTP.httpGetByte.machineData ∧
    RootReader lvl₀ env hftTlp Sparkle.IP.Bus.PCIe.tlpCplByte.machineData := by
  unfold pilotReaderOk at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hX, h1⟩, h2⟩ := h
  refine ⟨hX, ?_, ?_⟩
  · rw [← httpMD_eq]; exact rootReaderB_sound h1
  · rw [← tlpMD_eq]; exact rootReaderB_sound h2

/-- **the pilot entry**: the profile-free entry with the reader check `pilotReaderOk` as its extra guard (false: an explicit error, no fallback) -/
def pilotEntry (declName : Name) : MetaM (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design) :=
  synthesizeCombinationalOffR pilotReaderOk declName

/-- (2) **the guard from the run**: a successful run of the checked entry on the pilot root passed `readerOk` at ITS start environment `envAt cref w` (head, `getConstInfo` and `getEnv` keep the Core environment, as in `startKidsOk_of_run`).  Any `readerOk`. -/
theorem readerOk_of_run {readerOk : Environment → Name → Bool} {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (hcell : CellPrem Tools.ShippingChildFresh.MkRefd mref cref)
    (hr : RunsTo (synthesizeCombinationalOffR readerOk hftRoot) mctx mref cctx cref w (b, D') w') :
    readerOk (envAt cref w) hftRoot = true := by
  unfold synthesizeCombinationalOffR at hr
  obtain ⟨⟨M, D⟩, w1', hcore, -⟩ := Tools.ShippingEntrySoundness.RunsTo.bind hr
  obtain ⟨s, w1, envR, ci, w2, w3, w4, hh, hget, henv, -, -, -, hok, -, -⟩ := coreR_chain hcore
  have e1 : envAt cref w1 = envAt cref w := headAtOff_of_cellPrem (w := w) hftRoot hcell s w1 hh
  have e2 : envAt cref w2 = envAt cref w1 := envFrame_getConstInfo hftRoot (getEnvFrame_of_cellPrem hcell) w1 ci w2 hget
  have e3 : envR = envAt cref w2 := Tools.ShippingEntryReadsLinked.getEnv_value henv
  rw [e3, e2, e1] at hok
  exact hok

/-- **v7r** (route B): the final statement v6 at the concrete `lvl₀`, for the PILOT ENTRY only (`hr` is a run of `synthesizeCombinationalOffR pilotReaderOk hftRoot`), WITHOUT `lvl`, `hreadH`, `hreadT`.  The root's `hchk`, the two children's `RootReader` (from the check) and the conclusion's `GPt` all use the same `lvl₀`; the conclusion is about the same post-processing of the EXISTING core (`PostRunOff`). -/
def HftFinalStmtOffCombined7R : Prop :=
  ∀ {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (env₀ : Environment)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (hstart : Start L mctx cctx w)
    (hr : RunsTo (synthesizeCombinationalOffR pilotReaderOk hftRoot) mctx mref cctx cref w (b, D') w')
    (hcell : CellPrem Tools.ShippingChildFresh.MkRefd mref cref)
    (hchk : CheckedStart lvl₀ env₀ cref w hftRoot hftRootType hftRootValue synth_hftPcieOutByte.machineData)
    (hadm : AdmCtx (quietR L.O.quiet mref cref (envAt cref w) w) mctx cctx)
    (hdown : AdmDownR L.O (envAt cref w) w) (hD : DRowEnvR L.O (envAt cref w) w)
    (hG : DiagEnvR L.O (envAt cref w) w) (hT : TeleR L.O (envAt cref w) w)
    (hs : ProfStepR L.O w) (h0 : ProfOffW mref cref w),
    (∃ raw, PostRunOff mctx mref cctx cref w hftRoot D' b raw) ∧
    ∃ (mm : MonoTy shHft) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMonoV cdvT (envAt cref w) (GPt (ι := ι) lvl₀ (envAt cref w))
        (PostRunOff mctx mref cctx cref w hftRoot D') hftRoot shHft mm b D' p

theorem synth_hftPcieOutByte_finalOffCombined7R : HftFinalStmtOffCombined7R := by
  intro ι mref cref L env₀ mctx cctx w w' b D' hstart hr hcell hchk hadm hdown hD hG hT hs h0
  obtain ⟨-, hH, hT'⟩ := pilotReaderOk_sound (readerOk_of_run hcell hr)
  exact synth_hftPcieOutByte_finalOffCombined6 L lvl₀ env₀ hstart (offR_to_off hr) hcell hchk hH hT' hadm hdown hD hG hT hs h0

/-! ## the command of the pilot entry: it prints the artifact THIS run returned (no second synthesis) -/

/-- the pilot entry's ONE run and what the command prints from it: the Module and Design the run returned, and the Verilog text of THAT Module (`verilogOf`, as `#synthesizeVerilog`) -/
def pilotArtifact (declName : Name) : MetaM (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design × String) := do
  let (module, design) ← pilotEntry declName
  return (module, design, verilogOf module)

open Lean Elab Command in
elab "#synthesizeVerilogPilot " id:ident : command => do
  let declName ← liftCoreM do Lean.resolveGlobalConstNoOverload id
  liftTermElabM do
    inlinerFuelGuard declName
    let (module, _, verilog) ← pilotArtifact declName
    let warnings := Sparkle.Compiler.DRC.checkRegisteredOutputs module
    for w in warnings do
      Lean.logWarning m!"{w}"
    IO.println verilog
    IO.println "\n-- Verilog successfully generated (pilot entry)!"

end Tools.ShippingFGCircuitS3b2Final

#print axioms Tools.ShippingFGCircuitS3b2Final.pilotReaderOk_sound
#print axioms Tools.ShippingFGCircuitS3b2Final.readerOk_of_run
#print axioms Tools.ShippingFGCircuitS3b2Final.synth_hftPcieOutByte_finalOffCombined7R
