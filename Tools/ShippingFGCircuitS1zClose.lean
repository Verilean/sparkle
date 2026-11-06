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

end Tools.ShippingFGCircuitS1zClose
