import Tools.ShippingFGCircuitS1zClose
set_option autoImplicit false
-- FG circuit pilot S1z check. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED. Results: docs/FG-CIRCUIT-PILOT.md §28.

/-! # FGCircuitPilotCheck23 (light: each part is a small `run_cmd`)

1. SIGNATURES-A: `HftCoreCloses` against an independently written statement `ExpCC` (`isDefEq`, default transparency); controls: another world, another shape, another output, another env/logger/root, no core run, no `synthesizeFromConst` link, the old all-world `MachineCloses` form.
2. SIGNATURES-B: `hftPostGate_of_local`, `hftObNoRawOff_of_local` (gate derived, not assumed).
3. SIGNATURES-C: `synth_hftPcieOutByte_finalOffLNL_Z` against `ExpFLNL`; HYPS (13 names; no `hcl`/`hgate`/`hnoraw`); REMAINING; AXIOMS. -/
namespace Tests.Gen5.FGCircuitPilotCheck23
open Lean Meta Elab Command Term Sparkle.Core Sparkle.Core.Domain Tools.ShippingGen2 Tools.ShippingGen5DeclConnect Tools.ShippingGen5FG
open Tools.ShippingFGCircuit Tools.ShippingFGCircuitRoots Tools.ShippingFGCircuitArtifact Tools.ShippingFGCircuitCover Tools.ShippingFGCircuitBridge
open Tools.ShippingGenFGLedgerPremises Tools.ShippingFGCircuitS1iHead Tools.ShippingFGCircuitS1iEnv
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingEntryReadsLinked (envAt CoreSaved)
open Tools.ShippingGen5EnvFrame3 (CellPrem)
open Tools.ShippingFGCircuitS1kRoot Tools.ShippingFGCircuitS1kStmt Tools.ShippingFGCircuitS1kPkg
open Tools.ShippingFGCircuitS1qLinked Tools.ShippingFGCircuitS1qEndpoint
open Tools.ShippingFGCircuitS1mCD Tools.ShippingFGCircuitS1pCD Tools.ShippingFGCircuitS1rCD Tools.ShippingFGCircuitS1tFinal Tools.ShippingFGCircuitS1uSrc
open Tools.ShippingFGCircuitS1xNoRaw Tools.ShippingFGCircuitS1zClose
open Tools.ShippingMachineEntry
open Sparkle.Compiler.Elab

abbrev W := Void IO.RealWorld
abbrev Cx := Meta.Context
abbrev Rf1 := ST.Ref IO.RealWorld Meta.State
abbrev Cc := Core.Context
abbrev Rf2 := ST.Ref IO.RealWorld Core.State
abbrev Md := Sparkle.IR.AST.Module
abbrev Dg := Sparkle.IR.AST.Design
abbrev Rs := Tools.ShippingChildInv.Res
noncomputable def RootShape : MachineShape := synth_hftPcieOutByte.machineData.shape
noncomputable def OtherShape : MachineShape := Sparkle.Tests.SignalLoopTest.counterLoop.machineData.shape
noncomputable def HttpShape : MachineShape := Sparkle.IP.Net.HTTP.httpGetByte.machineData.shape

/-! ## 1. HftCoreCloses, independently -/

/-- the localised closing, written again from the description of docs §28.1: `decl`/`shape` the root; `Wsel` picks the start world of the machine run from (`w`, `w3`, `w8`); `Esel` the `tenv` from (`envR`, `envR'`); `lg` the logger flag; `Out` the claim about the result -/
noncomputable def ExpCC (decl : Name) (shape : MachineShape) (Wsel : W → W → W → W) (Esel : Environment → Environment → Environment) (lg : Bool)
    (Out : Option Rs → Md → Dg → Prop) (mctx : Cx) (mref : Rf1) (cctx : Cc) (cref : Rf2) (w : W) : Prop :=
  ∀ (raw : Md) (D₀ : Dg) (w1 : W),
    RunsTo (synthesizeCombinationalCoreOff decl) mctx mref cctx cref w (raw, D₀) w1 →
    ∀ (s : CoreSaved) (wh w2 w3 w4 : W) (envR : Environment) (ci : ConstantInfo),
      RunsTo (coreHeadOff decl) mctx mref cctx cref w s wh →
      RunsTo (getConstInfo decl) mctx mref cctx cref wh ci w2 →
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w2 envR w3 →
      RunsTo (synthesizeFromConst (fun e h t n => translateExprToWire envR e h t n) (Tools.ShippingChildInv.profLogIO false) decl [] false true
        (entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR)) (instancePredicate envR))
        mctx mref cctx cref w3 (raw, D₀) w4 →
      ∀ (envR' : Environment) (w8 w10 : W) (r : Option Rs),
        RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w3 envR' w8 →
        RunsTo (synthesizeMachineCertified (fun e hint top named => translateExprToWire (Esel envR envR') e hint top named)
          (Tools.ShippingChildInv.profLogIO lg) decl shape) mctx mref cctx cref (Wsel w w3 w8) r w10 →
        Out r raw D₀
noncomputable def OutOk : Option Rs → Md → Dg → Prop := fun r _ _ => r ≠ none
noncomputable def OutNone : Option Rs → Md → Dg → Prop := fun r _ _ => r = none
noncomputable def OutExact : Option Rs → Md → Dg → Prop := fun r raw D₀ => r = some (raw, D₀)
noncomputable def OutNotExact : Option Rs → Md → Dg → Prop := fun r raw D₀ => r ≠ some (raw, D₀)
noncomputable def OutTrue : Option Rs → Md → Dg → Prop := fun _ _ _ => True
noncomputable def SelW8 : W → W → W → W := fun _ _ w8 => w8
noncomputable def SelW3 : W → W → W → W := fun _ w3 _ => w3
noncomputable def SelW0 : W → W → W → W := fun w _ _ => w
noncomputable def SelE : Environment → Environment → Environment := fun e _ => e
noncomputable def SelE' : Environment → Environment → Environment := fun _ e' => e'

noncomputable def CCRoot : Cx → Rf1 → Cc → Rf2 → W → Prop := ExpCC hftRoot RootShape SelW8 SelE false OutOk
noncomputable def CCOtherW3 : Cx → Rf1 → Cc → Rf2 → W → Prop := ExpCC hftRoot RootShape SelW3 SelE false OutOk
noncomputable def CCOtherW0 : Cx → Rf1 → Cc → Rf2 → W → Prop := ExpCC hftRoot RootShape SelW0 SelE false OutOk
noncomputable def CCOtherShape : Cx → Rf1 → Cc → Rf2 → W → Prop := ExpCC hftRoot OtherShape SelW8 SelE false OutOk
noncomputable def CCHttpShape : Cx → Rf1 → Cc → Rf2 → W → Prop := ExpCC hftRoot HttpShape SelW8 SelE false OutOk
noncomputable def CCOutNone : Cx → Rf1 → Cc → Rf2 → W → Prop := ExpCC hftRoot RootShape SelW8 SelE false OutNone
noncomputable def CCOutExact : Cx → Rf1 → Cc → Rf2 → W → Prop := ExpCC hftRoot RootShape SelW8 SelE false OutExact
noncomputable def CCOutNotExact : Cx → Rf1 → Cc → Rf2 → W → Prop := ExpCC hftRoot RootShape SelW8 SelE false OutNotExact
noncomputable def CCOutTrue : Cx → Rf1 → Cc → Rf2 → W → Prop := ExpCC hftRoot RootShape SelW8 SelE false OutTrue
noncomputable def CCOtherEnv : Cx → Rf1 → Cc → Rf2 → W → Prop := ExpCC hftRoot RootShape SelW8 SelE' false OutOk
noncomputable def CCOtherLog : Cx → Rf1 → Cc → Rf2 → W → Prop := ExpCC hftRoot RootShape SelW8 SelE true OutOk
noncomputable def CCOtherRoot : Cx → Rf1 → Cc → Rf2 → W → Prop := ExpCC hftHttp RootShape SelW8 SelE false OutOk
/-- the all-world closing (S1x `hcl`) as a predicate of the same arguments -/
noncomputable def CCAllWorlds : Cx → Rf1 → Cc → Rf2 → W → Prop := fun mctx mref cctx cref _ => MachineCloses mctx mref cctx cref hftRoot RootShape
/-- no core-run premise: the machine run is anywhere -/
noncomputable def CCNoCore : Cx → Rf1 → Cc → Rf2 → W → Prop := fun mctx mref cctx cref w =>
  ∀ (envR : Environment) (w8 w10 : W) (r : Option Rs),
    RunsTo (synthesizeMachineCertified (fun e hint top named => translateExprToWire envR e hint top named)
      (Tools.ShippingChildInv.profLogIO false) hftRoot RootShape) mctx mref cctx cref w8 r w10 → r ≠ none
/-- no link to the `synthesizeFromConst` of the decomposition (the machine start world is an arbitrary `getEnv` end world) -/
noncomputable def CCNoSfc : Cx → Rf1 → Cc → Rf2 → W → Prop := fun mctx mref cctx cref w =>
  ∀ (raw : Md) (D₀ : Dg) (w1 : W), RunsTo (synthesizeCombinationalCoreOff hftRoot) mctx mref cctx cref w (raw, D₀) w1 →
    ∀ (envR envR' : Environment) (w3 w8 w10 : W) (r : Option Rs),
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w3 envR' w8 →
      RunsTo (synthesizeMachineCertified (fun e hint top named => translateExprToWire envR e hint top named)
        (Tools.ShippingChildInv.profLogIO false) hftRoot RootShape) mctx mref cctx cref w8 r w10 → r ≠ none

def whitelist : List Name := [``HftCoreCloses, ``CoreCloses, ``HftFinalStmtOffLNL, ``HftFinalStmtOffLN, ``HftFinalStmtOffL, ``HftPostGate]
def inQ (c : Name) : Bool := (`Tests.Gen5.FGCircuitPilotCheck23).isPrefixOf c
def normOnce (e : Lean.Expr) : MetaM Lean.Expr :=
  Meta.transform e (post := fun e => do
    let e := e.headBeta
    if let .const c _ := e.getAppFn then
      if whitelist.contains c || inQ c then
        if let some e' ← unfoldDefinition? e then return .visit e'.headBeta
    return .done e)
def norm (e : Lean.Expr) : MetaM Lean.Expr := do
  let mut e := e
  for _ in [0:5] do
    e ← normOnce e
  return e
def sameTy (what : String) (ty exp : Lean.Expr) : MetaM Unit := do
  let a ← norm ty
  let e ← norm exp
  unless ← withDefault (isDefEq a e) do throwError "{what}: type is NOT the expected statement"
def diffTy (what : String) (ty exp : Lean.Expr) : MetaM Unit := do
  let a ← norm ty
  let e ← norm exp
  if a == e then throwError "{what}: the MUTANT is the same expression"
  if ← withReducible (isDefEq a e) then throwError "{what}: the MUTANT was accepted"
def tyOf (n : Name) : MetaM Lean.Expr := do
  let ci ← getConstInfo n
  unless ci.levelParams.isEmpty do throwError "{n}: level parameters"
  pure ci.type
partial def binderInfos : Lean.Expr → List BinderInfo
  | .forallE _ _ b bi => bi :: binderInfos b
  | _ => []

set_option maxHeartbeats 4000000 in
run_cmd liftTermElabM do
  let C (n : Name) : Lean.Expr := mkConst n
  let X := `Tools.ShippingFGCircuitS1zClose
  let Q := `Tests.Gen5.FGCircuitPilotCheck23
  sameTy "HftCoreCloses" (C (X ++ `HftCoreCloses)) (C (Q ++ `CCRoot))
  let mut nm : Nat := 0
  for mu in ["CCOtherW3", "CCOtherW0", "CCOtherShape", "CCHttpShape", "CCOutNone", "CCOutExact", "CCOutNotExact", "CCOutTrue", "CCOtherEnv", "CCOtherLog", "CCOtherRoot", "CCAllWorlds", "CCNoCore", "CCNoSfc"] do
    diffTy s!"HftCoreCloses vs {mu}" (C (X ++ `HftCoreCloses)) (C (Q ++ Name.mkSimple mu)); nm := nm + 1
  logInfo m!"FGCIRCUIT23 SIGNATURES-A: HftCoreCloses matches the independently written ExpCC (isDefEq, default); {nm} mutants rejected (another world: w3 / the run's start world; another shape: counterLoop / httpGetByte; another output: = none / = some (raw, D₀) / ≠ some (raw, D₀) / True; another env; another logger; another root; the all-world MachineCloses; no core run; no synthesizeFromConst link)"
