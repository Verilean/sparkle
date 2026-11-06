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

/-! ## 2. the derived gate and `HftObNoRawOff` -/

noncomputable def GateT : Cx → Rf1 → Cc → Rf2 → W → Md → Dg → Prop := fun mctx mref cctx cref w b D' =>
  ∀ (raw : Md) (D₀ : Dg) (w1 : W), RunsTo (synthesizeCombinationalCoreOff hftRoot) mctx mref cctx cref w (raw, D₀) w1 →
    Tools.ShippingGen5DCEntryD.PostEntry b raw D₀ D' → Sparkle.IR.RefineCheck.hierGate b = true
noncomputable def GateConstC : Cx → Rf1 → Cc → Rf2 → W → Md → Dg → Prop := fun mctx mref cctx cref w b D' =>
  ∀ (raw : Md) (D₀ : Dg) (w1 : W), RunsTo (synthesizeCombinationalCoreOff hftRoot) mctx mref cctx cref w (raw, D₀) w1 →
    Tools.ShippingGen5DCEntryD.PostEntry b raw D₀ D' → True
noncomputable def GateBindsC : Cx → Rf1 → Cc → Rf2 → W → Md → Dg → Prop := fun mctx mref cctx cref w b D' =>
  ∀ (raw : Md) (D₀ : Dg) (w1 : W), RunsTo (synthesizeCombinationalCoreOff hftRoot) mctx mref cctx cref w (raw, D₀) w1 →
    Tools.ShippingGen5DCEntryD.PostEntry b raw D₀ D' → Sparkle.IR.RefineCheck.hierBinds b = true

/-- `hftPostGate_of_local`: the conclusion gate is a parameter; the closing premise is a parameter -/
noncomputable def ExpPG (Cl : Cx → Rf1 → Cc → Rf2 → W → Prop) (Shd : MachineShape) (Gt : Cx → Rf1 → Cc → Rf2 → W → Md → Dg → Prop) : Prop :=
  ∀ {mctx : Cx} {mref : Rf1} {cctx : Cc} {cref : Rf2} (L : Laws mref cref) {w : W} {b : Md} {D' : Dg}
    (_hstart : Start L mctx cctx w)
    (_hdRun : ∀ (raw : Md) (D₀ : Dg) (w1 : W), MachineDefinesLinkedOff mctx mref cctx cref hftRoot Shd w raw D₀ w1)
    (_hclL : Cl mctx mref cctx cref w),
    Gt mctx mref cctx cref w b D'
noncomputable def ExpPG0 (Cl : Cx → Rf1 → Cc → Rf2 → W → Prop) (Gt : Cx → Rf1 → Cc → Rf2 → W → Md → Dg → Prop) : Prop :=
  ∀ {mctx : Cx} {mref : Rf1} {cctx : Cc} {cref : Rf2} (L : Laws mref cref) {w : W} {b : Md} {D' : Dg}
    (_hdRun : ∀ (raw : Md) (D₀ : Dg) (w1 : W), MachineDefinesLinkedOff mctx mref cctx cref hftRoot RootShape w raw D₀ w1)
    (_hclL : Cl mctx mref cctx cref w),
    Gt mctx mref cctx cref w b D'
noncomputable def ExpNR (Cl : Cx → Rf1 → Cc → Rf2 → W → Prop) (Shd : MachineShape) : Prop :=
  ∀ {mctx : Cx} {mref : Rf1} {cctx : Cc} {cref : Rf2} (L : Laws mref cref) {w : W} {b : Md} {D' : Dg}
    (_hstart : Start L mctx cctx w)
    (_hdRun : ∀ (raw : Md) (D₀ : Dg) (w1 : W), MachineDefinesLinkedOff mctx mref cctx cref hftRoot Shd w raw D₀ w1)
    (_hclL : Cl mctx mref cctx cref w),
    HftObNoRawOff mctx mref cctx cref w b D'
noncomputable def ClNoneC : Cx → Rf1 → Cc → Rf2 → W → Prop := fun _ _ _ _ _ => True

set_option maxHeartbeats 4000000 in
run_cmd liftTermElabM do
  let C (n : Name) : Lean.Expr := mkConst n
  let X := `Tools.ShippingFGCircuitS1zClose
  let Q := `Tests.Gen5.FGCircuitPilotCheck23
  let mut nm : Nat := 0
  let t ← tyOf (X ++ `hftPostGate_of_local)
  let ok := mkApp3 (C (Q ++ `ExpPG)) (C (Q ++ `CCRoot)) (C (Q ++ `RootShape)) (C (Q ++ `GateT))
  sameTy "hftPostGate_of_local" t ok
  unless binderInfos (← norm t) == binderInfos (← norm ok) do throwError "hftPostGate_of_local: binder kinds differ"
  let muts : List (String × Lean.Expr) := [
    ("closing of another world (w3)", mkApp3 (C (Q ++ `ExpPG)) (C (Q ++ `CCOtherW3)) (C (Q ++ `RootShape)) (C (Q ++ `GateT))),
    ("closing of another shape", mkApp3 (C (Q ++ `ExpPG)) (C (Q ++ `CCOtherShape)) (C (Q ++ `RootShape)) (C (Q ++ `GateT))),
    ("closing with another output (= none)", mkApp3 (C (Q ++ `ExpPG)) (C (Q ++ `CCOutNone)) (C (Q ++ `RootShape)) (C (Q ++ `GateT))),
    ("no closing premise", mkApp3 (C (Q ++ `ExpPG)) (C (Q ++ `ClNoneC)) (C (Q ++ `RootShape)) (C (Q ++ `GateT))),
    ("machine boundary of another shape", mkApp3 (C (Q ++ `ExpPG)) (C (Q ++ `CCRoot)) (C (Q ++ `OtherShape)) (C (Q ++ `GateT))),
    ("constant gate", mkApp3 (C (Q ++ `ExpPG)) (C (Q ++ `CCRoot)) (C (Q ++ `RootShape)) (C (Q ++ `GateConstC))),
    ("hierBinds gate", mkApp3 (C (Q ++ `ExpPG)) (C (Q ++ `CCRoot)) (C (Q ++ `RootShape)) (C (Q ++ `GateBindsC))),
    ("no Start premise", mkApp2 (C (Q ++ `ExpPG0)) (C (Q ++ `CCRoot)) (C (Q ++ `GateT)))]
  for (what, m) in muts do
    diffTy s!"hftPostGate_of_local vs {what}" t m; nm := nm + 1
  let t2 ← tyOf (X ++ `hftObNoRawOff_of_local)
  let ok2 := mkApp2 (C (Q ++ `ExpNR)) (C (Q ++ `CCRoot)) (C (Q ++ `RootShape))
  sameTy "hftObNoRawOff_of_local" t2 ok2
  unless binderInfos (← norm t2) == binderInfos (← norm ok2) do throwError "hftObNoRawOff_of_local: binder kinds differ"
  let muts2 : List (String × Lean.Expr) := [
    ("closing of another world (w0)", mkApp2 (C (Q ++ `ExpNR)) (C (Q ++ `CCOtherW0)) (C (Q ++ `RootShape))),
    ("closing of another shape", mkApp2 (C (Q ++ `ExpNR)) (C (Q ++ `CCHttpShape)) (C (Q ++ `RootShape))),
    ("closing with another output (exact)", mkApp2 (C (Q ++ `ExpNR)) (C (Q ++ `CCOutExact)) (C (Q ++ `RootShape))),
    ("no closing premise", mkApp2 (C (Q ++ `ExpNR)) (C (Q ++ `ClNoneC)) (C (Q ++ `RootShape))),
    ("machine boundary of another shape", mkApp2 (C (Q ++ `ExpNR)) (C (Q ++ `CCRoot)) (C (Q ++ `OtherShape)))]
  for (what, m) in muts2 do
    diffTy s!"hftObNoRawOff_of_local vs {what}" t2 m; nm := nm + 1
  logInfo m!"FGCIRCUIT23 SIGNATURES-B: hftPostGate_of_local (hgate DERIVED: premises Start L, the machine boundary of the core run, HftCoreCloses; conclusion HftPostGate) and hftObNoRawOff_of_local match independently written statements; {nm} mutants rejected (another world / shape / output of the closing; no closing; boundary of another shape; constant or hierBinds gate; no Start)"

/-! ## 3. the final statement -/

noncomputable def ExpFLNL (Ob : Environment → Prop) (CV : CDRel) (Cl : Cx → Rf1 → Cc → Rf2 → W → Prop) : Prop :=
  ∀ (hlink : HftRootLink) {ι : Type} {mref : Rf1} {cref : Rf2}
    (L : Laws mref cref) (lvl : Lean.Expr → Nat) (env₀ : Environment)
    {mctx : Cx} {cctx : Cc} {w w' : W} {b : Md} {D' : Dg}
    (hstart : Start L mctx cctx w)
    (hr : RunsTo (synthesizeCombinationalOff hftRoot) mctx mref cctx cref w (b, D') w')
    (hcell : CellPrem Tools.ShippingChildFresh.MkRefd mref cref)
    (hchk : CheckedStart lvl env₀ cref w hftRoot hftRootType hftRootValue synth_hftPcieOutByte.machineData)
    (hreadH : RootReader lvl (envAt cref w) hftHttp Sparkle.IP.Net.HTTP.httpGetByte.machineData)
    (hreadT : RootReader lvl (envAt cref w) hftTlp Sparkle.IP.Bus.PCIe.tlpCplByte.machineData)
    (hcd : Ob (envAt cref w))
    (htop : ∀ p : Pkg ι (fun _ => defaultDomain), GPt (ι := ι) lvl (envAt cref w) hftRoot = some p → HftObTopCoreOff mctx mref cctx cref w b D' p)
    (hclL : Cl mctx mref cctx cref w),
    (∃ raw, PostRunOff mctx mref cctx cref w hftRoot D' b raw) ∧
    ∃ (mm : MonoTy shHft) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMonoV CV (envAt cref w) (GPt (ι := ι) lvl (envAt cref w))
        (PostRunOff mctx mref cctx cref w hftRoot D') hftRoot shHft mm b D' p
noncomputable def FZL := ExpFLNL HftObCDZ cdvZ CCRoot

set_option maxHeartbeats 4000000 in
run_cmd liftTermElabM do
  let C (n : Name) : Lean.Expr := mkConst n
  let X := `Tools.ShippingFGCircuitS1zClose
  let Q := `Tests.Gen5.FGCircuitPilotCheck23
  let Y := `Tools.ShippingFGCircuitS1xNoRaw
  let mut nm : Nat := 0
  let t ← tyOf (X ++ `synth_hftPcieOutByte_finalOffLNL_Z)
  sameTy "finalOffLNL_Z" t (C (Q ++ `FZL))
  unless binderInfos (← norm t) == binderInfos (← norm (C (Q ++ `FZL))) do throwError "finalOffLNL_Z: binder kinds differ"
  let ap (ob cv cl : Lean.Expr) : Lean.Expr := mkApp3 (C (Q ++ `ExpFLNL)) ob cv cl
  let ob := C ``HftObCDZ
  let cvZ := C ``cdvZ
  let cl := C (Q ++ `CCRoot)
  let muts : List (String × Lean.Expr) := [
    ("no closing premise", ap ob cvZ (C (Q ++ `ClNoneC))), ("closing of another world (w3)", ap ob cvZ (C (Q ++ `CCOtherW3))),
    ("closing of another world (w0)", ap ob cvZ (C (Q ++ `CCOtherW0))), ("closing of another shape", ap ob cvZ (C (Q ++ `CCOtherShape))),
    ("closing of another output (= none)", ap ob cvZ (C (Q ++ `CCOutNone))), ("closing of another output (exact)", ap ob cvZ (C (Q ++ `CCOutExact))),
    ("the all-world MachineCloses as hclL", ap ob cvZ (C (Q ++ `CCAllWorlds))), ("closing of another root", ap ob cvZ (C (Q ++ `CCOtherRoot))),
    ("carrier Y", ap ob (C ``cdvY) cl), ("carrier old", ap ob (C ``cdvOld) cl), ("obligation Y", ap (C ``HftObCDY) cvZ cl),
    ("hcl + hgate kept (S1x statement)", mkApp2 (C (Y ++ `HftFinalStmtOffLN)) ob cvZ)]
  for (what, m) in muts do
    diffTy s!"finalOffLNL_Z vs {what}" t m; nm := nm + 1
  logInfo m!"FGCIRCUIT23 SIGNATURES-C: synth_hftPcieOutByte_finalOffLNL_Z (hcl and hgate replaced by the one localised hclL) matches the independently written ExpFLNL; {nm} mutants rejected (no closing / another world / shape / output / root; all-world MachineCloses; carrier Y, old; obligation Y; hcl + hgate kept)"

/-! ## 4. HYPS, REMAINING -/

run_cmd liftTermElabM do
  let env ← getEnv
  let X := `Tools.ShippingFGCircuitS1zClose
  let ci ← getConstInfo (X ++ `synth_hftPcieOutByte_finalOffLNL_Z)
  let some ty ← unfoldDefinition? ci.type | throwError "the instance's type is not a definition"
  let names ← forallTelescope ty fun xs _ => do
    let mut hs : List (String × Lean.Expr) := []
    for x in xs do
      let d ← x.fvarId!.getDecl
      if d.binderInfo.isExplicit then hs := hs ++ [(d.userName.toString, ← instantiateMVars d.type)]
    return hs
  let expected := ["hlink", "L", "lvl", "env₀", "hstart", "hr", "hcell", "hchk", "hreadH", "hreadT", "hcd", "htop", "hclL"]
  unless names.map (·.1) == expected do throwError "hypotheses are {names.map (·.1)}, expected {expected}"
  for gone in ["hnoraw", "hcl", "hgate", "hsrc", "hhead", "hdRun", "hquiet", "hg", "hio", "hgates", "hRead", "hE", "hP", "hdesign"] do
    if (names.map (·.1)).contains gone then throwError "{gone} is a hypothesis"
  -- the limited scan: the type's constants and a ONE-level unfolding of the S1t/S1kStmt/S1u/S1x/S1z definitions (NOT the dependency closure)
  let diag : List Name := [``synthesizeCombinational, ``synthesizeCombinationalCore, ``synthesizeEntry, ``Tools.ShippingFGCircuitLinked.MachineDefinesLinked, ``Tools.ShippingFGCircuitBridge.PostRun,
    ``Tools.ShippingEntryReadsLinked.coreHead, ``synthesizeChild, ``HftObSrc, ``sorryAx, ``Tools.ShippingMachineEntry.MachineCloses, ``Tools.ShippingChildRunAKids.MachineClosesAtA, ``HftPostGate]
  for (n, t) in names do
    let mut used := t.getUsedConstants
    for c in t.getUsedConstants do
      if c.toString.startsWith "Tools.ShippingFGCircuitS1t" || c.toString.startsWith "Tools.ShippingFGCircuitS1kStmt" || c.toString.startsWith "Tools.ShippingFGCircuitS1u" || c.toString.startsWith "Tools.ShippingFGCircuitS1x" || c.toString.startsWith "Tools.ShippingFGCircuitS1z" then
        match env.find? c with
        | some (.defnInfo dd) => used := used ++ dd.value.getUsedConstants
        | _ => pure ()
    for b in diag do
      if used.contains b then throwError "hypothesis {n} mentions {b} (one-level scan)"
  let some (_, h) := names.find? (·.1 == "hclL") | throwError "hclL missing"
  unless h.getUsedConstants.contains (X ++ `HftCoreCloses) do throwError "hclL is not HftCoreCloses"
  let pp ← try pure (toString (← ppExpr h)) catch _ => pure s!"<constants: {h.getUsedConstants.toList.map (·.toString)}>"
  logInfo m!"FGCIRCUIT23 REMAINING hclL : {pp}  (the closing success of the machine run embedded in the target core run: closeLets accepts the transition and closeInstsGM's checks pass on the children's actual outputs; D.T-4; not derived here: the core run's result alone does not exclude the fallback route, which also returns a (Module × Design))"
  logInfo m!"FGCIRCUIT23 HYPS: HftFinalStmtOffLNL Ob CV = hlink L lvl env₀ hstart hr hcell hchk hreadH hreadT hcd htop hclL: {names.length} explicit hypotheses (S1x had 14: hcl and hgate are replaced by hclL; hgate is DERIVED by hftPostGate_of_local, hnoraw by hftObNoRawOff_of_local). The scan is the LIMITED one (the types, and a one-level unfolding of the pilot definitions); it does not show that no diagnostic entry occurs in the whole dependency closure"

/-! ## 5. AXIOMS -/

run_cmd liftTermElabM do
  let X := `Tools.ShippingFGCircuitS1zClose
  let names : List Name := [X ++ `coreCloses_of_machineCloses, X ++ `synthesizeFromConst_machine_invW, X ++ `coreOff_ranA, X ++ `closed_of_ranA, X ++ `hft_callsOk, X ++ `hft_slots, X ++ `hft_domB, X ++ `hft_outTy, X ++ `hft_nomem,
    X ++ `hftPostGate_of_local, X ++ `hftObNoRawOff_of_local, X ++ `synth_hftPcieOutByte_finalOffLNL, X ++ `synth_hftPcieOutByte_finalOffLNL_Z, X ++ `synth_hftPcieOutByte_finalOffLNL_Y, X ++ `synth_hftPcieOutByte_finalOffLNL_X]
  for nm in names do
    for ax in ← Lean.collectAxioms nm do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do throwError "{nm} uses {ax}"
  logInfo m!"FGCIRCUIT23 AXIOMS: {names.length} names, standard axioms only (no sorryAx, no native_decide)"

end Tests.Gen5.FGCircuitPilotCheck23
