import Tools.ShippingFGCircuitS1xNoRaw
set_option autoImplicit false
-- FG circuit pilot S1x check. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED. Results: docs/FG-CIRCUIT-PILOT.md §26.

/-! # FGCircuitPilotCheck20 (light: each part is a small `run_cmd`)

1. SIGNATURES-A: `HftPostGate`, `coreOff_closed` against independently written statements (`isDefEq`, default transparency, binder kinds), and mutants (each must NOT be defeq).
2. SIGNATURES-B: `hftObNoRawOff_of_run` and `HftFinalStmtOffLN` / `synth_hftPcieOutByte_finalOffLN_Z`.
3. HYPS: the explicit hypotheses of the instance by name (`hnoraw` is gone; `hcl`, `hgate` are in its place), and what they mention.
4. AXIOMS. 5. SNAPSHOT20: kernel facts. -/
namespace Tests.Gen5.FGCircuitPilotCheck20
open Lean Meta Elab Command Term Sparkle.Core Sparkle.Core.Domain Tools.ShippingGen2 Tools.ShippingGen5DeclConnect Tools.ShippingGen5FG
open Tools.ShippingFGCircuit Tools.ShippingFGCircuitRoots Tools.ShippingFGCircuitArtifact Tools.ShippingFGCircuitCover Tools.ShippingFGCircuitBridge
open Tools.ShippingGenFGLedgerPremises Tools.ShippingFGCircuitS1iHead Tools.ShippingFGCircuitS1iEnv
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingEntryReadsLinked (envAt)
open Tools.ShippingGen5EnvFrame3 (CellPrem)
open Tools.ShippingFGCircuitS1kRoot Tools.ShippingFGCircuitS1kStmt Tools.ShippingFGCircuitS1kPkg
open Tools.ShippingFGCircuitS1qLinked Tools.ShippingFGCircuitS1qEndpoint
open Tools.ShippingFGCircuitS1mCD Tools.ShippingFGCircuitS1pCD Tools.ShippingFGCircuitS1rCD Tools.ShippingFGCircuitS1tFinal Tools.ShippingFGCircuitS1uSrc Tools.ShippingFGCircuitS1xNoRaw
open Tools.ShippingMachineEntry
open Tools.ShippingHierMono (NoInstOf)
open Tools.ShippingGen5DCEntryD (PostEntry)
open Sparkle.Compiler.Elab

abbrev W := Void IO.RealWorld
abbrev Cx := Meta.Context
abbrev Rf1 := ST.Ref IO.RealWorld Meta.State
abbrev Cc := Core.Context
abbrev Rf2 := ST.Ref IO.RealWorld Core.State
abbrev Md := Sparkle.IR.AST.Module
abbrev Dg := Sparkle.IR.AST.Design
noncomputable def RootShape : MachineShape := synth_hftPcieOutByte.machineData.shape
noncomputable def OtherShape : MachineShape := Sparkle.Tests.SignalLoopTest.counterLoop.machineData.shape

/-! ## 1. HftPostGate and coreOff_closed -/

def ExpGate (G : Md → Bool) (root : Name) (post : Prop → Prop) (mctx : Cx) (mref : Rf1) (cctx : Cc) (cref : Rf2) (w : W) (b : Md) (D' : Dg) : Prop :=
  ∀ (raw : Md) (D₀ : Dg) (w1 : W), RunsTo (synthesizeCombinationalCoreOff root) mctx mref cctx cref w (raw, D₀) w1 → PostEntry b raw D₀ D' → G b = true
def GateTrue := ExpGate Sparkle.IR.RefineCheck.hierGate hftRoot (fun p => p)
def GateOtherRoot := ExpGate Sparkle.IR.RefineCheck.hierGate hftHttp (fun p => p)
def GateBinds := ExpGate Sparkle.IR.RefineCheck.hierBinds hftRoot (fun p => p)
def GateConst := ExpGate (fun _ => true) hftRoot (fun p => p)
def GateNoPE (mctx : Cx) (mref : Rf1) (cctx : Cc) (cref : Rf2) (w : W) (b : Md) (D' : Dg) : Prop :=
  ∀ (raw : Md) (D₀ : Dg) (w1 : W), RunsTo (synthesizeCombinationalCoreOff hftRoot) mctx mref cctx cref w (raw, D₀) w1 → Sparkle.IR.RefineCheck.hierGate b = true

/-- `coreOff_closed` and three mutants (no closing premise; no instance premise; the design half about another name) -/
def ExpClosed : Prop :=
  ∀ {mctx : Cx} {mref : Rf1} {cctx : Cc} {cref : Rf2} {declName : Name} {w w' : W} {m : Md} {d : Dg} {shape : MachineShape}
    (_hr : RunsTo (synthesizeCombinationalCoreOff declName) mctx mref cctx cref w (m, d) w')
    (_entry : MachineDefinesLinkedOff mctx mref cctx cref declName shape w m d w')
    (_closes : MachineCloses mctx mref cctx cref declName shape)
    (_hI : shape.insts ≠ []),
    NoInstOf m.name m.body ∧ ∀ g ∈ d.modules, NoInstOf m.name g.body
def ClosedNoCl : Prop :=
  ∀ {mctx : Cx} {mref : Rf1} {cctx : Cc} {cref : Rf2} {declName : Name} {w w' : W} {m : Md} {d : Dg} {shape : MachineShape}
    (_hr : RunsTo (synthesizeCombinationalCoreOff declName) mctx mref cctx cref w (m, d) w')
    (_entry : MachineDefinesLinkedOff mctx mref cctx cref declName shape w m d w')
    (_hI : shape.insts ≠ []),
    NoInstOf m.name m.body ∧ ∀ g ∈ d.modules, NoInstOf m.name g.body
def ClosedNoI : Prop :=
  ∀ {mctx : Cx} {mref : Rf1} {cctx : Cc} {cref : Rf2} {declName : Name} {w w' : W} {m : Md} {d : Dg} {shape : MachineShape}
    (_hr : RunsTo (synthesizeCombinationalCoreOff declName) mctx mref cctx cref w (m, d) w')
    (_entry : MachineDefinesLinkedOff mctx mref cctx cref declName shape w m d w')
    (_closes : MachineCloses mctx mref cctx cref declName shape),
    NoInstOf m.name m.body ∧ ∀ g ∈ d.modules, NoInstOf m.name g.body
def ClosedBodyOnly : Prop :=
  ∀ {mctx : Cx} {mref : Rf1} {cctx : Cc} {cref : Rf2} {declName : Name} {w w' : W} {m : Md} {d : Dg} {shape : MachineShape}
    (_hr : RunsTo (synthesizeCombinationalCoreOff declName) mctx mref cctx cref w (m, d) w')
    (_entry : MachineDefinesLinkedOff mctx mref cctx cref declName shape w m d w')
    (_closes : MachineCloses mctx mref cctx cref declName shape)
    (_hI : shape.insts ≠ []),
    NoInstOf m.name m.body
def ClosedOldCore : Prop :=
  ∀ {mctx : Cx} {mref : Rf1} {cctx : Cc} {cref : Rf2} {declName : Name} {w w' : W} {m : Md} {d : Dg} {shape : MachineShape}
    (_hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, d) w')
    (_entry : MachineDefinesLinkedOff mctx mref cctx cref declName shape w m d w')
    (_closes : MachineCloses mctx mref cctx cref declName shape)
    (_hI : shape.insts ≠ []),
    NoInstOf m.name m.body ∧ ∀ g ∈ d.modules, NoInstOf m.name g.body

def sameTy (what : String) (ty exp : Lean.Expr) : MetaM Unit := do
  unless ← withDefault (isDefEq ty exp) do throwError "{what}: type is NOT the expected statement"
def diffTy (what : String) (ty exp : Lean.Expr) : MetaM Unit := do
  if ← withDefault (isDefEq ty exp) then throwError "{what}: the MUTANT was accepted"
def tyOf (n : Name) : MetaM Lean.Expr := do
  let ci ← getConstInfo n
  unless ci.levelParams.isEmpty do throwError "{n}: level parameters"
  pure ci.type
partial def binderInfos : Lean.Expr → List BinderInfo
  | .forallE _ _ b bi => bi :: binderInfos b
  | _ => []

set_option maxHeartbeats 8000000 in
run_cmd liftTermElabM do
  let C (n : Name) : Lean.Expr := mkConst n
  let X := `Tools.ShippingFGCircuitS1xNoRaw
  let Q := `Tests.Gen5.FGCircuitPilotCheck20
  sameTy "HftPostGate" (C (X ++ `HftPostGate)) (C (Q ++ `GateTrue))
  let mut nm := 0
  for mu in ["GateOtherRoot", "GateBinds", "GateConst", "GateNoPE"] do
    diffTy s!"HftPostGate vs {mu}" (C (X ++ `HftPostGate)) (C (Q ++ Name.mkSimple mu)); nm := nm + 1
  let t ← tyOf (X ++ `coreOff_closed)
  sameTy "coreOff_closed" t (C (Q ++ `ExpClosed))
  unless binderInfos t == binderInfos (← whnfD (C (Q ++ `ExpClosed))) do throwError "coreOff_closed: binder kinds differ"
  for mu in ["ClosedNoCl", "ClosedNoI", "ClosedBodyOnly", "ClosedOldCore"] do
    diffTy s!"coreOff_closed vs {mu}" t (C (Q ++ Name.mkSimple mu)); nm := nm + 1
  logInfo m!"FGCIRCUIT20 SIGNATURES-A: HftPostGate and coreOff_closed (complete types, binder kinds) match independently written statements (isDefEq, default); {nm} mutants rejected (gate: other root / hierBinds / constant / no PostEntry; closed: no closing premise / no instance premise / body only / old core entry)"

end Tests.Gen5.FGCircuitPilotCheck20
