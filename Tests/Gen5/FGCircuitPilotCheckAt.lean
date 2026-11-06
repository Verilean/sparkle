import Tools.ShippingFGCircuitRootsAt
set_option autoImplicit false
-- FG circuit pilot S1b check. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED. Results: docs/FG-CIRCUIT-PILOT.md.

/-! # FGCircuitPilotCheckAt

Independent signature check of the published wrappers. Each EXPECTED type below is written here (a separate statement, with literal names,
literal shapes, the start environment spelled `envAt cref w`), and the wrapper's actual type is compared to it by `isDefEq` in `MetaM` — a
comparison that can FAIL (`example : T = T := rfl` and `#check` cannot). The same comparison is run against MUTANTS (wrong root name, wrong
shape/observation, wrong data, source meaning at another environment, `RootInEnv` at another environment, wrong returned module, the old free-env
statement); every mutant must be REJECTED.

Two kinds of claim are kept apart:
* what this build's environment HAS (the SNAPSHOT lines: the quoted values and the boundary rows equal this environment's declarations — a fact
  about this one build, checked in `MetaM`);
* what the theorems say about ANY run's environment (only the named hypotheses `hE`, `hB`, `hr`, `hd`; none is supplied by a theorem yet). -/
namespace Tests.Gen5.FGCircuitPilotCheckAt
open Lean Meta Elab Command Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Tools.ShippingGen2 Tools.ShippingGen5DeclConnect
open Tools.ShippingFGCircuit Tools.ShippingFGCircuitRoots Sparkle.Tests.SignalLoopTest
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingMachineEntry (MachineDefines MachineCloses)
open Tools.ShippingEntryReadsLinked (envAt)

abbrev Cref := ST.Ref IO.RealWorld Core.State
abbrev W := Void IO.RealWorld
def emptyModule : Sparkle.IR.AST.Module := { name := "", inputs := [], outputs := [], wires := [], body := [] }

/-! ## expected statements (parameters are the things a mutant changes) -/

/-- EH: environment of the `RootInEnv` premise; ES: environment of the `SourceDenotes` claim; sel: which module the trace talks about -/
def ExpMonoRoot (EH ES : Cref → W → W → Environment) (sel : Sparkle.IR.AST.Module → Sparkle.IR.AST.Design → Sparkle.IR.AST.Module)
    (X : Name) (ty val : Lean.Expr) (sh : SigShape) (dd : Tools.ShippingMachineAuto.MachineData) : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : Cref} {w w' : W}
    {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design} {d : DefinitionVal},
    RootInEnv (EH cref w w') X ty val d →
    RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalCore X [] false) mctx mref cctx cref w (m, design) w' →
    MachineDefines mctx mref cctx cref X dd.shape →
    ∃ mm : MonoTy sh, SourceDenotesMono (ES cref w w') X [] sh mm ∧
      Tools.ShippingMachineAuto.MachineTrace X dd (sel m design) (fun _ : Unit => defaultDomain)
        (fun _ bools bits => monoObs sh mm bools bits)

def ExpMonoShips (EH ES : Cref → W → W → Environment) (sel : Sparkle.IR.AST.Module → Sparkle.IR.AST.Design → Sparkle.IR.AST.Module)
    (X : Name) (ty val : Lean.Expr) (sh : SigShape) (dd : Tools.ShippingMachineAuto.MachineData) : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : Cref} {w w' : W}
    {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design} {d : DefinitionVal},
    RootInEnv (EH cref w w') X ty val d →
    RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational X) mctx mref cctx cref w (b, design) w' →
    MachineDefines mctx mref cctx cref X dd.shape →
    ∃ mm : MonoTy sh, SourceDenotesMono (ES cref w w') X [] sh mm ∧
      WiredConclusion X dd (fun _ : Unit => defaultDomain) (fun _ bools bits => monoObs sh mm bools bits) (sel b design)

def ExpPolyRoot (EH ES EB : Cref → W → W → Environment) (sel : Sparkle.IR.AST.Module → Sparkle.IR.AST.Design → Sparkle.IR.AST.Module)
    (X : Name) (ty val : Lean.Expr) (sh : SigShape) (dd : Tools.ShippingMachineAuto.MachineData) : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : Cref} {w w' : W}
    {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design} {d : DefinitionVal},
    RootInEnv (EH cref w w') X ty val d →
    BoundaryRowsInEnv (EB cref w w') →
    RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalCore X [] false) mctx mref cctx cref w (m, design) w' →
    MachineDefines mctx mref cctx cref X dd.shape →
    ∃ mm : sh.Ty, SourceDenotes (ES cref w w') X [] sh mm ∧
      Tools.ShippingMachineAuto.MachineTrace X dd (sel m design) (fun i : DomainConfig => i)
        (fun i bools bits => sh.obs (dom := fun i : DomainConfig => i) mm i bools bits)

def ExpPolyShips (EH ES EB : Cref → W → W → Environment) (sel : Sparkle.IR.AST.Module → Sparkle.IR.AST.Design → Sparkle.IR.AST.Module)
    (X : Name) (ty val : Lean.Expr) (sh : SigShape) (dd : Tools.ShippingMachineAuto.MachineData) : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : Cref} {w w' : W}
    {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design} {d : DefinitionVal},
    RootInEnv (EH cref w w') X ty val d →
    BoundaryRowsInEnv (EB cref w w') →
    RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational X) mctx mref cctx cref w (b, design) w' →
    MachineDefines mctx mref cctx cref X dd.shape →
    ∃ mm : sh.Ty, SourceDenotes (ES cref w w') X [] sh mm ∧
      WiredConclusion X dd (fun i : DomainConfig => i) (fun i bools bits => sh.obs (dom := fun i : DomainConfig => i) mm i bools bits)
        (sel b design)

def ExpCloses (X : Name) (dd : Tools.ShippingMachineAuto.MachineData) : Prop :=
  ∀ (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State) (cctx : Core.Context) (cref : Cref), MachineCloses mctx mref cctx cref X dd.shape

/-! ## the parameters: expected values and single-point mutations -/
def eS : Cref → W → W → Environment := fun cref w _ => envAt cref w      -- the START world of the run
def eE : Cref → W → W → Environment := fun cref _ w' => envAt cref w'    -- mutant: the END world
def selM : Sparkle.IR.AST.Module → Sparkle.IR.AST.Design → Sparkle.IR.AST.Module := fun m _ => m
def selX : Sparkle.IR.AST.Module → Sparkle.IR.AST.Design → Sparkle.IR.AST.Module := fun _ _ => emptyModule  -- mutant: another module

-- shapes written out (not the `sh…` constants of the implementation)
def shC : SigShape := { args := [], res := .one (.bits 8) }
def shS : SigShape := { args := [.bits 8], res := .one (.bits 8) }
def shE : SigShape := { args := [.bool], res := .one (.bits 8) }
def shA : SigShape := { args := [.bool, .bool], res := .one (.bits 2) }

noncomputable def dC : Tools.ShippingMachineAuto.MachineData := counterLoop.machineData
noncomputable def dS : Tools.ShippingMachineAuto.MachineData := shift4Loop.machineData
noncomputable def dE : Tools.ShippingMachineAuto.MachineData := counterEnableLoop.machineData
noncomputable def dA : Tools.ShippingMachineAuto.MachineData := Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData

def nC : Name := ``Sparkle.Tests.SignalLoopTest.counterLoop
def nS : Name := ``Sparkle.Tests.SignalLoopTest.shift4Loop
def nE : Name := ``Sparkle.Tests.SignalLoopTest.counterEnableLoop
def nA : Name := ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal

def ExpCounterRoot : Prop := ExpMonoRoot eS eS selM nC counterLoopType counterLoopValue shC dC
def ExpShift4Root : Prop := ExpMonoRoot eS eS selM nS shift4LoopType shift4LoopValue shS dS
def ExpEnableRoot : Prop := ExpMonoRoot eS eS selM nE counterEnableLoopType counterEnableLoopValue shE dE
def ExpArbiterRoot : Prop := ExpPolyRoot eS eS eS selM nA arbiterType arbiterValue shA dA
def ExpCounterShips : Prop := ExpMonoShips eS eS selM nC counterLoopType counterLoopValue shC dC
def ExpShift4Ships : Prop := ExpMonoShips eS eS selM nS shift4LoopType shift4LoopValue shS dS
def ExpEnableShips : Prop := ExpMonoShips eS eS selM nE counterEnableLoopType counterEnableLoopValue shE dE
def ExpArbiterShips : Prop := ExpPolyShips eS eS eS selM nA arbiterType arbiterValue shA dA

-- mutants of the counter root
def MutName : Prop := ExpMonoRoot eS eS selM nS counterLoopType counterLoopValue shC dC            -- wrong root name
def MutValue : Prop := ExpMonoRoot eS eS selM nC shift4LoopType shift4LoopValue shC dC            -- wrong quoted type/value
def MutShape : Prop := ExpMonoRoot eS eS selM nC counterLoopType counterLoopValue shS dC          -- wrong shape / observation
def MutData : Prop := ExpMonoRoot eS eS selM nC counterLoopType counterLoopValue shC dS           -- wrong machine data
def MutHypEnv : Prop := ExpMonoRoot eE eS selM nC counterLoopType counterLoopValue shC dC         -- RootInEnv at the END world
def MutDenEnv : Prop := ExpMonoRoot eS eE selM nC counterLoopType counterLoopValue shC dC         -- SourceDenotes at the END world
def MutModule : Prop := ExpMonoRoot eS eS selX nC counterLoopType counterLoopValue shC dC         -- trace of another module
def MutShipsName : Prop := ExpMonoShips eS eS selM nS counterLoopType counterLoopValue shC dC
def MutShipsDenEnv : Prop := ExpMonoShips eS eE selM nC counterLoopType counterLoopValue shC dC
def MutShipsModule : Prop := ExpMonoShips eS eS selX nC counterLoopType counterLoopValue shC dC
def MutArbName : Prop := ExpPolyRoot eS eS eS selM nC arbiterType arbiterValue shA dA
def MutArbShape : Prop := ExpPolyRoot eS eS eS selM nA arbiterType arbiterValue shS dA
def MutArbBoundaryEnv : Prop := ExpPolyRoot eS eS eE selM nA arbiterType arbiterValue shA dA     -- boundary rows at the END world
def MutArbDenEnv : Prop := ExpPolyRoot eS eE eS selM nA arbiterType arbiterValue shA dA
def MutArbShipsModule : Prop := ExpPolyShips eS eS eS selX nA arbiterType arbiterValue shA dA
def MutClosesName : Prop := ExpCloses nS dC
def ExpClosesC : Prop := ExpCloses nC dC
def ExpClosesS : Prop := ExpCloses nS dS
def ExpClosesE : Prop := ExpCloses nE dE
def ExpClosesA : Prop := ExpCloses nA dA

/-! ## the comparison (MetaM): actual theorem type vs expected, and mutants rejected -/

/-- unfold ONLY the check's own definitions and the implementation's shape constants (never `machineData`, which would evaluate): the comparison is
then structural, so a mutant differing in one constant is rejected cheaply and a match is an actual identity of statements. -/
def whitelist : List Name := [``ExpMonoRoot, ``ExpMonoShips, ``ExpPolyRoot, ``ExpPolyShips, ``ExpCloses,
  ``ExpCounterRoot, ``ExpShift4Root, ``ExpEnableRoot, ``ExpArbiterRoot, ``ExpCounterShips, ``ExpShift4Ships, ``ExpEnableShips, ``ExpArbiterShips,
  ``MutName, ``MutValue, ``MutShape, ``MutData, ``MutHypEnv, ``MutDenEnv, ``MutModule, ``MutShipsName, ``MutShipsDenEnv, ``MutShipsModule,
  ``MutArbName, ``MutArbShape, ``MutArbBoundaryEnv, ``MutArbDenEnv, ``MutArbShipsModule, ``MutClosesName, ``ExpClosesC, ``ExpClosesS, ``ExpClosesE, ``ExpClosesA,
  ``eS, ``eE, ``selM, ``selX, ``emptyModule, ``shC, ``shS, ``shE, ``shA, ``dC, ``dS, ``dE, ``dA, ``nC, ``nS, ``nE, ``nA,
  ``shCounter, ``shShift4, ``shEnable, ``shArbiter]

def norm (e : Lean.Expr) : MetaM Lean.Expr :=
  Meta.transform e (post := fun e => do
    if let .const c _ := e.getAppFn then
      if whitelist.contains c then
        if let some e' ← unfoldDefinition? e then return .visit e'.headBeta
    return .done e)

set_option maxHeartbeats 4000000 in
run_cmd liftTermElabM do
  let same (thm exp : Name) : MetaM Unit := do
    let ci ← getConstInfo thm
    unless ci.levelParams.isEmpty do throwError "{thm}: level parameters"
    let a ← norm ci.type
    let e ← norm (mkConst exp)
    unless ← withReducible (isDefEq a e) do throwError "{thm}: type is NOT the expected statement {exp}"
  let differs (thm mu0 : Name) : MetaM Unit := do
    let ci ← getConstInfo thm
    let a ← norm ci.type
    let e ← norm (mkConst mu0)
    if ← withReducible (isDefEq a e) then throwError "{thm}: the MUTANT {mu0} was accepted"
  let R := `Tools.ShippingFGCircuitRoots
  let roots : List (Name × Name) := [(R ++ `counterLoop_root_at, ``ExpCounterRoot), (R ++ `shift4Loop_root_at, ``ExpShift4Root),
    (R ++ `counterEnableLoop_root_at, ``ExpEnableRoot), (R ++ `arbiterSignal_root_at, ``ExpArbiterRoot),
    (R ++ `counterLoop_ships_at, ``ExpCounterShips), (R ++ `shift4Loop_ships_at, ``ExpShift4Ships),
    (R ++ `counterEnableLoop_ships_at, ``ExpEnableShips), (R ++ `arbiterSignal_ships_at, ``ExpArbiterShips)]
  for (t, e) in roots do same t e
  -- the wrappers do NOT carry the closes premise (it is supplied inside), and the supplied theorem has the expected type
  for (t, _) in roots do
    let ci ← getConstInfo t
    if (ci.type.find? (·.isConstOf ``MachineCloses)).isSome then throwError "{t}: still has a MachineCloses premise"
  for (c, e) in [(nC, ``ExpClosesC), (nS, ``ExpClosesS), (nE, ``ExpClosesE), (nA, ``ExpClosesA)] do
    same (c ++ `machine_closes) e
  differs (nC ++ `machine_closes) ``MutClosesName
  let mut nm : Nat := 0
  for (t, mu) in [(R ++ `counterLoop_root_at, ``MutName), (R ++ `counterLoop_root_at, ``MutValue), (R ++ `counterLoop_root_at, ``MutShape),
      (R ++ `counterLoop_root_at, ``MutData), (R ++ `counterLoop_root_at, ``MutHypEnv), (R ++ `counterLoop_root_at, ``MutDenEnv),
      (R ++ `counterLoop_root_at, ``MutModule), (R ++ `counterLoop_ships_at, ``MutShipsName), (R ++ `counterLoop_ships_at, ``MutShipsDenEnv),
      (R ++ `counterLoop_ships_at, ``MutShipsModule), (R ++ `arbiterSignal_root_at, ``MutArbName), (R ++ `arbiterSignal_root_at, ``MutArbShape),
      (R ++ `arbiterSignal_root_at, ``MutArbBoundaryEnv), (R ++ `arbiterSignal_root_at, ``MutArbDenEnv),
      (R ++ `arbiterSignal_ships_at, ``MutArbShipsModule)] do
    differs t mu
    nm := nm + 1
  -- the OLD free-environment statements are not the expected ones (env independent of the run)
  for (t, e) in [(R ++ `counterLoop_root, ``ExpCounterRoot), (R ++ `shift4Loop_root, ``ExpShift4Root),
      (R ++ `counterEnableLoop_root, ``ExpEnableRoot), (R ++ `arbiterSignal_root, ``ExpArbiterRoot)] do
    differs t e
    nm := nm + 1
  logInfo m!"FGCIRCUIT SIGNATURES: 8 wrapper types (4 roots, 4 ships) equal their independently written expected statements; no wrapper has a MachineCloses premise; 4 machine_closes theorems have the expected type; {nm} mutants rejected (wrong root/value/shape/data, RootInEnv or SourceDenotes or boundary rows at another environment, wrong module, the old free-env roots)"

/-! ## SNAPSHOT: facts about THIS build's environment (not a claim about the environment of any run) -/

run_cmd liftTermElabM do
  let env ← getEnv
  -- the arbiter's three auxiliary declarations, as `BoundaryRowsInEnv` states them
  for (nm, k) in [(`stIdle, 0), (`stGrantA, 1), (`stGrantB, 2)] do
    let some (.defnInfo d) := env.find? (privAbbrev nm) | throwError "{nm}: not a definition in this environment"
    unless d.levelParams.isEmpty && d.type == eBV 2 && d.value == eBVLit 2 k do throwError "{nm}: differs from bvAbbrevRow's literal"
  logInfo "FGCIRCUIT SNAPSHOT: in THIS build's environment the three arbiter abbreviations equal bvAbbrevRow's literals (BoundaryRowsInEnv holds here); this is not a statement about any run's environment, which is the hypothesis hB"

/-! ## axioms -/
run_cmd liftTermElabM do
  let R := `Tools.ShippingFGCircuitRoots
  let names : List Name := [R ++ `counterLoop_denotes, R ++ `shift4Loop_denotes, R ++ `counterEnableLoop_denotes, R ++ `arbiterSignal_denotes,
    R ++ `counterLoop_root_at, R ++ `shift4Loop_root_at, R ++ `counterEnableLoop_root_at, R ++ `arbiterSignal_root_at,
    R ++ `counterLoop_ships_at, R ++ `shift4Loop_ships_at, R ++ `counterEnableLoop_ships_at, R ++ `arbiterSignal_ships_at,
    nC ++ `machine_closes, nS ++ `machine_closes, nE ++ `machine_closes, nA ++ `machine_closes]
  for nm in names do
    for ax in ← Lean.collectAxioms nm do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do throwError "{nm} uses {ax}"
  logInfo m!"FGCIRCUIT AXIOMS-AT: {names.length} names, standard axioms only"

end Tests.Gen5.FGCircuitPilotCheckAt
