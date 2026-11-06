import Tests.Gen5.FGCircuitPilotCheck8
import Tools.ShippingFGCircuitS1lReader
set_option autoImplicit false
-- FG circuit pilot S1l check. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED. Results: docs/FG-CIRCUIT-PILOT.md §16.

/-! # FGCircuitPilotCheck10

1. SIGNATURES: complete expected types, written independently of the theorems, for `checkedEnv_of_decl`, `counterLoop_dataOfAt`, `counterLoop_gates`, `counterLoop_checkedEnv_of_finite`, `counterLoop_final11` and the constructors of the two named Props
   `CounterLoopExtern` / `CounterLoopEnvFacts`; one-point MUTANTS rejected (another root / value / shape, wrong polarity of the instance predicate, a dropped fact, the end world).
2. HYPS: the explicit hypotheses of `counterLoop_final11` (and that `hchk : CheckedStart` is no longer one of them).
3. AXIOMS of every new name.
4. SNAPSHOT10: the named facts are EVALUATED on this build's ONE environment in `MetaM` (an evaluation, not a supply of the hypotheses), and the finite-input claim (the gates and the data depend on the instance predicate / `proj` only at the value / `Signal.loop`) is probed with altered arguments. -/
namespace Tests.Gen5.FGCircuitPilotCheck10
open Lean Meta Elab Command Term Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Tools.ShippingGen2 Tools.ShippingGen5DeclConnect Tools.ShippingGen5FG
open Tools.ShippingFGCircuit Tools.ShippingFGCircuitRoots Tools.ShippingFGCircuitArtifact Tools.ShippingFGCircuitCover Tools.ShippingFGCircuitBridge
open Tools.ShippingFGCircuitLinked Tools.ShippingFGCircuitFinal4 Tools.ShippingFGCircuitRoots4
open Tools.ShippingFGCircuitS1hGates Tools.ShippingFGCircuitS1hQuote Tools.ShippingFGCircuitS1iHead Tools.ShippingFGCircuitS1iEnv Tools.ShippingFGCircuitS1lReader
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingEntryReadsLinked (envAt CoreSaved coreHead)
open Tools.ShippingMachineAuto (MachineData)
open Tools.ShippingStRefCorrespondence (ReadWorld)
open Tools.ShippingGen5Env (ReadsAt)
open Sparkle.Compiler.Elab Sparkle.Tests.SignalLoopTest Tools.ShippingGenFGLedgerPremises
open Tests.Gen5.FGCircuitPilotCheck5 (W GPd explicitBinders binderInfos dataExprOf shapeExprOf literalExpr)
open Tests.Gen5.FGCircuitPilotCheck7 (ZS ZE)

/-! ## 1. expected statements, written independently -/

/-- `checkedEnv_of_decl`: knobs: which environment each derived argument is taken from, and whether the gate / reader premise is present -/
def ExpOfDecl (ipE uiE seE : Environment → Environment → Environment) (needG needR : Bool) : Prop :=
  ∀ {lvl : Lean.Expr → Nat} {env₀ : Environment} {X : Name} {ty val : Lean.Expr} {d : DefinitionVal} {dd : MachineData},
    (env₀.find? X = some (.defnInfo d) ∧ d.levelParams = [] ∧ d.type = ty ∧ d.value = val) →
    (if needG then
      (certifiedShape? false [] (entryConst true false [] (.defnInfo d) (instancePredicate (ipE env₀ env₀)) (userInliner (uiE env₀ env₀)) (structEnv (seE env₀ env₀)))).isNone = true ∧
      (mixedCertifiedShape? false [] (entryConst true false [] (.defnInfo d) (instancePredicate (ipE env₀ env₀)) (userInliner (uiE env₀ env₀)) (structEnv (seE env₀ env₀)))
        (instancePredicate (ipE env₀ env₀))).isNone = true else True) →
    (if needR then
      machineShape? false [] (entryConst true false [] (.defnInfo d) (instancePredicate (ipE env₀ env₀)) (userInliner (uiE env₀ env₀)) (structEnv (seE env₀ env₀))) (structEnv (seE env₀ env₀)) = some dd.shape ∧
      Tools.ShippingGen5DataOf.dataOfAt lvl (entryConst true false [] (.defnInfo d) (instancePredicate (ipE env₀ env₀)) (userInliner (uiE env₀ env₀)) (structEnv (seE env₀ env₀)))
        (structEnv (seE env₀ env₀)) dd.shape = some dd else True) →
    CheckedEnv lvl env₀ X ty val dd
def OfDeclTrue := ExpOfDecl (fun e _ => e) (fun e _ => e) (fun e _ => e) true true
def MutOfDeclNoGates := ExpOfDecl (fun e _ => e) (fun e _ => e) (fun e _ => e) false true
def MutOfDeclNoReader := ExpOfDecl (fun e _ => e) (fun e _ => e) (fun e _ => e) true false

/-- the closed facts about the `partial`/extern helpers: knobs: the term the helpers are applied to, the arity of the `runCircuitH` test -/
def ExpExternMk (v : Lean.Expr) (arity : Nat) : Prop :=
  Sparkle.Compiler.MachTupleIn.packTupleInputs counterLoopValue = counterLoopValue →
  Sparkle.Compiler.MachRawSurface.rootFloat counterLoopValue = v →
  counterLoopValue.find? (fun t => t.isAppOfArity ``Sparkle.Core.runCircuitH arity) = none →
  CounterLoopExtern
def ExternMkTrue := ExpExternMk counterLoopValue 8
def MutExternValue := ExpExternMk shift4LoopValue 8
def MutExternArity := ExpExternMk counterLoopValue 7

/-- the environment facts: knobs: root value, type, shape's data, polarity of the instance predicate, the name `proj` is asked at -/
def ExpEnvFactsMk (val ty : Lean.Expr) (dd : MachineData) (pol : Bool) (loopName : Name) : Prop :=
  ∀ {env₀ : Environment},
    (∃ d : DefinitionVal, (env₀.find? ``counterLoop = some (.defnInfo d) ∧ d.levelParams = [] ∧ d.type = counterLoopType ∧ d.value = val) ∧
      machineShape? false [] (.defnInfo d) (structEnv env₀) = some dd.shape) →
    userInliner env₀ counterLoopValue = counterLoopValue →
    userInliner env₀ ty = counterLoopType →
    instancePredicate env₀ counterLoopValue = pol →
    (structEnv env₀).proj loopName = none →
    CounterLoopEnvFacts env₀
def EnvFactsMkTrue := ExpEnvFactsMk counterLoopValue counterLoopType counterLoop.machineData false ``Sparkle.Core.Signal.Signal.loop
def MutEnvValue := ExpEnvFactsMk shift4LoopValue counterLoopType counterLoop.machineData false ``Sparkle.Core.Signal.Signal.loop
def MutEnvTy := ExpEnvFactsMk counterLoopValue shift4LoopType counterLoop.machineData false ``Sparkle.Core.Signal.Signal.loop
def MutEnvData := ExpEnvFactsMk counterLoopValue counterLoopType shift4Loop.machineData false ``Sparkle.Core.Signal.Signal.loop
def MutEnvPolarity := ExpEnvFactsMk counterLoopValue counterLoopType counterLoop.machineData true ``Sparkle.Core.Signal.Signal.loop
def MutEnvName := ExpEnvFactsMk counterLoopValue counterLoopType counterLoop.machineData false ``Sparkle.Core.Signal.Signal.register

/-- `counterLoop_dataOfAt` -/
def ExpDataOfAt (dd : MachineData) (fuel : Nat) (needX : Bool) : Prop :=
  ∀ (lvl : Lean.Expr → Nat), lvl counterLoop.machineData.shape.body = fuel →
    ∀ (d : DefinitionVal), d.type = counterLoopType → d.value = counterLoopValue →
    ∀ (se : StructEnv), se.proj ``Sparkle.Core.Signal.Signal.loop = none → (if needX then CounterLoopExtern else True) →
      Tools.ShippingGen5DataOf.dataOfAt lvl (.defnInfo d) se counterLoop.machineData.shape = some dd
def DataOfAtTrue := ExpDataOfAt counterLoop.machineData 1000000 true
def MutDataOfAtData := ExpDataOfAt shift4Loop.machineData 1000000 true
def MutDataOfAtFuel := ExpDataOfAt counterLoop.machineData 1000001 true
def MutDataOfAtNoX := ExpDataOfAt counterLoop.machineData 1000000 false

/-- `counterLoop_gates` -/
def ExpGatesLoop (pol : Bool) (needIp : Bool) : Prop :=
  ∀ (d : DefinitionVal), d.type = counterLoopType → d.value = counterLoopValue →
    ∀ (ip : Lean.Expr → Bool), (if needIp then ip counterLoopValue = pol else True) →
      (certifiedShape? false [] (.defnInfo d)).isNone = true ∧ (mixedCertifiedShape? false [] (.defnInfo d) ip).isNone = true
def GatesLoopTrue := ExpGatesLoop false true
def MutGatesPol := ExpGatesLoop true true
def MutGatesNoIp := ExpGatesLoop false false

/-- `counterLoop_checkedEnv_of_finite` -/
def ExpCheckedFin (dd : MachineData) (ty val : Lean.Expr) (fuel : Nat) (needX needF : Bool) : Prop :=
  ∀ (lvl : Lean.Expr → Nat) (env₀ : Environment), lvl counterLoop.machineData.shape.body = fuel →
    (if needX then CounterLoopExtern else True) → (if needF then CounterLoopEnvFacts env₀ else True) →
      CheckedEnv lvl env₀ ``counterLoop ty val dd
def CheckedFinTrue := ExpCheckedFin counterLoop.machineData counterLoopType counterLoopValue 1000000 true true
def MutCFData := ExpCheckedFin shift4Loop.machineData counterLoopType counterLoopValue 1000000 true true
def MutCFVal := ExpCheckedFin counterLoop.machineData counterLoopType shift4LoopValue 1000000 true true
def MutCFFuel := ExpCheckedFin counterLoop.machineData counterLoopType counterLoopValue 999999 true true
def MutCFNoX := ExpCheckedFin counterLoop.machineData counterLoopType counterLoopValue 1000000 false true
def MutCFNoF := ExpCheckedFin counterLoop.machineData counterLoopType counterLoopValue 1000000 true false

/-- `counterLoop_final11`: knobs: where `HeadAt` starts, where the link `ReadsAt` is read, the environment of the conclusion, the data, the post root, and which finite premise is present -/
def ExpF11 (hhw rdw : W → W → W) (eC : Environment → ST.Ref IO.RealWorld Core.State → W → W → Environment) (lvlBody : Lean.Expr) (postRoot : Name)
    (needLvl needX needF : Bool) : Prop :=
  ∀ {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (lvl : Lean.Expr → Nat) (env₀ : Environment)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : W} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design},
    Start L mctx cctx w →
    RunsTo (synthesizeCombinational ``counterLoop) mctx mref cctx cref w (b, D') w' →
    (∀ (s : CoreSaved) (w1 : W), RunsTo (coreHead ``counterLoop) mctx mref cctx cref (hhw w w') s w1 → envAt cref w1 = envAt cref (hhw w w')) →
    ReadWorld cref →
    (if needLvl then lvl lvlBody = 1000000 else True) →
    (if needX then CounterLoopExtern else True) →
    (if needF then CounterLoopEnvFacts env₀ else True) →
    ReadsAt env₀ cref (rdw w w') →
    (∃ raw, PostRun mctx mref cctx cref w postRoot D' b raw) ∧
    ∃ (mm : MonoTy shCounter) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMono (eC env₀ cref w w') (GPd (ι := ι) lvl (eC env₀ cref w w'))
        (PostRun mctx mref cctx cref w postRoot D') ``counterLoop shCounter mm b D' p
def F11True := ExpF11 (fun w _ => w) (fun w _ => w) ZS counterLoop.machineData.shape.body ``counterLoop true true true
def M11HeadEnd := ExpF11 (fun _ w' => w') (fun w _ => w) ZS counterLoop.machineData.shape.body ``counterLoop true true true
def M11LinkEnd := ExpF11 (fun w _ => w) (fun _ w' => w') ZS counterLoop.machineData.shape.body ``counterLoop true true true
def M11ConclEnd := ExpF11 (fun w _ => w) (fun w _ => w) ZE counterLoop.machineData.shape.body ``counterLoop true true true
def M11Data := ExpF11 (fun w _ => w) (fun w _ => w) ZS shift4Loop.machineData.shape.body ``counterLoop true true true
def M11Post := ExpF11 (fun w _ => w) (fun w _ => w) ZS counterLoop.machineData.shape.body ``shift4Loop true true true
def M11NoLvl := ExpF11 (fun w _ => w) (fun w _ => w) ZS counterLoop.machineData.shape.body ``counterLoop false true true
def M11NoX := ExpF11 (fun w _ => w) (fun w _ => w) ZS counterLoop.machineData.shape.body ``counterLoop true false true
def M11NoF := ExpF11 (fun w _ => w) (fun w _ => w) ZS counterLoop.machineData.shape.body ``counterLoop true true false

def whitelist : List Name := [``ExpOfDecl, ``OfDeclTrue, ``MutOfDeclNoGates, ``MutOfDeclNoReader, ``ExpExternMk, ``ExternMkTrue, ``MutExternValue, ``MutExternArity,
  ``ExpEnvFactsMk, ``EnvFactsMkTrue, ``MutEnvValue, ``MutEnvTy, ``MutEnvData, ``MutEnvPolarity, ``MutEnvName,
  ``ExpDataOfAt, ``DataOfAtTrue, ``MutDataOfAtData, ``MutDataOfAtFuel, ``MutDataOfAtNoX, ``ExpGatesLoop, ``GatesLoopTrue, ``MutGatesPol, ``MutGatesNoIp,
  ``ExpCheckedFin, ``CheckedFinTrue, ``MutCFData, ``MutCFVal, ``MutCFFuel, ``MutCFNoX, ``MutCFNoF,
  ``ExpF11, ``F11True, ``M11HeadEnd, ``M11LinkEnd, ``M11ConclEnd, ``M11Data, ``M11Post, ``M11NoLvl, ``M11NoX, ``M11NoF,
  ``Tests.Gen5.FGCircuitPilotCheck7.ZS, ``Tests.Gen5.FGCircuitPilotCheck7.ZE, ``Tests.Gen5.FGCircuitPilotCheck5.GPd,
  -- definitions under test
  ``HeadAt, ``RootInEnv, ``GatesOnDecl, ``ReaderOnDecl, ``EntryOfDecl]

def norm (e : Lean.Expr) : MetaM Lean.Expr :=
  Meta.transform e (post := fun e => do
    let e := e.headBeta
    if let .const c _ := e.getAppFn then
      if whitelist.contains c then
        if let some e' ← unfoldDefinition? e then return .visit e'.headBeta
    return .done e)

set_option maxHeartbeats 16000000 in
run_cmd liftTermElabM do
  let same (thm exp : Name) : MetaM Unit := do
    let ci ← getConstInfo thm
    unless ci.levelParams.isEmpty do throwError "{thm}: level parameters"
    let a ← norm ci.type
    let e ← norm (mkConst exp)
    unless ← withDefault (isDefEq a e) do throwError "{thm}: type is NOT the expected statement {exp}"
    let ba ← binderInfos a
    let be ← binderInfos e
    unless ba == be do throwError "{thm}: binder kinds differ from {exp}: {repr ba} vs {repr be}"
  let differs (thm mu0 : Name) : MetaM Unit := do
    let ci ← getConstInfo thm
    let a ← norm ci.type
    let e ← norm (mkConst mu0)
    if ← withDefault (isDefEq a e) then throwError "{thm}: the MUTANT {mu0} was accepted"
  let S := `Tools.ShippingFGCircuitS1lReader
  let mut nm : Nat := 0
  same (S ++ `checkedEnv_of_decl) ``OfDeclTrue
  for mu in [``MutOfDeclNoGates, ``MutOfDeclNoReader] do differs (S ++ `checkedEnv_of_decl) mu; nm := nm + 1
  same (S ++ `CounterLoopExtern.mk) ``ExternMkTrue
  for mu in [``MutExternValue, ``MutExternArity] do differs (S ++ `CounterLoopExtern.mk) mu; nm := nm + 1
  same (S ++ `CounterLoopEnvFacts.mk) ``EnvFactsMkTrue
  for mu in [``MutEnvValue, ``MutEnvTy, ``MutEnvData, ``MutEnvPolarity, ``MutEnvName] do differs (S ++ `CounterLoopEnvFacts.mk) mu; nm := nm + 1
  same (S ++ `counterLoop_dataOfAt) ``DataOfAtTrue
  for mu in [``MutDataOfAtData, ``MutDataOfAtFuel, ``MutDataOfAtNoX] do differs (S ++ `counterLoop_dataOfAt) mu; nm := nm + 1
  same (S ++ `counterLoop_gates) ``GatesLoopTrue
  for mu in [``MutGatesPol, ``MutGatesNoIp] do differs (S ++ `counterLoop_gates) mu; nm := nm + 1
  same (S ++ `counterLoop_checkedEnv_of_finite) ``CheckedFinTrue
  for mu in [``MutCFData, ``MutCFVal, ``MutCFFuel, ``MutCFNoX, ``MutCFNoF] do differs (S ++ `counterLoop_checkedEnv_of_finite) mu; nm := nm + 1
  same (S ++ `counterLoop_final11) ``F11True
  for mu in [``M11HeadEnd, ``M11LinkEnd, ``M11ConclEnd, ``M11Data, ``M11Post, ``M11NoLvl, ``M11NoX, ``M11NoF] do differs (S ++ `counterLoop_final11) mu; nm := nm + 1
  logInfo m!"FGCIRCUIT10 SIGNATURES: checkedEnv_of_decl, CounterLoopExtern.mk, CounterLoopEnvFacts.mk, counterLoop_dataOfAt, counterLoop_gates, counterLoop_checkedEnv_of_finite, counterLoop_final11: complete types match the independently written statements; {nm} mutants rejected (each counted per check: dropped gate / reader / lvl / extern / env-facts premise, another value / type / data (EnvFacts.mk, dataOfAt, the fuel body of final11) / post root, the instance predicate with the wrong polarity, `proj` asked at another name, the arity of the runCircuitH test, the fuel, END-WORLD controls = the same run's end world w' (head start, link, conclusion environment))"

/-! ## 2. the hypotheses that remain -/

run_cmd liftTermElabM do
  let S := `Tools.ShippingFGCircuitS1lReader
  let bs ← explicitBinders (S ++ `counterLoop_final11)
  let names := (bs.map (·.1)).filter fun n => !n.startsWith "a._@"
  let expected := ["L", "lvl", "env₀", "hstart", "hr", "hhead", "hcell", "hlvl", "hx", "hf", "hlink"]
  unless names == expected do throwError "counterLoop_final11: hypotheses are {names}, expected {expected}"
  for gone in ["hchk", "hquiet", "hg", "hw", "hA6", "hsrc", "hdRun", "hgates", "hRead", "hE", "hreader", "hquote", "hgatesB"] do
    if names.contains gone then throwError "counterLoop_final11: {gone} is a hypothesis"
  for (n, t) in bs do
    let pp ← try pure (toString (← ppExpr t)) catch _ => pure s!"<unprintable; constants: {t.getUsedConstants.toList.map (·.toString)}>"
    logInfo m!"FGCIRCUIT10 REMAINING counterLoop_final11 {n} : {pp}"
  logInfo "FGCIRCUIT10 HYPS: final11 = L lvl env₀ hstart hr hhead(HeadAt) hcell(ReadWorld cref) hlvl(lvl at the shape's body = 1000000) hx(CounterLoopExtern: packTupleInputs / rootFloat / Expr.find? on counterLoopValue) hf(CounterLoopEnvFacts env₀: root + machineShape?, userInliner at value and type, instancePredicate at value, proj at Signal.loop) hlink(ReadsAt env₀ cref w). NOT hypotheses: hchk(CheckedStart), the gates / the reader as evaluation statements, hquiet, GetEnvFrame, hdRun, MachineDefinesLinked, hsrc, DesignTransport, hw"

/-! ## 3. axioms -/
run_cmd liftTermElabM do
  let S := `Tools.ShippingFGCircuitS1lReader
  let names : List Name := [S ++ `entryGatesB_of_gatesOnDecl, S ++ `readerAt_of_readerOnDecl, S ++ `checkedEnv_of_decl, S ++ `entryOfDecl_eq,
    S ++ `machRoot_counterLoop, S ++ `srcDomOf_counterLoop, S ++ `dataOfCore_counterLoop, S ++ `counterLoop_dataOfAt, S ++ `counterLoop_gates,
    S ++ `counterLoop_gatesOnDecl, S ++ `counterLoop_readerOnDecl, S ++ `counterLoop_checkedEnv_of_finite, S ++ `counterLoop_final11]
  for nm in names do
    for ax in ← Lean.collectAxioms nm do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do throwError "{nm} uses {ax}"
  logInfo m!"FGCIRCUIT10 AXIOMS: {names.length} names, standard axioms only (no sorryAx, no native_decide)"

/-! ## 4. SNAPSHOT10: the named facts evaluated on ONE environment; the finite-input claim probed -/

run_cmd liftTermElabM do
  let env ← getEnv
  let X := ``counterLoop
  -- CounterLoopExtern (closed, env independent)
  unless Sparkle.Compiler.MachTupleIn.packTupleInputs counterLoopValue == counterLoopValue do throwError "pack fact false"
  unless Sparkle.Compiler.MachRawSurface.rootFloat counterLoopValue == counterLoopValue do throwError "rootFloat fact false"
  unless (counterLoopValue.find? (fun t => t.isAppOfArity ``Sparkle.Core.runCircuitH 8)).isNone do throwError "find? fact false"
  -- CounterLoopEnvFacts env
  let some (.defnInfo d) := env.find? X | throwError "no root"
  unless d.levelParams.isEmpty && d.type == counterLoopType && d.value == counterLoopValue do throwError "root fact false"
  let se := structEnv env
  let some s := machineShape? false [] (.defnInfo d) se | throwError "machineShape? none"
  unless (← shapeExprOf s) == (← shapeExprOf counterLoop.machineData.shape) do throwError "machineShape? ≠ the data's shape"
  unless userInliner env counterLoopValue == counterLoopValue do throwError "ui_val false"
  unless userInliner env counterLoopType == counterLoopType do throwError "ui_ty false"
  unless instancePredicate env counterLoopValue == false do throwError "ip_val false"
  unless (se.proj ``Sparkle.Core.Signal.Signal.loop).isNone do throwError "proj fact false"
  -- the entry constant is the declaration itself (entryOfDecl_eq, evaluated)
  let some E := Tools.ShippingGen5Acc.entry₀ env X | throwError "no entry"
  unless (match E with | .defnInfo d' => d'.value == counterLoopValue && d'.type == counterLoopType | _ => false) do throwError "entry₀ is not the declaration"
  -- the finite-input claim: gates and data with ALTERED arguments (the instance predicate true off the value; proj answers off Signal.loop)
  let ipAlt : Lean.Expr → Bool := fun e => if e == counterLoopValue then instancePredicate env e else true
  let seAlt : StructEnv := { se with proj := fun n => if n == ``Sparkle.Core.Signal.Signal.loop then se.proj n else some (`x, 1, 0), fields := fun n => some (n, []) }
  unless (certifiedShape? false [] E).isNone && (mixedCertifiedShape? false [] E ipAlt).isNone do throwError "gates depend on the instance predicate off the value"
  let some dd := Tools.ShippingGen5DataOf.dataOfAt (fun _ => 1000000) E seAlt counterLoop.machineData.shape | throwError "dataOfAt none under altered proj/fields"
  unless (← dataExprOf dd) == (← literalExpr ``counterLoop.machineData) do throwError "dataOfAt (altered proj/fields) differs from machineData"
  -- negative controls: the probes are not vacuous
  -- (1) the instance predicate is not constantly false: some sub-term of a hierarchical root's body satisfies it
  let hftBody := (env.find? ``Tests.Gen5.FGCircuitPilotCheck8.hftOutProbe).bind (·.value?)
  let ctrl1 : Bool := match hftBody with | some v => (v.find? fun e => instancePredicate env e).isSome | none => false
  -- (2) the data reader is sensitive to the value: another root's value changes the result
  let E2 := ConstantInfo.defnInfo { d with value := shift4LoopValue, type := shift4LoopType }
  let other := Tools.ShippingGen5DataOf.dataOfAt (fun _ => 1000000) E2 se counterLoop.machineData.shape
  let lit ← literalExpr ``counterLoop.machineData
  let ctrl2 : Bool ← match other with | some dd2 => do pure ((← dataExprOf dd2) != lit) | none => pure true
  unless ctrl2 do throwError "negative control: another value gave the same data"
  logInfo m!"FGCIRCUIT10 SNAPSHOT10: on this build's ONE environment (an EVALUATION, not a supply of the hypotheses): CounterLoopExtern (pack / rootFloat / Expr.find?) and CounterLoopEnvFacts (root, machineShape? = the data's shape, userInliner at value and type, instancePredicate at value = false, proj at Signal.loop = none) hold; entry₀ is the declaration; the gates (mixedCertifiedShape? with the instance predicate true everywhere except the value) and dataOfAt (proj / fields answering something else off Signal.loop) are unchanged — the only places the evaluation looked. Controls: another root's value gives other data; the instance predicate is true on some sub-term of the hierarchical probe's body: {ctrl1} (informative: false only if the probe's body has no instance sub-term)"

end Tests.Gen5.FGCircuitPilotCheck10
