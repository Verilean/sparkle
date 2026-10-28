import Tests.Compiler.ReaderFuelShadowTest
import Tools.Prototype.ExtReaderGlue

/-! # EXT2: the WHOLE model reader `machineShapeXM` (every call site of the extern / partial operations turned into the models) against the
production `machineShape?`

TARGET-ONLY (`./.cluster/qbuild.sh build Tests.Compiler.ExtReaderWholeAgreeTest`); not in `Tests.AllTests`. EVIDENCE only, NOT a proof and NOT
an equivalence claim: a finite comparison on the 40 fixed cases of `Tests.Compiler.ReaderFuelShadowTest` (the cases of `ReaderLfpExecTest`).
Per case one line `XMWHOLE <label> [<group>]: real=… model=… …` with the layout (all `MachineShape` fields), reader refusal agreement
(`some none` vs production `none`; the real legacy fallback is NOT executed or verified) and the layout compared by the local `fieldChecks`
(EVERY field of `MachineShape` and `Layout`, including `instOrigins`; coverage asserted against the structure info). The file THROWS unless:
40 cases, 0 timeouts, 0 disagreements, 0 outer-none, 33 successes (all MachineShape fields equal), 7 refusals (production none ↔ model some
none). `machineShapeXM` answering outer `none` (BOT: no finite derivation) is a mismatch. The model reader here calls `liftM`, `lowerM`,
`inst1M`, `betaM`, `eqvX`, `rootFloatS`, `zeroLitM`, `zetaAllM`; it still calls the shipped `Expr.eqv` inside the let-table helpers
(`machBindLet…`, `machLetIndex`), the shipped `shapeStart`'s `machReserve`, `hasLooseBVars`, `getAppFn/getAppArgs`. -/
namespace Tests.Compiler.ExtReaderWholeAgreeTest
open Lean Elab Command Meta
open Sparkle.Compiler.Elab
open Tools.Prototype.ReaderExec
open Tools.Prototype.ExtReader
open Tests.Compiler.ReaderFuelShadowTest

/-- EVERY field of `MachineShape` (with `layout` expanded to the fields of `Layout`), as `(name, equal)`. -/
def fieldChecks (a b : MachineShape) : List (String × Bool) :=
  [("binders", a.binders == b.binders), ("body", a.body == b.body),
   ("layout.slots", a.layout.slots == b.layout.slots), ("layout.outs", a.layout.outs == b.layout.outs),
   ("layout.resetKind", a.layout.resetKind == b.layout.resetKind), ("layout.lets", a.layout.lets == b.layout.lets),
   ("runs", a.runs == b.runs), ("insts", a.insts == b.insts), ("loops", a.loops == b.loops),
   ("instFields", a.instFields == b.instFields), ("instOrigins", a.instOrigins == b.instOrigins)]

/-- Local replacement of `compareRes`: same shapes of answer, all fields compared. -/
def compareAll : Option MachineShape → Option (Option MachineShape) → String × Bool
  | none, some none => ("n/a", true)
  | some a, some (some b) =>
    match (fieldChecks a b).filter (!·.2) |>.map (·.1) with
    | [] => ("all-equal", true)
    | ds => ("differ:" ++ ",".intercalate ds, false)
  | _, _ => ("n/a", false)

structure XObs where
  real : Option MachineShape
  x : Option (Option MachineShape)
  realMs : Nat
  xMs : Nat

def xwork (sm : Bool) (ps : List (String × Nat)) (entry : ConstantInfo) (senv : StructEnv) :
    IO (Option XObs) := do
  let t0 ← IO.monoMsNow
  let real := machineShape? sm ps entry senv
  let t1 ← if shapeKey real == 0 then pure 0 else IO.monoMsNow
  let x := machineShapeXM sm ps entry senv
  let xk : UInt64 := match x with
    | none => 3
    | some r => shapeKey r
  let t2 ← if xk == 0 then pure 0 else IO.monoMsNow
  return some { real := real, x := x, realMs := t1 - t0, xMs := t2 - t1 }

def xsleeper (ms : Nat) : IO (Option XObs) := do
  for _ in [0:ms / 50] do
    if ← IO.checkCanceled then return none
    IO.sleep 50
  return none

def xClass : Option (Option MachineShape) → String
  | none => "BOT"
  | some none => "FAIL"
  | some (some _) => "OK"

def xCase (label group : String) (n : Name) (sm : Bool := false)
    (ps : List (String × Nat) := []) : TermElabM Nat := do
  let env ← getEnv
  let senv := structEnv env
  let ci ← getConstInfo n
  let entry := entryConst true sm ps ci (instancePredicate env) (userInliner env) senv
  let tw ← IO.asTask (xwork sm ps entry senv) .dedicated
  let ts ← IO.asTask (xsleeper caseBudgetMs) .dedicated
  let r ← IO.waitAny [tw, ts]
  match r with
  | .error e =>
    IO.cancel ts
    throwError m!"XMWHOLE {label} [{group}]: ERROR {toString e}"
  | .ok none =>
    IO.cancel tw
    let line := s!"XMWHOLE {label} [{group}]: TIMEOUT after {caseBudgetMs} ms"
    (← IO.getStderr).putStrLn line
    logWarning m!"{line}"
    return 1
  | .ok (some o) =>
    IO.cancel ts
    let (fields, eq) := compareAll o.real o.x
    let shape : String := match o.x with
      | none => "none" | some none => "some none" | some (some _) => "some (some x)"
    let line := s!"XMWHOLE {label} [{group}]: real={realClass o.real} model={xClass o.x} class={shape} fields={fields} equal={eq} realMs={o.realMs} modelMs={o.xMs}"
    (← IO.getStderr).putStrLn line
    logInfo m!"{line}"
    -- 1 timeout (above); 2 disagreement; 3 outer none; 4 agreeing refusal; 0 agreeing success
    match o.x with
    | none => return 3
    | some xr =>
      if !eq then return 2
      else if o.real.isNone && xr.isNone then return 4
      else if o.real.isSome && xr.isSome then return 0
      else return 2

/-- THROWS unless the names compared by `fieldChecks` are exactly the fields of `MachineShape` (`layout` expanded to `Layout`'s). -/
def checkFieldCoverage : CoreM Unit := do
  let env ← getEnv
  let top := getStructureFieldsFlattened env ``MachineShape false
  let lay := getStructureFieldsFlattened env ``Sparkle.IR.Machine.Layout false
  let expected := top.toList.flatMap fun f =>
    if f == `layout then lay.toList.map (s!"layout.{·}") else [toString f]
  let dummy : MachineShape := { binders := [], body := .bvar 0, layout := { slots := [], outs := [], resetKind := default } }
  let got := (fieldChecks dummy dummy).map (·.1)
  let sort := fun (l : List String) => l.toArray.qsort (· < ·) |>.toList
  unless sort expected == sort got do
    throwError m!"field coverage mismatch: structure {expected} vs compared {got}"
  IO.println s!"XMWHOLE field coverage: {got.length} fields compared = structure fields"

/-- Expected number of cases (the fixed shadow list). -/
def expectedCases : Nat := 40

run_cmd liftTermElabM do
  checkFieldCoverage
  let cases : List (Unit → TermElabM Nat) := [
    (fun _ => xCase "counterLoop" "loop" ``Tests.Compiler.ReaderFuelGridTest.counterLoop),
    (fun _ => xCase "accLoop" "loop" ``Tests.Compiler.ReaderFuelGridTest.accLoop),
    (fun _ => xCase "wholeLoop" "loop" ``wholeLoop),
    (fun _ => xCase "loopPair" "loop" ``loopPair),
    (fun _ => xCase "toggle107" "loop" ``Sparkle.Tests.Compiler.Issue107LetBoundInstanceDup.toggle),
    (fun _ => xCase "latch2" "nested" ``latch2),
    (fun _ => xCase "pair" "nested" ``pair),
    (fun _ => xCase "consumer" "nested" ``consumer),
    (fun _ => xCase "chain3" "nested-shared" ``chain3),
    (fun _ => xCase "siblings" "nested-shared" ``siblings),
    (fun _ => xCase "caller" "calls" ``Tests.Compiler.ReaderFuelGridTest.caller),
    (fun _ => xCase "callerNested" "calls" ``Tests.Compiler.ReaderFuelGridTest.callerNested),
    (fun _ => xCase "callerInner" "calls" ``Tests.Compiler.ReaderFuelGridTest.callerInner),
    (fun _ => xCase "callerD" "calls" ``callerD),
    (fun _ => xCase "callerLN" "calls" ``callerLN),
    (fun _ => xCase "threeInstances" "calls" ``Sparkle.Tests.Compiler.Issue107LetBoundInstanceDup.threeInstances),
    (fun _ => xCase "parent" "instS" ``parent),
    (fun _ => xCase "chained" "instS" ``chained),
    (fun _ => xCase "grand" "instS-callers" ``grand),
    (fun _ => xCase "grandH" "instS-callers" ``grandH),
    (fun _ => xCase "topD2" "instS-callers" ``topD2),
    (fun _ => xCase "mixD1" "instS-callers" ``mixD1),
    (fun _ => xCase "mixDeep" "instS-callers" ``mixDeep),
    (fun _ => xCase "twinCalls" "instS" ``Sparkle.Tests.Compiler.MultiInstance.twinCalls),
    (fun _ => xCase "mesh2x2" "instS" ``Sparkle.Tests.Compiler.MultiInstance.mesh2x2),
    (fun _ => xCase "cnt" "multi-output" ``cnt),
    (fun _ => xCase "mid2" "multi-output" ``mid2),
    (fun _ => xCase "pe" "multi-output" ``Sparkle.Tests.Compiler.MultiInstance.pe),
    (fun _ => xCase "source" "multi-output" ``source),
    (fun _ => xCase "memCounter" "memory" ``Tests.Compiler.ReaderFuelGridTest.memCounter),
    (fun _ => xCase "twoMems" "memory" ``Tests.Compiler.ReaderFuelGridTest.twoMems),
    (fun _ => xCase "mixedMems" "memory" ``mixedMems),
    (fun _ => xCase "withMemory" "memory" ``withMemory),
    (fun _ => xCase "twoLoops" "refusal" ``Tests.Compiler.ReaderFuelGridTest.twoLoops),
    (fun _ => xCase "opaqueInit" "refusal" ``Tests.Compiler.ReaderFuelGridTest.opaqueInit),
    (fun _ => xCase "loopCall" "refusal" ``loopCall),
    (fun _ => xCase "notHw" "refusal" ``Tests.Compiler.ReaderFuelGridTest.notHw),
    (fun _ => xCase "natSig" "refusal" ``natSig),
    (fun _ => xCase "gridInit" "refusal" ``Tests.Compiler.ReaderFuelGridTest.gridInit),
    (fun _ => xCase "latchSymbolic" "refusal" ``Tests.Compiler.ReaderFuelGridTest.latch true)]
  let mut n := 0
  let mut timeouts := 0
  let mut disagreements := 0
  let mut outerNone := 0
  let mut successes := 0
  let mut refusals := 0
  for c in cases do
    n := n + 1
    match ← c () with
    | 1 => timeouts := timeouts + 1
    | 2 => disagreements := disagreements + 1
    | 3 => outerNone := outerNone + 1
    | 4 => refusals := refusals + 1
    | _ => successes := successes + 1
  let line := s!"XMWHOLE SUMMARY: cases={n} expected={expectedCases} timeouts={timeouts} disagreements={disagreements} outerNone={outerNone} successes={successes} refusals={refusals} (reader refusal agreement; real fallback NOT verified)"
  (← IO.getStderr).putStrLn line
  logInfo m!"{line}"
  unless n == expectedCases do throwError m!"{line}: wrong case count"
  unless timeouts == 0 do throwError m!"{line}: timeouts"
  unless disagreements == 0 do throwError m!"{line}: disagreements"
  unless outerNone == 0 do throwError m!"{line}: outer none"
  unless successes == 33 do throwError m!"{line}: expected 33 successes"
  unless refusals == 7 do throwError m!"{line}: expected 7 refusals"

end Tests.Compiler.ExtReaderWholeAgreeTest
