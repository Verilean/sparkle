import Tests.Compiler.ReaderFuelShadowTest
import Tools.Prototype.NormStepModel

/-! # NMC (a): the WHOLE model wrapper `machineShapeNM` against the production `machineShape?`

TARGET-ONLY (`./.cluster/qbuild.sh build Tests.Compiler.NormStepModelWholeAgreeTest`); not in `Tests.AllTests`. EVIDENCE only, NOT a
proof and NOT an equivalence claim: a finite comparison on the 40 fixed cases of `Tests.Compiler.ReaderFuelShadowTest` (the cases of
`ReaderLfpExecTest`). Per case one line `NMWHOLE <label> [<group>]: real=… model=… …` with the layout (all `MachineShape` fields),
refusal (`some none` vs production `none`) and fallback outcomes compared by `compareRes`. Mismatches are REPORTED, not thrown; the file
throws only if the case count is not 40. `machineShapeNM` answering outer `none` (BOT: no finite derivation) is a mismatch. BUILT: see
REPORT-NMC. -/
namespace Tests.Compiler.NormStepModelWholeAgreeTest
open Lean Elab Command Meta
open Sparkle.Compiler.Elab
open Tools.Prototype.ReaderExec
open Tools.Prototype.NormStepModel
open Tests.Compiler.ReaderFuelShadowTest

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
  let x := machineShapeNM sm ps entry senv
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
    throwError m!"NMWHOLE {label} [{group}]: ERROR {toString e}"
  | .ok none =>
    IO.cancel tw
    let line := s!"NMWHOLE {label} [{group}]: TIMEOUT after {caseBudgetMs} ms"
    (← IO.getStderr).putStrLn line
    logWarning m!"{line}"
    return 1
  | .ok (some o) =>
    IO.cancel ts
    let (fields, eq) := compareRes o.real o.x
    let shape : String := match o.x with
      | none => "none" | some none => "some none" | some (some _) => "some (some x)"
    let line := s!"NMWHOLE {label} [{group}]: real={realClass o.real} model={xClass o.x} class={shape} fields={fields} equal={eq} realMs={o.realMs} modelMs={o.xMs}"
    (← IO.getStderr).putStrLn line
    logInfo m!"{line}"
    if eq then return 0 else return 2

/-- Expected number of cases (the fixed shadow list). -/
def expectedCases : Nat := 40

run_cmd liftTermElabM do
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
  for c in cases do
    n := n + 1
    match ← c () with
    | 1 => timeouts := timeouts + 1
    | 2 => disagreements := disagreements + 1
    | _ => pure ()
  let line := s!"NMWHOLE SUMMARY: cases={n} expected={expectedCases} timeouts={timeouts} disagreements={disagreements}"
  (← IO.getStderr).putStrLn line
  logInfo m!"{line}"
  unless n == expectedCases do throwError m!"{line}: wrong case count"

end Tests.Compiler.NormStepModelWholeAgreeTest
