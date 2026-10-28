import Tests.Compiler.ReaderFuelShadowTest
import Tools.Prototype.ReaderFixpointExec

/-! # LC9: executable `partial_fixpoint` block (`machineShapeX`) against the production `machineShape?`

TARGET-ONLY (`lake build Tests.Compiler.ReaderLfpExecTest`); not in `Tests.AllTests`.  EVIDENCE for A1's
acceptance condition on the 40 fixed shadow cases (declarations imported from
`Tests.Compiler.ReaderFuelShadowTest`), NOT a proof.  Per case one line

    LFPEXEC <label> [<group>]: real=<OK|FAIL> exec=<OK|FAIL|BOT> class=<none|some none|some (some x)> fields=… equal=…

`exec` = `machineShapeX` (outer `none` can only be reported if the code returns it, which `partial_fixpoint`
code never does; a hang shows as TIMEOUT).  
LC10: the file THROWS unless, over the expected `expectedCases` = 40 cases, there are 0 timeouts and 0
disagreements.  The compared projection (`compareRes`): exec `some none` ↔ production `none`; exec
`some (some x)` ↔ production `some x` (all `MachineShape` fields equal); anything else (incl. exec outer
`none`, i.e. BOT) is a disagreement.  A TIMEOUT is "no result within the budget", NOT evidence of
non-termination.  BUILT: lc10 (see REPORT-LC10). -/
namespace Tests.Compiler.ReaderLfpExecTest
open Lean Elab Command Meta
open Sparkle.Compiler.Elab
open Tools.Prototype.ReaderExec
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
  let x := machineShapeX sm ps entry senv
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
    throwError m!"LFPEXEC {label} [{group}]: ERROR {toString e}"
  | .ok none =>
    IO.cancel tw
    let line := s!"LFPEXEC {label} [{group}]: TIMEOUT after {caseBudgetMs} ms"
    (← IO.getStderr).putStrLn line
    logWarning m!"{line}"
    return 1
  | .ok (some o) =>
    IO.cancel ts
    let (fields, eq) := compareRes o.real o.x
    let shape : String := match o.x with
      | none => "none" | some none => "some none" | some (some _) => "some (some x)"
    let line := s!"LFPEXEC {label} [{group}]: real={realClass o.real} exec={xClass o.x} class={shape} fields={fields} equal={eq} realMs={o.realMs} execMs={o.xMs}"
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
  let line := s!"LFPEXEC SUMMARY: cases={n} expected={expectedCases} timeouts={timeouts} disagreements={disagreements}"
  (← IO.getStderr).putStrLn line
  logInfo m!"{line}"
  unless n == expectedCases && timeouts == 0 && disagreements == 0 do
    throwError m!"{line}: corpus check FAILED (need cases=40, timeouts=0, disagreements=0)"

end Tests.Compiler.ReaderLfpExecTest
