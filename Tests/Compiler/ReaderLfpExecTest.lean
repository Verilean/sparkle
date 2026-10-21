import Tests.Compiler.ReaderFuelShadowTest
import Tools.Prototype.ReaderFixpointExec

/-! # LC9: executable `partial_fixpoint` block (`machineShapeX`) against the production `machineShape?`

TARGET-ONLY (`lake build Tests.Compiler.ReaderLfpExecTest`); not in `Tests.AllTests`.  EVIDENCE for A1's
acceptance condition on the 40 fixed shadow cases (declarations imported from
`Tests.Compiler.ReaderFuelShadowTest`), NOT a proof.  Per case one line

    LFPEXEC <label> [<group>]: real=<OK|FAIL> exec=<OK|FAIL|BOT> class=<none|some none|some (some x)> fields=… equal=…

`exec` = `machineShapeX` (outer `none` can only be reported if the code returns it, which `partial_fixpoint`
code never does; a hang shows as TIMEOUT).  A case errors iff `equal=false`. -/
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
    (ps : List (String × Nat) := []) : TermElabM Unit := do
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
  | .ok (some o) =>
    IO.cancel ts
    let (fields, eq) := compareRes o.real o.x
    let shape : String := match o.x with
      | none => "none" | some none => "some none" | some (some _) => "some (some x)"
    let line := s!"LFPEXEC {label} [{group}]: real={realClass o.real} exec={xClass o.x} class={shape} fields={fields} equal={eq} realMs={o.realMs} execMs={o.xMs}"
    (← IO.getStderr).putStrLn line
    logInfo m!"{line}"
    unless eq do
      throwError m!"LFPEXEC {label}: the executable block differs from the production reader"

run_cmd liftTermElabM <| xCase "counterLoop" "loop" ``Tests.Compiler.ReaderFuelGridTest.counterLoop
run_cmd liftTermElabM <| xCase "accLoop" "loop" ``Tests.Compiler.ReaderFuelGridTest.accLoop
run_cmd liftTermElabM <| xCase "wholeLoop" "loop" ``wholeLoop
run_cmd liftTermElabM <| xCase "loopPair" "loop" ``loopPair
run_cmd liftTermElabM <| xCase "toggle107" "loop" ``Sparkle.Tests.Compiler.Issue107LetBoundInstanceDup.toggle
run_cmd liftTermElabM <| xCase "latch2" "nested" ``latch2
run_cmd liftTermElabM <| xCase "pair" "nested" ``pair
run_cmd liftTermElabM <| xCase "consumer" "nested" ``consumer
run_cmd liftTermElabM <| xCase "chain3" "nested-shared" ``chain3
run_cmd liftTermElabM <| xCase "siblings" "nested-shared" ``siblings
run_cmd liftTermElabM <| xCase "caller" "calls" ``Tests.Compiler.ReaderFuelGridTest.caller
run_cmd liftTermElabM <| xCase "callerNested" "calls" ``Tests.Compiler.ReaderFuelGridTest.callerNested
run_cmd liftTermElabM <| xCase "callerInner" "calls" ``Tests.Compiler.ReaderFuelGridTest.callerInner
run_cmd liftTermElabM <| xCase "callerD" "calls" ``callerD
run_cmd liftTermElabM <| xCase "callerLN" "calls" ``callerLN
run_cmd liftTermElabM <| xCase "threeInstances" "calls" ``Sparkle.Tests.Compiler.Issue107LetBoundInstanceDup.threeInstances
run_cmd liftTermElabM <| xCase "parent" "instS" ``parent
run_cmd liftTermElabM <| xCase "chained" "instS" ``chained
run_cmd liftTermElabM <| xCase "grand" "instS-callers" ``grand
run_cmd liftTermElabM <| xCase "grandH" "instS-callers" ``grandH
run_cmd liftTermElabM <| xCase "topD2" "instS-callers" ``topD2
run_cmd liftTermElabM <| xCase "mixD1" "instS-callers" ``mixD1
run_cmd liftTermElabM <| xCase "mixDeep" "instS-callers" ``mixDeep
run_cmd liftTermElabM <| xCase "twinCalls" "instS" ``Sparkle.Tests.Compiler.MultiInstance.twinCalls
run_cmd liftTermElabM <| xCase "mesh2x2" "instS" ``Sparkle.Tests.Compiler.MultiInstance.mesh2x2
run_cmd liftTermElabM <| xCase "cnt" "multi-output" ``cnt
run_cmd liftTermElabM <| xCase "mid2" "multi-output" ``mid2
run_cmd liftTermElabM <| xCase "pe" "multi-output" ``Sparkle.Tests.Compiler.MultiInstance.pe
run_cmd liftTermElabM <| xCase "source" "multi-output" ``source
run_cmd liftTermElabM <| xCase "memCounter" "memory" ``Tests.Compiler.ReaderFuelGridTest.memCounter
run_cmd liftTermElabM <| xCase "twoMems" "memory" ``Tests.Compiler.ReaderFuelGridTest.twoMems
run_cmd liftTermElabM <| xCase "mixedMems" "memory" ``mixedMems
run_cmd liftTermElabM <| xCase "withMemory" "memory" ``withMemory
run_cmd liftTermElabM <| xCase "twoLoops" "refusal" ``Tests.Compiler.ReaderFuelGridTest.twoLoops
run_cmd liftTermElabM <| xCase "opaqueInit" "refusal" ``Tests.Compiler.ReaderFuelGridTest.opaqueInit
run_cmd liftTermElabM <| xCase "loopCall" "refusal" ``loopCall
run_cmd liftTermElabM <| xCase "notHw" "refusal" ``Tests.Compiler.ReaderFuelGridTest.notHw
run_cmd liftTermElabM <| xCase "natSig" "refusal" ``natSig
run_cmd liftTermElabM <| xCase "gridInit" "refusal" ``Tests.Compiler.ReaderFuelGridTest.gridInit
run_cmd liftTermElabM <| xCase "latchSymbolic" "refusal" ``Tests.Compiler.ReaderFuelGridTest.latch true

end Tests.Compiler.ReaderLfpExecTest
