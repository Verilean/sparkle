import Tests.Compiler.ReaderFuelShadowTest
import Tools.Prototype.ReaderFixpointNorm

/-! # LC11b: `machNorm` (real, `partial def`) against `execNorm` (`partial_fixpoint` of `normStep`)

TARGET-ONLY (`./.cluster/qbuild.sh build Tests.Compiler.NormXExecTest`); not in `Tests.AllTests`.  EVIDENCE, not proof.
Per one of the 40 shadow cases (`expectedCases`): the expression the wrapper normalises (`shapePre … |>.e`, the
first `machNorm` query of `machineShape?`) is run through `machNorm senv e` and `execNorm senv e`; agreement means
`execNorm senv e = some (machNorm senv e)` (`Expr` `==`).  A case with no `shapePre` (refusal before the
`machNorm` call) is counted as `nopre` (nothing compared).  TIMEOUT = no result within `caseBudgetMs`, NOT evidence
of non-termination.  THROWS unless cases = 40, 0 timeouts, 0 disagreements. -/
namespace Tests.Compiler.NormXExecTest
open Lean Elab Command Meta
open Sparkle.Compiler.Elab
open Tools.Prototype.ReaderExec Tools.ShippingReaderFuel
open Tests.Compiler.ReaderFuelShadowTest

/-- 0 = agree, 1 = disagree, 2 = nothing compared (no `shapePre`). -/
def nwork (sm : Bool) (ps : List (String × Nat)) (entry : ConstantInfo) (senv : StructEnv) :
    IO (Option Nat) := do
  match shapePre sm ps entry senv with
  | none => return some 2
  | some p =>
    let a := machNorm senv p.e
    let b := execNorm senv p.e
    return some (if b == some a then 0 else 1)

def nsleeper (ms : Nat) : IO (Option Nat) := do
  for _ in [0:ms / 50] do
    if ← IO.checkCanceled then return none
    IO.sleep 50
  return none

/-- returns 0 agree, 1 timeout, 2 disagree, 3 nothing compared. -/
def nCase (label group : String) (n : Name) (sm : Bool := false)
    (ps : List (String × Nat) := []) : TermElabM Nat := do
  let env ← getEnv
  let senv := structEnv env
  let ci ← getConstInfo n
  let entry := entryConst true sm ps ci (instancePredicate env) (userInliner env) senv
  let tw ← IO.asTask (nwork sm ps entry senv) .dedicated
  let ts ← IO.asTask (nsleeper caseBudgetMs) .dedicated
  match ← IO.waitAny [tw, ts] with
  | .error e =>
    IO.cancel ts
    throwError m!"NORMX {label} [{group}]: ERROR {toString e}"
  | .ok none =>
    IO.cancel tw
    let line := s!"NORMX {label} [{group}]: TIMEOUT after {caseBudgetMs} ms"
    (← IO.getStderr).putStrLn line
    logWarning m!"{line}"
    return 1
  | .ok (some k) =>
    IO.cancel ts
    let line := s!"NORMX {label} [{group}]: {if k == 0 then "agree" else if k == 1 then "DISAGREE" else "nopre"}"
    (← IO.getStderr).putStrLn line
    logInfo m!"{line}"
    return (if k == 0 then 0 else if k == 1 then 2 else 3)

def expectedCases : Nat := 40

run_cmd liftTermElabM do
  let cases : List (Unit → TermElabM Nat) := [
    (fun _ => nCase "counterLoop" "loop" ``Tests.Compiler.ReaderFuelGridTest.counterLoop),
    (fun _ => nCase "accLoop" "loop" ``Tests.Compiler.ReaderFuelGridTest.accLoop),
    (fun _ => nCase "wholeLoop" "loop" ``wholeLoop),
    (fun _ => nCase "loopPair" "loop" ``loopPair),
    (fun _ => nCase "toggle107" "loop" ``Sparkle.Tests.Compiler.Issue107LetBoundInstanceDup.toggle),
    (fun _ => nCase "latch2" "nested" ``latch2),
    (fun _ => nCase "pair" "nested" ``pair),
    (fun _ => nCase "consumer" "nested" ``consumer),
    (fun _ => nCase "chain3" "nested-shared" ``chain3),
    (fun _ => nCase "siblings" "nested-shared" ``siblings),
    (fun _ => nCase "caller" "calls" ``Tests.Compiler.ReaderFuelGridTest.caller),
    (fun _ => nCase "callerNested" "calls" ``Tests.Compiler.ReaderFuelGridTest.callerNested),
    (fun _ => nCase "callerInner" "calls" ``Tests.Compiler.ReaderFuelGridTest.callerInner),
    (fun _ => nCase "callerD" "calls" ``callerD),
    (fun _ => nCase "callerLN" "calls" ``callerLN),
    (fun _ => nCase "threeInstances" "calls" ``Sparkle.Tests.Compiler.Issue107LetBoundInstanceDup.threeInstances),
    (fun _ => nCase "parent" "instS" ``parent),
    (fun _ => nCase "chained" "instS" ``chained),
    (fun _ => nCase "grand" "instS-callers" ``grand),
    (fun _ => nCase "grandH" "instS-callers" ``grandH),
    (fun _ => nCase "topD2" "instS-callers" ``topD2),
    (fun _ => nCase "mixD1" "instS-callers" ``mixD1),
    (fun _ => nCase "mixDeep" "instS-callers" ``mixDeep),
    (fun _ => nCase "twinCalls" "instS" ``Sparkle.Tests.Compiler.MultiInstance.twinCalls),
    (fun _ => nCase "mesh2x2" "instS" ``Sparkle.Tests.Compiler.MultiInstance.mesh2x2),
    (fun _ => nCase "cnt" "multi-output" ``cnt),
    (fun _ => nCase "mid2" "multi-output" ``mid2),
    (fun _ => nCase "pe" "multi-output" ``Sparkle.Tests.Compiler.MultiInstance.pe),
    (fun _ => nCase "source" "multi-output" ``source),
    (fun _ => nCase "memCounter" "memory" ``Tests.Compiler.ReaderFuelGridTest.memCounter),
    (fun _ => nCase "twoMems" "memory" ``Tests.Compiler.ReaderFuelGridTest.twoMems),
    (fun _ => nCase "mixedMems" "memory" ``mixedMems),
    (fun _ => nCase "withMemory" "memory" ``withMemory),
    (fun _ => nCase "twoLoops" "refusal" ``Tests.Compiler.ReaderFuelGridTest.twoLoops),
    (fun _ => nCase "opaqueInit" "refusal" ``Tests.Compiler.ReaderFuelGridTest.opaqueInit),
    (fun _ => nCase "loopCall" "refusal" ``loopCall),
    (fun _ => nCase "notHw" "refusal" ``Tests.Compiler.ReaderFuelGridTest.notHw),
    (fun _ => nCase "natSig" "refusal" ``natSig),
    (fun _ => nCase "gridInit" "refusal" ``Tests.Compiler.ReaderFuelGridTest.gridInit),
    (fun _ => nCase "latchSymbolic" "refusal" ``Tests.Compiler.ReaderFuelGridTest.latch true)]
  let mut n := 0
  let mut timeouts := 0
  let mut disagreements := 0
  let mut compared := 0
  for c in cases do
    n := n + 1
    match ← c () with
    | 1 => timeouts := timeouts + 1
    | 2 => disagreements := disagreements + 1
    | 0 => compared := compared + 1
    | _ => pure ()
  let line := s!"NORMX SUMMARY: cases={n} expected={expectedCases} compared={compared} timeouts={timeouts} disagreements={disagreements}"
  (← IO.getStderr).putStrLn line
  logInfo m!"{line}"
  unless n == expectedCases && timeouts == 0 && disagreements == 0 do
    throwError m!"{line}: check FAILED (need cases=40, timeouts=0, disagreements=0)"

end Tests.Compiler.NormXExecTest
