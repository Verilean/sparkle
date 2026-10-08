import Tests.Compiler.ShippingMachineInstTest
import Tools.ShippingMachineShipsHierHCommand
import Tools.ShippingPremiseEval

/-! The premise evaluator never reads the unverified as verified.

`Tools.ShippingPremiseEval.Verdict` has fixed fields; the module verdict is
`PREM` only when the theorem's checker, the child bound and every boundary
check HOLD, and the trace verdict `MATCHED` only when at least one boundary
trace was taken and all matched. Negative cases: a real parent calling two
DIFFERENT children (the call–instance correspondence is not reconstructed:
`UNTRACED`), a verdict with nothing evaluated, one with no trace, one with a
rejected premise. -/
namespace Sparkle.Tests.Compiler.ShippingPremiseEvalTest
open Lean
open Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.Tests.Compiler.ShippingMachineInstTest
open Tools.ShippingPremiseEval

/-- A machine calling two different combinational children. -/
def callerMix (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let sel ← Signal.reg 0#2
    let acc ← Signal.reg 0#8
    let selS := (sel : Signal defaultDomain (BitVec 2))
    let accS := (acc : Signal defaultDomain (BitVec 8))
    let y := pick selS (accS + x)
    let z := pickD selS y
    sel <~ selS + (Signal.pure 1#2 : Signal defaultDomain (BitVec 2))
    acc <~ z
    return z

set_option maxHeartbeats 0 in
#machine_endpoint callerMix
set_option maxHeartbeats 0 in
#machine_linked callerMix
set_option maxHeartbeats 0 in
#machine_composed callerMix
#machine_ships_hierH callerMix

run_cmd Lean.Elab.Command.liftTermElabM do
  -- several children: generated, module premises hold, but the boundary is NOT traced
  let v ← evalShipsHierH ``callerMix
  Lean.logInfo m!"{v.report}"
  unless v.moduleTag == "MOD:PREM" && v.traceTag == "TRACE:UNTRACED" && !v.applies do
    throwError "callerMix: {v.tag}"
  -- nothing evaluated: unknown, not applying
  let v0 : Verdict := { theoremName := "nothing" }
  unless v0.moduleTag.startsWith "MOD:UNKNOWN" && v0.traceTag == "TRACE:UNTRACED" && !v0.applies do
    throwError "empty verdict: {v0.tag}"
  -- every module check holds but no trace taken: not applying
  let v1 : Verdict := { theoremName := "no trace", checker := .holds, childBound := .holds, svParent := .holds }
  unless v1.tag == "MOD:PREM|TRACE:UNTRACED|SV:PARENT|SVCHILD:OPEN|CLOSED:NA" && !v1.applies do
    throwError "no-trace verdict: {v1.tag}"
  -- only unknown boundary facts: unknown
  let v2 : Verdict := { theoremName := "unknown", checker := .holds, childBound := .holds, boundaryChecks := [("x", .unknown "not evaluated")], traces := [("t", .matched)] }
  unless v2.moduleTag == "MOD:UNKNOWN:x" && !v2.applies do throwError "unknown verdict: {v2.tag}"
  -- a rejected premise: NOPREM even with everything else fine
  let v3 : Verdict := { theoremName := "rejected", checker := .fails "no", childBound := .holds, traces := [("t", .matched)], svParent := .holds }
  unless v3.moduleTag == "MOD:NOPREM:checker" && !v3.applies do throwError "rejected verdict: {v3.tag}"
  -- a mismatched trace
  let v4 : Verdict := { theoremName := "mismatch", checker := .holds, childBound := .holds, traces := [("t", .matched), ("u", .mismatch "differs")] }
  unless v4.traceTag == "TRACE:MISMATCH" && !v4.applies do throwError "mismatch verdict: {v4.tag}"
  -- the children's texts checked but a child not assigning its outputs: uniqueness not claimed
  let v5 : Verdict := { theoremName := "no outs", checker := .holds, childBound := .holds, traces := [("t", .matched)], svChildren := .holds, uniqueCheck := .fails "unassigned output" }
  unless v5.uniqTag == "CLOSED:UNPROVEN" do throwError "uniqueness verdict: {v5.tag}"
  -- designCheck false or unknown, or outsCheck false or unknown: never AT-MOST-ONE
  let cases : List (Status × Status) := [(.fails "x", .holds), (.unknown "x", .holds), (.holds, .fails "x"),
    (.holds, .unknown "x"), (.fails "x", .fails "y"), (.unknown "x", .unknown "y")]
  for (dc, oc) in cases do
    let v : Verdict := { theoremName := "u", checker := .holds, childBound := .holds, traces := [("t", .matched)], svChildren := dc, uniqueCheck := oc }
    if v.uniqTag == "CLOSED:AT-MOST-ONE" then throwError "uniqueness claimed for {repr dc} / {repr oc}"
  Lean.logInfo m!"PREMISE EVAL: unverified / untraced / empty / rejected / mismatched never count as applying"

end Sparkle.Tests.Compiler.ShippingPremiseEvalTest
