import Tests.Ved.U1MultiLoopRow
import Tests.IP.Control.PIDTest

/-!
# `#ved_u1` on a real `Signal.loop` row, part 5 (PID controller with anti-windup)

`Sparkle.Tests.IP.Control.PIDTest.pidTop` (registers 32/32 bits: integrator and previous error): the original
declaration is accepted by `#ved_u1` with the strict audit, then `checkRows` compares the stored type with `==`
and checks the axioms.  `U1MultiLoopAll` checks all rows together.

The goal of the step has a large error term repeated in every arm of the nested clamps (341 331 nodes read as a
tree, 79 distinct subterms); `omega` on it runs out of memory.  The script closes it with `ved_wire`
(`Tools/VedU1Wire.lean`): every operation becomes a variable, equal-valued wires are proved equal one at a time
by `omega` in a small context, and the proofs are auxiliary theorems.
-/

namespace Tests.Ved.U1MultiLoopFull5

open Lean Elab Command
open Tests.Ved.U1MultiLoopRow

#guard_msgs (drop info) in
#ved_u1_pub Sparkle.Tests.IP.Control.PIDTest.pidTop

def rows : List (Name × Name) :=
  [(.anonymous, `Sparkle.Tests.IP.Control.PIDTest.pidTop)]

/-- info: OK 1 rows: stored type = U1Stmt c m F, axioms within std3 -/
#guard_msgs in
run_cmd checkRows rows

example : rows.length = 1 := by decide

end Tests.Ved.U1MultiLoopFull5
