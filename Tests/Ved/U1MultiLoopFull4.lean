import Tests.Ved.U1MultiLoopRow
import Tests.IP.Crypto.Fp381MontMulHWTest
import Tests.IP.Net.TCPStateTest

/-!
# `#ved_u1` on real `Signal.loop` rows, part 4 (Fp381 Montgomery multiplier, TCP server FSM)

Rows of sparkle-ved-u1-multiloop-rest: refused at the end of part 3 and accepted now.  Each original
`private` declaration is accepted by `#ved_u1` with the strict audit, then `checkRows` compares the stored
types with `==` and checks the axioms.  `U1MultiLoopAll` checks all rows together.

* `synth_fp381MontMulDone` (registers 448/384/384/5/1 bits): the step compares a 448-bit accumulator update with
  two products by a 32-bit literal; the kernel unfolds `x * n#w` by recursion on the literal, so the script
  commutes such products to `n#w * x` (`ved_mul_lit_bv`, `ved_mul_lit_nat`, `Tools/VedU1Loop.lean`);
* `synth_serverFsmTxReq` (registers 4/32/32/1 bits): the closing split uses the case hypotheses to settle the
  other tests on the same state, so the FSM state tests no longer multiply.
-/

namespace Tests.Ved.U1MultiLoopFull4

open Lean Elab Command
open Tests.Ved.U1MultiLoopRow

#guard_msgs (drop info) in
#ved_u1_row Tests.IP.Crypto.Fp381MontMulHWTest synth_fp381MontMulDone
#guard_msgs (drop info) in
#ved_u1_row Tests.IP.Net.TCPStateTest synth_serverFsmTxReq

def rows : List (Name × Name) :=
  [(`Tests.IP.Crypto.Fp381MontMulHWTest, `synth_fp381MontMulDone),
   (`Tests.IP.Net.TCPStateTest, `synth_serverFsmTxReq)]

/-- info: OK 2 rows: stored type = U1Stmt c m F, axioms within std3 -/
#guard_msgs in
run_cmd checkRows rows

example : rows.length = 2 := by decide

end Tests.Ved.U1MultiLoopFull4
