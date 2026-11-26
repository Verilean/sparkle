import Tests.Ved.U1MultiLoopRow
import Tests.IP.Net.HFTStrategyTest
import Tests.IP.Net.HTTPTest
import Tests.IP.Net.SLIPTest

/-!
# `#ved_u1` on real `Signal.loop` rows, part 3 of 3 (HFT strategy, HTTP, SLIP)

Rows of sparkle-ved-u1-multiloop not in the PR check `U1MultiLoopCheck` (which holds the representative
rows and the refusal controls); split so no single Lake module carries all 26 proofs.  Each original
`private` declaration is accepted by `#ved_u1` with the strict audit, then `checkRows` compares the stored
types with `==` and checks the axioms.  `U1MultiLoopAll` checks all 26 rows together.
-/

namespace Tests.Ved.U1MultiLoopFull3

open Lean Elab Command
open Tests.Ved.U1MultiLoopRow

#guard_msgs (drop info) in
#ved_u1_row Tests.IP.Net.HFTStrategyTest synth_hftEmitCount
#guard_msgs (drop info) in
#ved_u1_row Tests.IP.Net.HFTStrategyTest synth_hftTriggerSeen
#guard_msgs (drop info) in
#ved_u1_row Tests.IP.Net.HTTPTest synth_httpRequestParser
#guard_msgs (drop info) in
#ved_u1_row Tests.IP.Net.HTTPTest synth_httpStatus
#guard_msgs (drop info) in
#ved_u1_row Tests.IP.Net.SLIPTest synth_slipFramerByte

def rows : List (Name × Name) :=
  [(`Tests.IP.Net.HFTStrategyTest, `synth_hftEmitCount),
   (`Tests.IP.Net.HFTStrategyTest, `synth_hftTriggerSeen),
   (`Tests.IP.Net.HTTPTest, `synth_httpRequestParser),
   (`Tests.IP.Net.HTTPTest, `synth_httpStatus),
   (`Tests.IP.Net.SLIPTest, `synth_slipFramerByte)]

/-- info: OK 5 rows: stored type = U1Stmt c m F, axioms within std3 -/
#guard_msgs in
run_cmd checkRows rows

example : rows.length = 5 := by decide

end Tests.Ved.U1MultiLoopFull3
