import Tests.Ved.U1MultiLoopRow
import Tests.IP.Crypto.Eip1559EnvelopeHWTest
import Tests.IP.Crypto.GHASHHWSynth
import Tests.IP.Crypto.HKDFHWTest
import Tests.IP.Crypto.ModInvHWTest

/-!
# `#ved_u1` on real `Signal.loop` rows, part 2 of 3 (EIP-1559 envelope, GHASH, HKDF, modular inverse)

Rows of sparkle-ved-u1-multiloop not in the PR check `U1MultiLoopCheck` (which holds the representative
rows and the refusal controls); split so no single Lake module carries all 26 proofs.  Each original
`private` declaration is accepted by `#ved_u1` with the strict audit, then `checkRows` compares the stored
types with `==` and checks the axioms.  `U1MultiLoopAll` checks all 26 rows together.
-/

namespace Tests.Ved.U1MultiLoopFull2

open Lean Elab Command
open Tests.Ved.U1MultiLoopRow

#guard_msgs (drop info) in
#ved_u1_row Tests.IP.Crypto.Eip1559EnvelopeHWTest synth_envDone
#guard_msgs (drop info) in
#ved_u1_row Tests.IP.Crypto.GHASHHWSynth synth_gmulHWResult
#guard_msgs (drop info) in
#ved_u1_row Tests.IP.Crypto.HKDFHWTest synth_hkdfCounter
#guard_msgs (drop info) in
#ved_u1_row Tests.IP.Crypto.HKDFHWTest synth_hkdfDone
#guard_msgs (drop info) in
#ved_u1_row Tests.IP.Crypto.HKDFHWTest synth_hkdfTrig
#guard_msgs (drop info) in
#ved_u1_row Tests.IP.Crypto.ModInvHWTest synth_modInvDone
#guard_msgs (drop info) in
#ved_u1_row Tests.IP.Crypto.ModInvHWTest synth_modInvMulStart

def rows : List (Name × Name) :=
  [(`Tests.IP.Crypto.Eip1559EnvelopeHWTest, `synth_envDone),
   (`Tests.IP.Crypto.GHASHHWSynth, `synth_gmulHWResult),
   (`Tests.IP.Crypto.HKDFHWTest, `synth_hkdfCounter),
   (`Tests.IP.Crypto.HKDFHWTest, `synth_hkdfDone),
   (`Tests.IP.Crypto.HKDFHWTest, `synth_hkdfTrig),
   (`Tests.IP.Crypto.ModInvHWTest, `synth_modInvDone),
   (`Tests.IP.Crypto.ModInvHWTest, `synth_modInvMulStart)]

/-- info: OK 7 rows: stored type = U1Stmt c m F, axioms within std3 -/
#guard_msgs in
run_cmd checkRows rows

example : rows.length = 7 := by decide

end Tests.Ved.U1MultiLoopFull2
