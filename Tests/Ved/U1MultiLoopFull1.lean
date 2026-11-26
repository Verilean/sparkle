import Tests.Ved.U1MultiLoopRow
import Tests.IP.Bus.DroneCANHWTest
import Tests.IP.Bus.PCIeTest
import Tests.IP.Bus.SBUSHWTest
import Tests.IP.Crypto.AESGCMHWTest
import Tests.IP.Crypto.BLS12MillerHWTest
import Tests.IP.Crypto.Ed25519SignHWTest
import Tests.IP.Crypto.RLPHWTest

/-!
# `#ved_u1` on real `Signal.loop` rows, part 1 of 3 (buses, AES-GCM, BLS12 Miller step, Ed25519, RLP)

Rows of sparkle-ved-u1-multiloop not in the PR check `U1MultiLoopCheck` (which holds the representative
rows and the refusal controls); split so no single Lake module carries all 26 proofs.  Each original
`private` declaration is accepted by `#ved_u1` with the strict audit, then `checkRows` compares the stored
types with `==` and checks the axioms.  `U1MultiLoopAll` checks all 26 rows together.
-/

namespace Tests.Ved.U1MultiLoopFull1

open Lean Elab Command
open Tests.Ved.U1MultiLoopRow

#guard_msgs (drop info) in
#ved_u1_row Tests.IP.Bus.DroneCANHWTest synth_droneCanTidError
#guard_msgs (drop info) in
#ved_u1_row Tests.IP.Bus.PCIeTest synth_tlpRxAddr
#guard_msgs (drop info) in
#ved_u1_row Tests.IP.Bus.SBUSHWTest synth_sbusIdx
#guard_msgs (drop info) in
#ved_u1_row Tests.IP.Bus.SBUSHWTest synth_sbusCh0
#guard_msgs (drop info) in
#ved_u1_row Tests.IP.Crypto.AESGCMHWTest synth_gcmTagY
#guard_msgs (drop info) in
#ved_u1_row Tests.IP.Crypto.AESGCMHWTest synth_gcmTagFire
#guard_msgs (drop info) in
#ved_u1_row Tests.IP.Crypto.BLS12MillerHWTest synth_millerStep_done
#guard_msgs (drop info) in
#ved_u1_row Tests.IP.Crypto.Ed25519SignHWTest synth_ed25519SignS
#guard_msgs (drop info) in
#ved_u1_row Tests.IP.Crypto.Ed25519SignHWTest synth_ed25519SignDone
#guard_msgs (drop info) in
#ved_u1_row Tests.IP.Crypto.RLPHWTest synth_rlpHeaderValid
#guard_msgs (drop info) in
#ved_u1_row Tests.IP.Crypto.RLPHWTest synth_rlpHeaderDone

def rows : List (Name × Name) :=
  [(`Tests.IP.Bus.DroneCANHWTest, `synth_droneCanTidError),
   (`Tests.IP.Bus.PCIeTest, `synth_tlpRxAddr),
   (`Tests.IP.Bus.SBUSHWTest, `synth_sbusIdx),
   (`Tests.IP.Bus.SBUSHWTest, `synth_sbusCh0),
   (`Tests.IP.Crypto.AESGCMHWTest, `synth_gcmTagY),
   (`Tests.IP.Crypto.AESGCMHWTest, `synth_gcmTagFire),
   (`Tests.IP.Crypto.BLS12MillerHWTest, `synth_millerStep_done),
   (`Tests.IP.Crypto.Ed25519SignHWTest, `synth_ed25519SignS),
   (`Tests.IP.Crypto.Ed25519SignHWTest, `synth_ed25519SignDone),
   (`Tests.IP.Crypto.RLPHWTest, `synth_rlpHeaderValid),
   (`Tests.IP.Crypto.RLPHWTest, `synth_rlpHeaderDone)]

/-- info: OK 11 rows: stored type = U1Stmt c m F, axioms within std3 -/
#guard_msgs in
run_cmd checkRows rows

example : rows.length = 11 := by decide

end Tests.Ved.U1MultiLoopFull1
