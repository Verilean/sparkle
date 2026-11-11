import Tests.Ved.U1MultiLoopCheck
import Tests.Ved.U1MultiLoopFull1
import Tests.Ved.U1MultiLoopFull2
import Tests.Ved.U1MultiLoopFull3

/-!
# All 26 accepted `Signal.loop` rows together (sparkle-ved-u1-multiloop)

Imports the PR check and the three full parts (no proof is re-run here) and checks, for the complete
list of 26 rows, that `<decl>.ved_u1` exists with stored type `==` `U1Stmt c m F` and std3 axioms,
and that the four files together hold exactly these rows (`rows.length = 26`, no duplicate).
-/

namespace Tests.Ved.U1MultiLoopAll

open Lean Elab Command
open Tests.Ved.U1MultiLoopRow

def rows : List (Name × Name) :=
  [(`Tests.IP.Net.UARTTest, `synth_uartTx),
   (`Tests.IP.Net.UARTTest, `synth_uartRx),
   (`Tests.IP.Crypto.Eip1559EnvelopeHWTest, `synth_envByte),
   (`Tests.IP.Bus.DroneCANHWTest, `synth_droneCanTidError),
   (`Tests.IP.Bus.PCIeTest, `synth_tlpRxAddr),
   (`Tests.IP.Bus.SBUSHWTest, `synth_sbusIdx),
   (`Tests.IP.Bus.SBUSHWTest, `synth_sbusCh0),
   (`Tests.IP.Crypto.AESGCMHWTest, `synth_gcmTagY),
   (`Tests.IP.Crypto.AESGCMHWTest, `synth_gcmTagFire),
   (`Tests.IP.Crypto.BLS12MillerHWTest, `synth_millerStep_done),
   (`Tests.IP.Crypto.Ed25519SignHWTest, `synth_ed25519SignS),
   (`Tests.IP.Crypto.Ed25519SignHWTest, `synth_ed25519SignDone),
   (`Tests.IP.Crypto.RLPHWTest, `synth_rlpHeaderValid),
   (`Tests.IP.Crypto.RLPHWTest, `synth_rlpHeaderDone),
   (`Tests.IP.Crypto.Eip1559EnvelopeHWTest, `synth_envDone),
   (`Tests.IP.Crypto.GHASHHWSynth, `synth_gmulHWResult),
   (`Tests.IP.Crypto.HKDFHWTest, `synth_hkdfCounter),
   (`Tests.IP.Crypto.HKDFHWTest, `synth_hkdfDone),
   (`Tests.IP.Crypto.HKDFHWTest, `synth_hkdfTrig),
   (`Tests.IP.Crypto.ModInvHWTest, `synth_modInvDone),
   (`Tests.IP.Crypto.ModInvHWTest, `synth_modInvMulStart),
   (`Tests.IP.Net.HFTStrategyTest, `synth_hftEmitCount),
   (`Tests.IP.Net.HFTStrategyTest, `synth_hftTriggerSeen),
   (`Tests.IP.Net.HTTPTest, `synth_httpRequestParser),
   (`Tests.IP.Net.HTTPTest, `synth_httpStatus),
   (`Tests.IP.Net.SLIPTest, `synth_slipFramerByte)]

example : rows.length = 26 := by decide

example : rows = Tests.Ved.U1MultiLoopCheck.rows ++ Tests.Ved.U1MultiLoopFull1.rows ++
    Tests.Ved.U1MultiLoopFull2.rows ++ Tests.Ved.U1MultiLoopFull3.rows := by decide

example : rows.Nodup := by decide

/-- info: OK 26 rows: stored type = U1Stmt c m F, axioms within std3 -/
#guard_msgs in
run_cmd checkRows rows

end Tests.Ved.U1MultiLoopAll
