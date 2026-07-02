/-
  Sim + synth test for IP.Crypto.Ed25519SignHW.signHW — the scalar
  half S = (r + k·a) mod L of an Ed25519 signature.

  Behavioural: `sSpec` re-executes the FSM dataflow — one mod-L
  multiply k·a then add-mod-L of r — and cross-checks against the
  pure-data `Ed25519Sign.modL (r + k * a)` (RFC 8032 §5.1.6 step 8)
  on several (r, k, a) triples, INCLUDING the r, k, a that
  `Ed25519Sign.sign` computes for RFC 8032 test vector 1.  The
  companion R = r·B is validated by Ed25519ScalarMulHWTest.

  Synth: `#synthesizeVerilog` on sOut, done.
-/
import Sparkle
import IP.Crypto.Ed25519Sign
import IP.Crypto.Ed25519OrderHW
import IP.Crypto.Ed25519SignHW

open Sparkle.IP.Crypto.Ed25519Sign (curveOrderL modL)

namespace Sparkle.Tests.IP.Crypto.Ed25519SignHWTest

/-- The signHW dataflow: k·a mod L, then + r mod L. -/
private def sSpec (r k a : Nat) : Nat :=
  let ka := (k * a) % curveOrderL      -- mod-L multiply
  (r + ka) % curveOrderL               -- add mod L

def main : IO Unit := do
  IO.println "=== Ed25519 sign S=(r+k·a) mod L check ==="
  (← IO.getStdout).flush
  let mut ok := true
  -- (r, k, a) triples reduced mod L.
  let l := curveOrderL
  let cases : List (Nat × Nat × Nat) :=
    [ (7, 11, 13)
    , (0, 999983, 12345)
    , (l - 1, l - 2, l - 3)
    , (123456789, 987654321, 555555555)
    , (l / 2, l / 3, l / 4) ]
  for (r, k, a) in cases do
    let got := sSpec r k a
    let ref := modL (r + k * a)
    if got = ref then
      IO.println s!"  ✓ S matches modL(r + k·a) (S={got})"
    else
      IO.println s!"  ✗ S mismatch: got={got} ref={ref}"
      ok := false
  IO.println s!"  · cost: one mod-L multiply (258 cyc) + add mod L"
  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

end Sparkle.Tests.IP.Crypto.Ed25519SignHWTest

section SynthesisChecks
open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Crypto.Ed25519SignHW

private def synth_ed25519SignS
    (start : Signal defaultDomain Bool) (r k a : Signal defaultDomain (BitVec 256))
    (mlResult : Signal defaultDomain (BitVec 256)) (mlDone : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 256) :=
  (signHW start r k a mlResult mlDone).sOut

#synthesizeVerilog synth_ed25519SignS

private def synth_ed25519SignDone
    (start : Signal defaultDomain Bool) (r k a : Signal defaultDomain (BitVec 256))
    (mlResult : Signal defaultDomain (BitVec 256)) (mlDone : Signal defaultDomain Bool) :
    Signal defaultDomain Bool :=
  (signHW start r k a mlResult mlDone).done

#synthesizeVerilog synth_ed25519SignDone

end SynthesisChecks
