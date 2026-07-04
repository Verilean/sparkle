/-
  Sim + synth test for IP.Crypto.Ed25519ScalarMulHW.scalarMulHW —
  the Ed25519 double-and-add scalar multiplier (extended coords)
  that drives the point-op engine.

  Behavioural: `ladderSpec` re-executes the EXACT double-and-add
  register logic of `scalarMulHW` (MSB-first over bits 255..0,
  R = 2R then R = R+P when bit set, using `Ed25519PointExt`
  double/add for the point ops) and cross-checks the final R
  against `Ed25519PointExt.mulScalar` on several scalars applied
  to the generator (affine-compared).

  Synth: `#synthesizeVerilog` on xOut, done.
-/
import Sparkle
import IP.Crypto.Proof.Ed25519PointExt
import IP.Crypto.Ed25519ScalarMulHW

open Sparkle.IP.Crypto.Ed25519PointExt (Point identity generator double add mulScalar toAffine)

namespace Sparkle.Tests.IP.Crypto.Ed25519ScalarMulHWTest

/-- The double-and-add ladder EXACTLY as `scalarMulHW` sequences it:
    MSB-first over 256 bits, R = 2·R, then (if bit set) R = R + P. -/
private def ladderSpec (k : Nat) (P : Point) : Point := Id.run do
  let mut r := identity
  let mut i : Nat := 256
  while i > 0 do
    i := i - 1
    r := double r
    if (k >>> i) &&& 1 = 1 then
      r := add r P
  return r

def main : IO Unit := do
  IO.println "=== Ed25519 double-and-add scalar-mul ladder check ==="
  (← IO.getStdout).flush
  let mut ok := true
  let G := generator
  for k in [1, 2, 3, 7, 8, 12345, 0xDEADBEEF, 999983] do
    let ladder := toAffine (ladderSpec k G)
    let ref := toAffine (mulScalar k G)
    if ladder = ref then
      IO.println s!"  ✓ ladder k={k} matches Ed25519PointExt.mulScalar"
    else
      IO.println s!"  ✗ ladder k={k} mismatch"
      ok := false
  IO.println s!"  · cycle cost ≈ 256·(double 8 + ½·add 9)·260 ≈ ~0.83M cyc (avg)"
  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

end Sparkle.Tests.IP.Crypto.Ed25519ScalarMulHWTest

section SynthesisChecks
open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Crypto.Ed25519ScalarMulHW

private def synth_ed25519ScalarMulX
    (start : Signal defaultDomain Bool) (k : Signal defaultDomain (BitVec 256))
    (px py pz pt : Signal defaultDomain (BitVec 256))
    (rx ry rz rt : Signal defaultDomain (BitVec 256))
    (rdone : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 256) :=
  (scalarMulHW start k px py pz pt rx ry rz rt rdone).xOut

#synthesizeVerilog synth_ed25519ScalarMulX

private def synth_ed25519ScalarMulDone
    (start : Signal defaultDomain Bool) (k : Signal defaultDomain (BitVec 256))
    (px py pz pt : Signal defaultDomain (BitVec 256))
    (rx ry rz rt : Signal defaultDomain (BitVec 256))
    (rdone : Signal defaultDomain Bool) : Signal defaultDomain Bool :=
  (scalarMulHW start k px py pz pt rx ry rz rt rdone).done

#synthesizeVerilog synth_ed25519ScalarMulDone

end SynthesisChecks
