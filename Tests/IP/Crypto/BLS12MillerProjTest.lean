/-
  Sim test for IP.Crypto.BLS12MillerProj — the projective Miller
  loop reference.  Confirms it computes the SAME optimal-ate
  pairing as the shipped affine `Pairing.pairing`, at the
  post-final-exponentiation level, on the generators and on
  scaled inputs (bilinearity), plus a full sign→verify built on
  the projective pairing.
-/
import IP.Crypto.BLS12_381
import IP.Crypto.BLS12MillerProj

open Sparkle.IP.Crypto.BLS12_381
open Sparkle.IP.Crypto.BLS12MillerProj

namespace Sparkle.Tests.IP.Crypto.BLS12MillerProjTest

def main : IO Unit := do
  IO.println "=== BLS12-381 projective Miller loop (vs affine reference) ==="
  (← IO.getStdout).flush
  let mut ok := true

  let g1 := G1.generator
  let g2 := G2.generator

  -- 1. Projective pairing on the generators equals the shipped pairing.
  let eRef := Pairing.pairing g1 g2
  let eProj := pairingProj g1 g2
  if eProj == eRef then
    IO.println "  ✓ pairingProj(g1,g2) == pairing(g1,g2)"
  else
    IO.println "  ✗ pairingProj(g1,g2) ≠ pairing(g1,g2)"; ok := false
  (← IO.getStdout).flush

  -- 2. Non-degenerate.
  if eProj == Fp12.one then
    IO.println "  ✗ pairingProj degenerate (=1)"; ok := false
  else
    IO.println "  ✓ pairingProj(g1,g2) ≠ 1"
  (← IO.getStdout).flush

  -- 3. Bilinearity on scaled inputs, and agreement with the affine
  --    pairing on those too.
  let a : Nat := 5
  let eProjA := pairingProj (G1.mulScalar a g1) g2
  let eRefA := Pairing.pairing (G1.mulScalar a g1) g2
  let ePow := Fp12.pow eProj a
  if eProjA == eRefA ∧ eProjA == ePow then
    IO.println "  ✓ bilinear + matches affine: eProj(5·g1,g2) = eProj^5 = eRef(5·g1,g2)"
  else
    IO.println "  ✗ bilinearity / affine agreement FAILED"; ok := false
  (← IO.getStdout).flush

  -- 4. A full sign→verify using the projective pairing.
  let msg : Array UInt8 := "sparkle-miller-proj".toUTF8.toList.toArray
  let sk : Nat := 0xFEEDFACE
  let pk := derivePublicKey sk
  let sig := sign sk msg
  let hm := hashToG2 msg
  let lhs := pairingProj G1.generator sig
  let rhs := pairingProj pk hm
  if lhs == rhs then
    IO.println "  ✓ projective verify: e(g1,σ) = e(pk,H(m)) on a real sig"
  else
    IO.println "  ✗ projective verify FAILED"; ok := false
  -- Wrong message must NOT verify.
  let hmBad := hashToG2 ("wrong".toUTF8.toList.toArray)
  if pairingProj pk hmBad == lhs then
    IO.println "  ✗ projective verify accepted wrong message"; ok := false
  else
    IO.println "  ✓ projective verify rejects wrong message"
  (← IO.getStdout).flush

  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

end Sparkle.Tests.IP.Crypto.BLS12MillerProjTest
