/-
  Sim test for IP.Crypto.BLS12_381 — the pure-data BLS
  signature-scheme reference.

  Checks:
    1. Tower / group sanity: G1 and G2 generators lie on their
       curves; the pairing e(g1, g2) is non-degenerate (≠ 1).
    2. Pairing bilinearity: e(a·g1, g2) = e(g1, a·g2) = e(g1,g2)^a.
       (Bilinearity + non-degeneracy is what makes sign/verify
       sound; we assert it directly.)
    3. Sign → Verify round-trip PASSES.
    4. Tampered signature FAILS verification.
    5. Aggregate of 3 signatures over the SAME message verifies.

  TEST-VECTOR PROVENANCE (be explicit): these are
  SELF-CONSISTENCY checks (sk → pk = sk·g1, σ = sk·H(m), and the
  pairing identity e(g1, σ) = e(pk, H(m))), NOT third-party
  known-answer vectors.  The hash-to-curve here is the
  documented SIMPLE placeholder (real RFC 9380 expand_message_xmd
  over SHA-256 feeding a scalar·G2 map — see BLS12_381.lean's
  Layer-8 note), so signatures are intentionally NOT
  bit-compatible with blst / the eth2 KAT suite.  What IS
  exercised end-to-end is the full field tower (Fp→Fp2→Fp6→Fp12),
  G1/G2 arithmetic, and the real optimal-ate pairing (Miller loop
  transcribed from py_ecc + full (p¹²-1)/r final exponentiation).
-/
import IP.Crypto.BLS12_381

open Sparkle.IP.Crypto.BLS12_381

namespace Sparkle.Tests.IP.Crypto.BLS12381Test

def main : IO Unit := do
  IO.println "=== BLS12-381 signature scheme (pure-data reference) ==="
  (← IO.getStdout).flush
  let mut ok := true

  -- 1. Generators on their curves.
  let g1 := G1.generator
  let g2 := G2.generator
  if G1.onCurve g1 then IO.println "  ✓ G1 generator on E(Fp): y²=x³+4"
  else do IO.println "  ✗ G1 generator OFF curve"; ok := false
  if G2.onCurve g2 then IO.println "  ✓ G2 generator on E'(Fp2): y²=x³+4(u+1)"
  else do IO.println "  ✗ G2 generator OFF curve"; ok := false
  (← IO.getStdout).flush

  -- 2. Pairing non-degeneracy + bilinearity.
  let e := Pairing.pairing g1 g2
  if e == Fp12.one then do IO.println "  ✗ e(g1,g2) = 1 (degenerate!)"; ok := false
  else IO.println "  ✓ e(g1,g2) ≠ 1 (non-degenerate)"
  (← IO.getStdout).flush
  let a : Nat := 3
  let eA1 := Pairing.pairing (G1.mulScalar a g1) g2
  let eA2 := Pairing.pairing g1 (G2.mulScalar a g2)
  let ePow := Fp12.pow e a
  if eA1 == eA2 ∧ eA1 == ePow then
    IO.println "  ✓ bilinear: e(3·g1,g2) = e(g1,3·g2) = e(g1,g2)³"
  else
    IO.println "  ✗ bilinearity FAILED"; ok := false
  (← IO.getStdout).flush

  -- 3. Sign → Verify round-trip.
  let msg : Array UInt8 := "sparkle-bls-test".toUTF8.toList.toArray
  let sk : Nat := 0x1234567890ABCDEF
  let pk := derivePublicKey sk
  let sig := sign sk msg
  if verify pk msg sig then
    IO.println "  ✓ sign → verify round-trip PASSES"
  else
    IO.println "  ✗ sign → verify round-trip FAILED"; ok := false
  (← IO.getStdout).flush

  -- 4. Tampered signature fails.  Perturb σ by adding g2 (a
  --    valid-but-wrong point) so it is a genuine G2 point that
  --    is simply not sk·H(m).
  let sigBad := G2.add sig g2
  if verify pk msg sigBad then
    IO.println "  ✗ tampered signature ACCEPTED (should reject)"; ok := false
  else
    IO.println "  ✓ tampered signature correctly REJECTED"
  -- Also: verifying a good sig against the wrong message must fail.
  let msg2 : Array UInt8 := "different-message".toUTF8.toList.toArray
  if verify pk msg2 sig then
    IO.println "  ✗ wrong-message verify ACCEPTED (should reject)"; ok := false
  else
    IO.println "  ✓ wrong-message verify correctly REJECTED"
  (← IO.getStdout).flush

  -- 5. Aggregate of 3 signatures over the SAME message.
  let sks : List Nat := [111, 222, 333]
  let pks := sks.map derivePublicKey
  let sigs := sks.map (fun s => sign s msg)
  let aggSig := aggregate sigs
  if verifyAggregate pks msg aggSig then
    IO.println "  ✓ aggregate of 3 sigs verifies e(g1,Σσ)=e(Σpk,H(m))"
  else
    IO.println "  ✗ aggregate verification FAILED"; ok := false
  -- Aggregate with a wrong key set must fail.
  let pksBad := (444 :: sks.tail).map derivePublicKey
  if verifyAggregate pksBad msg aggSig then
    IO.println "  ✗ aggregate with wrong keyset ACCEPTED (should reject)"; ok := false
  else
    IO.println "  ✓ aggregate with wrong keyset correctly REJECTED"
  (← IO.getStdout).flush

  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

end Sparkle.Tests.IP.Crypto.BLS12381Test
