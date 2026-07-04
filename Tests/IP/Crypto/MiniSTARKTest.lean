/-
  Sim test for IP.Crypto.MiniSTARK — end-to-end polynomial
  commitment + opening verification.

  Scenario:
    Prover picks polynomial p(x) = 7 + 3x + 5x² over
    Goldilocks.  Evaluation domain D = {1, 2, 3, 4, 5, 6,
    7, 8} (8 points).  Commits to evaluations, then opens
    at j=3 (= x=4).

    Expected p(4) = 7 + 12 + 80 = 99.

  Verifier checks:
    1. The opening at j=3 is valid (Merkle ✓ + Horner ✓).
    2. Tampering with the claimed value (99 → 100) fails.
    3. Tampering with the polynomial fails too.
    4. Wrong index fails.
-/

import IP.Crypto.Proof.MiniSTARK
import IP.Crypto.Proof.Polynomial

open Sparkle.IP.Crypto.MiniSTARK
open Sparkle.IP.Crypto.Polynomial

namespace Sparkle.Tests.IP.Crypto.MiniSTARKTest

def main : IO Unit := do
  IO.println "=== Mini-STARK commitment + open sim ==="
  let mut ok := true

  -- Setup: p(x) = 7 + 3x + 5x².
  let poly : Poly := #[7, 3, 5]
  let xs : Array Nat := #[1, 2, 3, 4, 5, 6, 7, 8]
  let (root, ys) := commitPoly poly xs
  IO.println s!"  committed root size = {root.size} bytes (expected 32)"

  -- Honest opening at j=3 (= x=4).  Expected p(4) = 7 + 12 + 80 = 99.
  let (yClaimed, path) := openPoly ys 3
  IO.println s!"  opened y at j=3 = {yClaimed} (expected 99)"

  -- 1. Honest verify.
  let v1 := verifyOpenPoly poly xs root 3 yClaimed path
  IO.println s!"  verifier on honest opening = {v1} (expected true)"
  if !v1 then ok := false

  -- 2. Tampered claimed-y.  Should fail (Merkle path
  --    doesn't reconstruct → root mismatch).
  let v2 := verifyOpenPoly poly xs root 3 100 path
  IO.println s!"  verifier on tampered y (99→100) = {v2} (expected false)"
  if v2 then ok := false

  -- 3. Honest Merkle path but tampered polynomial: Horner
  --    eval gives a different value → polyOk = false.
  let badPoly : Poly := #[7, 3, 6]  -- 5→6 in the x² coefficient
  let v3 := verifyOpenPoly badPoly xs root 3 yClaimed path
  IO.println s!"  verifier on tampered polynomial = {v3} (expected false)"
  if v3 then ok := false

  -- 4. Wrong opening index: Merkle path for j=3, claim j=5.
  let v4 := verifyOpenPoly poly xs root 5 yClaimed path
  IO.println s!"  verifier on wrong index (3 vs 5) = {v4} (expected false)"
  if v4 then ok := false

  -- 5. Test all 8 honest openings round-trip.
  let mut allOpen := true
  for h : i in [:8] do
    let (yi, pi) := openPoly ys i
    let vi := verifyOpenPoly poly xs root i yi pi
    if !vi then
      IO.println s!"  ✗ honest opening at j={i} failed"
      allOpen := false
  if allOpen then
    IO.println "  ✓ all 8 honest openings round-trip successfully"
  else ok := false

  if ok then
    IO.println "\nALL PASS"
  else
    IO.println "\nFAIL"
    IO.Process.exit 1

end Sparkle.Tests.IP.Crypto.MiniSTARKTest
