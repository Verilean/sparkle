/-
  Sim test for IP.Crypto.Goldilocks.

  Algebraic invariant checks for the Goldilocks prime field.
-/

import IP.Crypto.Proof.Goldilocks

open Sparkle.IP.Crypto.Goldilocks

namespace Sparkle.Tests.IP.Crypto.GoldilocksTest

def main : IO Unit := do
  IO.println "=== Goldilocks field sim ==="
  let mut ok := true

  -- 1. p layout.
  IO.println s!"  p = 2^64 - 2^32 + 1 = 0x{Nat.toDigits 16 p |> String.ofList}"
  IO.println s!"  (expected 0xffffffff00000001)"
  let pOk := p = 0xFFFFFFFF00000001
  if !pOk then ok := false

  -- 2. Identity: 0 + a = a.
  let r1 := add 0 42
  let okAdd0 := r1 = 42
  IO.println s!"  0 + 42 = {r1} {if okAdd0 then "✓" else "✗"}"
  if !okAdd0 then ok := false

  -- 3. Wrap: (p-1) + 1 = 0.
  let r2 := add (p - 1) 1
  let okWrap := r2 = 0
  IO.println s!"  (p-1) + 1 = {r2} (expected 0) {if okWrap then "✓" else "✗"}"
  if !okWrap then ok := false

  -- 4. Sub underflow: 0 - 1 = p - 1.
  let r3 := sub 0 1
  let okNeg := r3 = p - 1
  IO.println s!"  0 - 1 = p - 1 ? {if okNeg then "✓" else "✗"}"
  if !okNeg then ok := false

  -- 5. Small mul.
  let r4 := mul 7 11
  IO.println s!"  7 * 11 = {r4} {if r4 = 77 then "✓" else "✗"}"
  if r4 ≠ 77 then ok := false

  -- 6. Fermat inverse round-trip.
  let aInv := inv 7
  let r5 := mul 7 aInv
  IO.println s!"  7 * inv(7) = {r5} (expected 1) {if r5 = 1 then "✓" else "✗"}"
  if r5 ≠ 1 then ok := false

  -- 7. 2^64 mod p: should equal 2^32 - 1 (a Goldilocks identity).
  let r6 := powMod 2 64
  IO.println s!"  2^64 mod p = {r6} (expected {2^32 - 1}) {if r6 = 2^32 - 1 then "✓" else "✗"}"
  if r6 ≠ 2^32 - 1 then ok := false

  -- 8. Primitive 2^32-th root: g^(2^32) = 1.
  let r7 := powMod gen2pow32 (2^32)
  IO.println s!"  gen2pow32^(2^32) = {r7} (expected 1) {if r7 = 1 then "✓" else "✗"}"
  if r7 ≠ 1 then ok := false

  -- 9. AND g^(2^31) ≠ 1 (it's exactly order 2^32, not a smaller divisor).
  let r8 := powMod gen2pow32 (2^31)
  IO.println s!"  gen2pow32^(2^31) = {r8} (expected ≠ 1) {if r8 ≠ 1 then "✓" else "✗"}"
  if r8 = 1 then ok := false

  if ok then
    IO.println "\nALL PASS"
  else
    IO.println "\nFAIL"
    IO.Process.exit 1

end Sparkle.Tests.IP.Crypto.GoldilocksTest
