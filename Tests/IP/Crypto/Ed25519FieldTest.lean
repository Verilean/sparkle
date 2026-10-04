/-
  Sim test for IP.Crypto.Ed25519Field.

  Validates the pure-data field arithmetic against
  hand-computed test cases.  No HW engine yet — Phase L.2.b
  follows after the curve / signing layers are in place.
-/

import IP.Crypto.Proof.Ed25519Field

open Sparkle.IP.Crypto.Ed25519Field

namespace Sparkle.Tests.IP.Crypto.Ed25519FieldTest

private def hexOfBitVec (x : BitVec 256) : String := Id.run do
  let mut out := ""
  for i in [:32] do
    let lo := (31 - i) * 8
    let b := (x.toNat >>> lo) &&& 0xFF
    let hi := (b >>> 4) &&& 0xF
    let lo' := b &&& 0xF
    let digit (d : Nat) : Char :=
      if d < 10 then Char.ofNat (d + 0x30) else Char.ofNat (d - 10 + 0x61)
    out := out.push (digit hi)
    out := out.push (digit lo')
  return out

def main : IO Unit := do
  IO.println "=== Ed25519 field arithmetic sim ==="

  let mut ok := true

  -- p = 2^255 - 19; print to confirm.
  let pV := p
  IO.println s!"  p = 2^255 - 19 = ... (low 32 hex digits) {Nat.toDigits 16 (pV % (2^128)) |> String.ofList}"

  -- Identity: 0 + a = a.
  let a := 42
  let r1 := add 0 a
  let okAdd0 := r1 = 42
  IO.println s!"  0 + 42 = {r1} (expected 42) {if okAdd0 then "✓" else "✗"}"
  if !okAdd0 then ok := false

  -- Wrap: (p - 1) + 1 = 0
  let r2 := add (p - 1) 1
  let okWrap := r2 = 0
  IO.println s!"  (p-1) + 1 = {r2} (expected 0) {if okWrap then "✓" else "✗"}"
  if !okWrap then ok := false

  -- Sub negative: 0 - 1 = p - 1
  let r3 := sub 0 1
  let okSubNeg := r3 = p - 1
  IO.println s!"  0 - 1 = p - 1 ? {if okSubNeg then "✓" else "✗"}"
  if !okSubNeg then ok := false

  -- Multiplication: 2 * (p - 1) / 2 ≡ p - 1.  Just test
  -- a small known case: 7 * 11 = 77 (in field).
  let r4 := mul 7 11
  let okMul := r4 = 77
  IO.println s!"  7 * 11 = {r4} (expected 77) {if okMul then "✓" else "✗"}"
  if !okMul then ok := false

  -- Fermat inverse: a * a^(-1) = 1.
  let aInv := inv 7
  let oneTest := mul 7 aInv
  let okInv := oneTest = 1
  IO.println s!"  7 * inv(7) = {oneTest} (expected 1) {if okInv then "✓" else "✗"}"
  if !okInv then ok := false

  -- A bigger test: 2^254 * 2 mod p = 2^255 mod p = 19.
  let big := powMod 2 255
  let okBig := big = 19
  IO.println s!"  2^255 mod p = {big} (expected 19) {if okBig then "✓" else "✗"}"
  if !okBig then ok := false

  -- toBitVec / ofBitVec round-trip.
  let bv := toBitVec 12345
  let back := ofBitVec bv
  let okRt := back = 12345
  IO.println s!"  toBitVec ∘ ofBitVec round-trip: {if okRt then "✓" else "✗"}"
  if !okRt then ok := false

  let _ := hexOfBitVec

  if ok then
    IO.println "\nALL PASS"
  else
    IO.println "\nFAIL"
    IO.Process.exit 1

end Sparkle.Tests.IP.Crypto.Ed25519FieldTest
