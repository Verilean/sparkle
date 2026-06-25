/-
  Sim test for IP.Crypto.Secp256k1{Field, Point, ECDSA}.

  Layered checks:
    1. Field invariants (small ones).
    2. Base point on curve, 2·G matches the well-known
       published value.
    3. n · G = infinity (group order check).
    4. ECDSA sign + verify round-trip (self-consistency).
    5. ECDSA verify rejects a tampered message hash.
-/

import IP.Crypto.Secp256k1Field
import IP.Crypto.Secp256k1Point
import IP.Crypto.Secp256k1ECDSA

namespace Sparkle.Tests.IP.Crypto.Secp256k1Test

open Sparkle.IP.Crypto.Secp256k1Point
  (Point base baseX baseY add double mulScalar onCurve curveOrderN)
open Sparkle.IP.Crypto.Secp256k1ECDSA (sign verify derivePublicKey n)

/-- Well-known x-coord of 2·G. -/
def twoGx : Nat :=
  0xc6047f9441ed7d6d3045406e95c07cd85c778e4b8cef3ca7abac09b95c709ee5
/-- Well-known y-coord of 2·G. -/
def twoGy : Nat :=
  0x1ae168fea63dc339a3c58419466ceaeef7f632653266d0e1236431a950cfe52a

def main : IO Unit := do
  IO.println "=== secp256k1 sim ==="
  let mut ok := true

  -- 1. Field smoke checks.
  let pV := Sparkle.IP.Crypto.Secp256k1Field.p
  IO.println s!"  p (low 64 hex) = ...{Nat.toDigits 16 (pV % (2^256)) |> String.ofList |>.takeRight 64}"
  let r0 := Sparkle.IP.Crypto.Secp256k1Field.add (pV - 1) 1
  IO.println s!"  (p-1) + 1 mod p = {r0} (expected 0) {if r0 = 0 then "✓" else "✗"}"
  if r0 ≠ 0 then ok := false

  -- 2. Base point on curve.
  let baseOk := onCurve base
  IO.println s!"  G on curve = {baseOk}"
  if !baseOk then ok := false

  -- 3. 2·G matches the published value.
  let twoG := double base
  let twoOk := match twoG with
               | .affine x y => x == twoGx && y == twoGy
               | .infinity   => false
  IO.println s!"  2·G = published value ? {twoOk}"
  match twoG with
  | .affine x y =>
    IO.println s!"    x got: {Nat.toDigits 16 x |> String.ofList}"
    IO.println s!"    x exp: {Nat.toDigits 16 twoGx |> String.ofList}"
    IO.println s!"    y got: {Nat.toDigits 16 y |> String.ofList}"
    IO.println s!"    y exp: {Nat.toDigits 16 twoGy |> String.ofList}"
  | .infinity => IO.println "    (got infinity ?!)"
  if !twoOk then ok := false

  -- 4. mulScalar 2 G == double G.
  let mul2G := mulScalar 2 base
  let mulOk := mul2G == twoG
  IO.println s!"  mulScalar 2 G = double G ? {mulOk}"
  if !mulOk then ok := false

  -- 5. n · G = infinity (cyclic-group law).  Costs ~256
  -- iterations of double+add, each ~1 inversion (~256
  -- powMods).  Slow but tractable.
  IO.println "  (computing n · G — may take 60s)"
  let nG := mulScalar curveOrderN base
  let nGOk := match nG with
              | .infinity => true
              | _         => false
  IO.println s!"  n · G = infinity ? {nGOk}"
  if !nGOk then ok := false

  -- 6. ECDSA round-trip: sign + verify self-consistency.
  let d : Nat := 0x1234567890ABCDEF1234567890ABCDEF1234567890ABCDEF1234567890ABCDEF
  let q := derivePublicKey d
  let z : Nat := 0xDEADBEEFCAFEBABEDEADBEEFCAFEBABEDEADBEEFCAFEBABEDEADBEEFCAFEBABE
  let k : Nat := 0xFEEDFACE0BADF00DFEEDFACE0BADF00DFEEDFACE0BADF00DFEEDFACE0BADF00D
  IO.println "  (signing — may take ~30s)"
  match sign d k z with
  | none =>
    IO.println "    ✗ sign produced no signature (r=0 or s=0)"
    ok := false
  | some (r, s) =>
    IO.println s!"    r = {Nat.toDigits 16 r |> String.ofList}"
    IO.println s!"    s = {Nat.toDigits 16 s |> String.ofList}"
    IO.println "  (verifying — may take ~60s for 2 scalar mults)"
    let okVer := verify q z r s
    IO.println s!"    verify(Q, z, r, s) = {okVer} (expected true)"
    if !okVer then ok := false

    -- 7. Tampered message: flip a bit in z, verify should fail.
    let zBad := z ^^^ 1
    let okBad := verify q zBad r s
    IO.println s!"    verify(Q, z xor 1, r, s) = {okBad} (expected false)"
    if okBad then ok := false

  if ok then
    IO.println "\nALL PASS"
  else
    IO.println "\nFAIL"
    IO.Process.exit 1

end Sparkle.Tests.IP.Crypto.Secp256k1Test
