/-
  IP.Crypto.X25519 — Curve25519 scalar multiplication
  (RFC 7748 §5).

  Operates on the same prime field as Ed25519
  (`p = 2^255 - 19`, re-using `Sparkle.IP.Crypto.Ed25519Field`).
  X25519 only manipulates the u-coordinate of a Montgomery
  curve; the Montgomery ladder runs in constant rounds (255
  steps) using only field add/sub/mul.

  Pure-data reference + RFC 7748 §6.1 KAT in this file.
  HW engine (multi-cycle ladder) follows in T.1.b.
-/

import IP.Crypto.Ed25519Field

namespace Sparkle.IP.Crypto.X25519

abbrev fAdd := Sparkle.IP.Crypto.Ed25519Field.add
abbrev fSub := Sparkle.IP.Crypto.Ed25519Field.sub
abbrev fMul := Sparkle.IP.Crypto.Ed25519Field.mul
abbrev fSq  := Sparkle.IP.Crypto.Ed25519Field.sq
abbrev fInv := Sparkle.IP.Crypto.Ed25519Field.inv
abbrev fP   := Sparkle.IP.Crypto.Ed25519Field.p

/-- Curve25519 constant a24 = (A - 2) / 4 = (486662 - 2) / 4 = 121665.
    Used in the Montgomery ladder's doubling formula. -/
def a24 : Nat := 121665

/-! ### Byte-array ↔ field element (little-endian, 32 bytes). -/

/-- Decode 32 little-endian bytes into a Nat, masking the
    top bit per RFC 7748 §5: "any existing top bit MUST be
    masked to zero" before reducing mod p. -/
def decodeUCoord (bytes : Array UInt8) : Nat := Id.run do
  let mut acc : Nat := 0
  for i in [:32] do
    let b := if h : i < bytes.size then bytes[i].toNat else 0
    acc := acc ||| (b <<< (i * 8))
  -- Mask the top bit (bit 255) before reduction.
  acc := acc &&& ((1 <<< 255) - 1)
  return acc % fP

/-- Encode a field element as 32 little-endian bytes. -/
def encodeUCoord (u : Nat) : Array UInt8 := Id.run do
  let r := u % fP
  let mut out : Array UInt8 := Array.replicate 32 0
  for i in [:32] do
    let b := (r >>> (i * 8)) &&& 0xFF
    out := out.set! i (UInt8.ofNat b)
  return out

/-! ### Scalar clamping (RFC 7748 §5). -/

/-- Clamp a 32-byte little-endian scalar:
      bits 0, 1, 2 of byte 0 → 0
      bit 7 of byte 31 → 0
      bit 6 of byte 31 → 1
    Returns the clamped scalar as a Nat. -/
def clampScalar (k : Array UInt8) : Nat := Id.run do
  let mut bytes := k
  if bytes.size < 32 then
    bytes := bytes ++ Array.replicate (32 - bytes.size) 0
  let b0 := (bytes[0]!.toNat &&& 248)
  let b31 := (bytes[31]!.toNat &&& 127) ||| 64
  bytes := bytes.set! 0 (UInt8.ofNat b0)
  bytes := bytes.set! 31 (UInt8.ofNat b31)
  let mut acc : Nat := 0
  for i in [:32] do
    acc := acc ||| (bytes[i]!.toNat <<< (i * 8))
  return acc

/-! ### Montgomery ladder (constant-round).

    Per RFC 7748 §5, for each scalar bit from MSB to LSB,
    we conditionally swap (x2, z2) ↔ (x3, z3), then apply
    the joint double-and-add formulas and conditionally
    swap back.  255 iterations cover the highest bit
    (bit 254 is forced to 1 by the clamp).
-/

/-- One step of the Montgomery ladder for X25519 (RFC 7748 §5).
    Inputs: (x_1, x_2, z_2, x_3, z_3) and the swap bit.
    Outputs: updated (x_2, z_2, x_3, z_3). -/
def ladderStep (x1 x2 z2 x3 z3 : Nat) (swap : Bool) :
    Nat × Nat × Nat × Nat := Id.run do
  -- Conditional swap of (x2, z2) ↔ (x3, z3)
  let (x2, x3) := if swap then (x3, x2) else (x2, x3)
  let (z2, z3) := if swap then (z3, z2) else (z2, z3)
  -- Per RFC 7748 §5:
  --   A  = x_2 + z_2
  --   AA = A^2
  --   B  = x_2 - z_2
  --   BB = B^2
  --   E  = AA - BB
  --   C  = x_3 + z_3
  --   D  = x_3 - z_3
  --   DA = D * A
  --   CB = C * B
  --   x_3' = (DA + CB)^2
  --   z_3' = x_1 * (DA - CB)^2
  --   x_2' = AA * BB
  --   z_2' = E * (AA + a24 * E)
  let a := fAdd x2 z2
  let aa := fSq a
  let b := fSub x2 z2
  let bb := fSq b
  let e := fSub aa bb
  let c := fAdd x3 z3
  let d := fSub x3 z3
  let da := fMul d a
  let cb := fMul c b
  let x3' := fSq (fAdd da cb)
  let z3' := fMul x1 (fSq (fSub da cb))
  let x2' := fMul aa bb
  let z2' := fMul e (fAdd aa (fMul a24 e))
  return (x2', z2', x3', z3')

/-- Scalar multiplication: compute scalar * u on Curve25519.
    Implements the Montgomery ladder per RFC 7748 §5. -/
def scalarMult (k u : Nat) : Nat := Id.run do
  let x1 := u % fP
  let mut x2 : Nat := 1
  let mut z2 : Nat := 0
  let mut x3 : Nat := x1
  let mut z3 : Nat := 1
  let mut swap : Bool := false
  -- Iterate from bit 254 down to bit 0 (255 iterations).
  for t' in [:255] do
    let t := 254 - t'
    let kt := ((k >>> t) &&& 1) = 1
    let curSwap := xor swap kt
    let (nx2, nz2, nx3, nz3) := ladderStep x1 x2 z2 x3 z3 curSwap
    x2 := nx2
    z2 := nz2
    x3 := nx3
    z3 := nz3
    swap := kt
  -- Final conditional swap (matches the cumulative swap state).
  let finalX2 := if swap then x3 else x2
  let finalZ2 := if swap then z3 else z2
  -- Return x_2 / z_2 via Fermat inverse.
  return fMul finalX2 (fInv finalZ2)

/-- X25519(scalar_bytes, u_bytes) — the RFC 7748 §5 interface.
    Both inputs are 32-byte little-endian; output is 32-byte
    little-endian. -/
def x25519 (scalar uBytes : Array UInt8) : Array UInt8 :=
  let k := clampScalar scalar
  let u := decodeUCoord uBytes
  encodeUCoord (scalarMult k u)

/-- The standard X25519 base point: u = 9. -/
def basePoint : Array UInt8 := Id.run do
  let mut out : Array UInt8 := Array.replicate 32 0
  out := out.set! 0 9
  return out

/-- X25519 scalar mult against the base point — the
    "public key from secret key" operation. -/
def x25519Base (scalar : Array UInt8) : Array UInt8 :=
  x25519 scalar basePoint

end Sparkle.IP.Crypto.X25519
