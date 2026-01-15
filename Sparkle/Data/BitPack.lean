/-
  BitPack: Type class for packing/unpacking values to/from bit vectors

  This proves that a type can be represented in hardware by converting
  to and from a fixed-width bit vector.
-/

namespace Sparkle.Data.BitPack

/--
  BitPack type class: Proves a type α can be converted to/from a BitVec of width n.

  This is essential for hardware synthesis, as all values must ultimately
  be representable as bit patterns.

  Laws (not enforced, but expected):
  - toBitVec (fromBitVec bv) = bv (round-trip property)
  - fromBitVec (toBitVec x) = x (round-trip property)
-/
class BitPack (α : Type u) (n : Nat) where
  toBitVec : α → BitVec n
  fromBitVec : BitVec n → α

namespace BitPack

variable {α : Type u} {n : Nat}

/-- Convert a value to its bit vector representation -/
@[inline]
def pack [BitPack α n] (x : α) : BitVec n :=
  BitPack.toBitVec x

/-- Convert a bit vector to its value representation -/
@[inline]
def unpack [BitPack α n] (bv : BitVec n) : α :=
  BitPack.fromBitVec bv

end BitPack

-- Instances for standard types

/-- BitPack instance for Bool (1 bit) -/
instance : BitPack Bool 1 where
  toBitVec b := if b then 1#1 else 0#1
  fromBitVec bv := bv != 0#1

/-- BitPack instance for BitVec n (identity mapping) -/
instance {n : Nat} : BitPack (BitVec n) n where
  toBitVec bv := bv
  fromBitVec bv := bv

/-- BitPack instance for Unit (0 bits) -/
instance : BitPack Unit 0 where
  toBitVec _ := 0#0
  fromBitVec _ := ()

/-- BitPack instance for UInt8 (8 bits) -/
instance : BitPack UInt8 8 where
  toBitVec n := BitVec.ofNat 8 n.toNat
  fromBitVec bv := UInt8.ofNat bv.toNat

/-- BitPack instance for UInt16 (16 bits) -/
instance : BitPack UInt16 16 where
  toBitVec n := BitVec.ofNat 16 n.toNat
  fromBitVec bv := UInt16.ofNat bv.toNat

/-- BitPack instance for UInt32 (32 bits) -/
instance : BitPack UInt32 32 where
  toBitVec n := BitVec.ofNat 32 n.toNat
  fromBitVec bv := UInt32.ofNat bv.toNat

/-- BitPack instance for UInt64 (64 bits) -/
instance : BitPack UInt64 64 where
  toBitVec n := BitVec.ofNat 64 n.toNat
  fromBitVec bv := UInt64.ofNat bv.toNat

/-- BitPack instance for pairs (concatenate bit vectors) -/
instance {α β : Type u} {n m : Nat} [BitPack α n] [BitPack β m] :
    BitPack (α × β) (n + m) where
  toBitVec pair :=
    let bvA := BitPack.toBitVec pair.1
    let bvB := BitPack.toBitVec pair.2
    -- Concatenate: A is in upper bits, B in lower bits
    bvA ++ bvB
  fromBitVec bv :=
    -- Split: upper n bits for A, lower m bits for B
    let bvA := BitVec.extractLsb' 0 n bv
    let bvB := BitVec.extractLsb' n m bv
    (BitPack.fromBitVec bvA, BitPack.fromBitVec bvB)

/-- Helper to get the bit width of a type with BitPack instance -/
def bitWidth (α : Type u) (n : Nat) [BitPack α n] : Nat := n

/-- Test if a value round-trips correctly through BitPack -/
def testRoundTrip {α : Type u} {n : Nat} [BitPack α n] [BEq α] (x : α) : Bool :=
  let bv : BitVec n := BitPack.toBitVec x
  let x' : α := BitPack.fromBitVec bv
  x == x'

/-- Example: RGB structure for demonstration -/
structure RGB where
  r : BitVec 8
  g : BitVec 8
  b : BitVec 8
  deriving Repr, BEq

/-- BitPack instance for RGB (24 bits total) -/
instance : BitPack RGB 24 where
  toBitVec rgb := rgb.r ++ rgb.g ++ rgb.b
  fromBitVec bv :=
    let r := BitVec.extractLsb' 0 8 bv
    let g := BitVec.extractLsb' 8 8 bv
    let b := BitVec.extractLsb' 16 8 bv
    { r := r, g := g, b := b }

/-- Example RGB value -/
def exampleRGB : RGB := { r := 0xFF#8, g := 0x80#8, b := 0x00#8 }

end Sparkle.Data.BitPack
