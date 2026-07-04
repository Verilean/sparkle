/-
  IP.Crypto.Keccak256 — Ethereum-style Keccak-256.

  This is the **Ethereum** Keccak-256, the one used by every
  EVM hash primitive (`keccak256(...)`, transaction hashing,
  contract addresses, ERC-20 event topics, EIP-712, etc.).

  NOTE: This is NOT NIST SHA3-256.  Both are built on the same
  Keccak-f[1600] permutation and the same 1088/512 sponge
  parameters, but they differ in the domain-separator byte
  appended at the end of the absorbed message:

    * Keccak-256 (Ethereum)  : 0x01
    * SHA3-256   (FIPS 202)  : 0x06

  Everything else (state, permutation, round constants, rotation
  offsets, padding shape) is identical.  Treat the two as
  separate functions — they produce different digests.

  Layout (per Keccak Reference v3.0 §1.2):
    * State: 5 × 5 array of 64-bit lanes (1600 bits total).
    * Permutation: 24 rounds, each applying θ → ρ → π → χ → ι.
    * Sponge:
        - rate   r = 1088 bits  (= 136 bytes)
        - capac. c =  512 bits
        - output d =  256 bits (truncated from the squeezed
                       state's first r bits)
    * Absorb: XOR message blocks of r bits into the first r
              bits of state, then permute.
    * Pad:    multi-rate padding — append delimiter byte
              (0x01 for Keccak, 0x06 for SHA3) then zero-pad
              then set the high bit of the last byte.

  The pure-data form here is what every higher-level Ethereum
  primitive in this IP tree calls: transaction RLP-then-hash,
  contract-address derivation (`keccak(rlp([sender, nonce]))`),
  ERC-20 ABI selector (first 4 bytes of `keccak(signature)`),
  etc.  A Signal-domain HW engine (24-cycle iterative
  permutation) will follow in the eth-wallet HW phase; this
  spec is what it cross-checks against.
-/

import Sparkle

namespace Sparkle.IP.Crypto.Keccak256

/-! ### State: 5 × 5 lanes of 64 bits.

    Indexed as `state[x + 5*y]` for x,y ∈ {0..4}.  This matches
    the lane-major flattening used by every reference Keccak
    implementation and keeps the round constants / rotation
    table 1:1 with the spec. -/

abbrev State := Array (BitVec 64)

def State.empty : State := Array.replicate 25 0#64

@[inline] def State.get (s : State) (x y : Nat) : BitVec 64 :=
  s.getD (x + 5 * y) 0#64

@[inline] def State.set (s : State) (x y : Nat) (v : BitVec 64) : State :=
  s.set! (x + 5 * y) v

/-! ### Round constants (Keccak-f[1600] §3.2.5). -/

def rc : Array (BitVec 64) := #[
  0x0000000000000001#64, 0x0000000000008082#64, 0x800000000000808a#64,
  0x8000000080008000#64, 0x000000000000808b#64, 0x0000000080000001#64,
  0x8000000080008081#64, 0x8000000000008009#64, 0x000000000000008a#64,
  0x0000000000000088#64, 0x0000000080008009#64, 0x000000008000000a#64,
  0x000000008000808b#64, 0x800000000000008b#64, 0x8000000000008089#64,
  0x8000000000008003#64, 0x8000000000008002#64, 0x8000000000000080#64,
  0x000000000000800a#64, 0x800000008000000a#64, 0x8000000080008081#64,
  0x8000000000008080#64, 0x0000000080000001#64, 0x8000000080008008#64
]

/-! ### Rotation offsets r(x,y) (Keccak Reference §1.4.4).

    `rotOffsets[x + 5*y]` is the left-rotation count applied to
    lane (x,y) during the ρ step.  Generated from the spec's
    standard table; the constants are immutable. -/

def rotOffsets : Array Nat := #[
   0,  1, 62, 28, 27,    -- y=0
  36, 44,  6, 55, 20,    -- y=1
   3, 10, 43, 25, 39,    -- y=2
  41, 45, 15, 21,  8,    -- y=3
  18,  2, 61, 56, 14     -- y=4
]

@[inline] def rotL64 (x : BitVec 64) (n : Nat) : BitVec 64 :=
  let n := n % 64
  if n == 0 then x
  else (x <<< (BitVec.ofNat 64 n)) ||| (x >>> (BitVec.ofNat 64 (64 - n)))

/-! ### Round function: θ → ρ → π → χ → ι. -/

/-- θ: column parity diffusion. -/
def stepTheta (s : State) : State := Id.run do
  let mut c : Array (BitVec 64) := Array.replicate 5 0#64
  for x in [:5] do
    let v := s.get x 0 ^^^ s.get x 1 ^^^ s.get x 2 ^^^ s.get x 3 ^^^ s.get x 4
    c := c.set! x v
  let mut d : Array (BitVec 64) := Array.replicate 5 0#64
  for x in [:5] do
    let xm1 := (x + 4) % 5
    let xp1 := (x + 1) % 5
    d := d.set! x ((c.getD xm1 0#64) ^^^ rotL64 (c.getD xp1 0#64) 1)
  let mut s' := s
  for y in [:5] do
    for x in [:5] do
      s' := s'.set x y (s'.get x y ^^^ d.getD x 0#64)
  return s'

/-- ρ: per-lane left rotation by `rotOffsets[x + 5*y]`. -/
def stepRho (s : State) : State := Id.run do
  let mut s' := s
  for y in [:5] do
    for x in [:5] do
      let r := rotOffsets.getD (x + 5 * y) 0
      s' := s'.set x y (rotL64 (s.get x y) r)
  return s'

/-- π: lane permutation (x', y') ← (y, (2x + 3y) mod 5). -/
def stepPi (s : State) : State := Id.run do
  let mut s' := State.empty
  for y in [:5] do
    for x in [:5] do
      let xNew := y
      let yNew := (2 * x + 3 * y) % 5
      s' := s'.set xNew yNew (s.get x y)
  return s'

/-- χ: row-wise non-linear step: A'[x,y] = A[x,y] ⊕ (¬A[x+1,y] ∧ A[x+2,y]). -/
def stepChi (s : State) : State := Id.run do
  let mut s' := s
  for y in [:5] do
    -- Snapshot the row first so the updates inside the row
    -- don't feed back into the same-row computation.
    let r0 := s.get 0 y
    let r1 := s.get 1 y
    let r2 := s.get 2 y
    let r3 := s.get 3 y
    let r4 := s.get 4 y
    s' := s'.set 0 y (r0 ^^^ ((~~~ r1) &&& r2))
    s' := s'.set 1 y (r1 ^^^ ((~~~ r2) &&& r3))
    s' := s'.set 2 y (r2 ^^^ ((~~~ r3) &&& r4))
    s' := s'.set 3 y (r3 ^^^ ((~~~ r4) &&& r0))
    s' := s'.set 4 y (r4 ^^^ ((~~~ r0) &&& r1))
  return s'

/-- ι: XOR round constant into lane (0,0). -/
def stepIota (s : State) (roundIdx : Nat) : State :=
  s.set 0 0 (s.get 0 0 ^^^ rc.getD roundIdx 0#64)

/-- One full Keccak-f[1600] round. -/
def keccakRound (s : State) (roundIdx : Nat) : State :=
  stepIota (stepChi (stepPi (stepRho (stepTheta s)))) roundIdx

/-- The 24-round Keccak-f[1600] permutation. -/
def keccakF (s : State) : State := Id.run do
  let mut s' := s
  for r in [:24] do
    s' := keccakRound s' r
  return s'

/-! ### Sponge construction (rate 1088 / capacity 512). -/

/-- Rate in bytes for Keccak-256 (1088 bits = 136 bytes). -/
def rateBytes : Nat := 136

/-- Convert little-endian 8 bytes to a 64-bit lane (Keccak's
    lane endianness is LE — byte 0 is the low byte). -/
def bytesToLane (bs : Array UInt8) (offset : Nat) : BitVec 64 := Id.run do
  let mut acc : BitVec 64 := 0#64
  for i in [:8] do
    let b := bs.getD (offset + i) 0
    acc := acc ||| ((BitVec.ofNat 64 b.toNat) <<< (BitVec.ofNat 64 (i * 8)))
  return acc

/-- Inverse: serialize a lane to 8 LE bytes. -/
def laneToBytes (v : BitVec 64) : Array UInt8 := Id.run do
  let mut out : Array UInt8 := #[]
  for i in [:8] do
    let byte := (v >>> (BitVec.ofNat 64 (i * 8))) &&& 0xFF#64
    out := out.push (UInt8.ofNat byte.toNat)
  return out

/-- Absorb one already-padded rate-sized block into the state. -/
def absorbBlock (s : State) (block : Array UInt8) : State := Id.run do
  let mut s' := s
  for laneIdx in [:rateBytes / 8] do
    let lane := bytesToLane block (laneIdx * 8)
    s' := s'.set! laneIdx ((s'.getD laneIdx 0#64) ^^^ lane)
  return keccakF s'

/-- Keccak multi-rate padding with the **Ethereum delimiter
    byte 0x01** (NOT the SHA3 byte 0x06).

    Produces a byte array whose length is a multiple of
    `rateBytes`.  The pad shape is:
      [...input bytes..., 0x01, 0x00, ..., 0x00, 0x80]
    with the final byte's 0x80 bit and the delimiter byte
    possibly being the same byte when the input fills the
    block to within one byte of the rate (in that case the
    delimiter becomes 0x81). -/
def padEthereum (input : Array UInt8) : Array UInt8 := Id.run do
  let mut padded := input
  let lastBlockLen := input.size % rateBytes
  let zerosNeeded := rateBytes - lastBlockLen - 1
  if zerosNeeded == 0 then
    -- Delimiter and final 0x80 share one byte.
    padded := padded.push 0x81
  else
    padded := padded.push 0x01
    for _ in [:zerosNeeded - 1] do
      padded := padded.push 0x00
    padded := padded.push 0x80
  return padded

/-- Pure-data Ethereum Keccak-256 of a byte array, returning
    a 32-byte digest. -/
def keccak256OfBytes (input : Array UInt8) : Array UInt8 := Id.run do
  let padded := padEthereum input
  let nBlocks := padded.size / rateBytes
  let mut state := State.empty
  for blockIdx in [:nBlocks] do
    let block := (padded.toList.drop (blockIdx * rateBytes)).take rateBytes |>.toArray
    state := absorbBlock state block
  -- Squeeze the first 256 bits = first 4 lanes = first 32 bytes.
  let mut out : Array UInt8 := #[]
  for laneIdx in [:4] do
    out := out ++ laneToBytes (state.getD laneIdx 0#64)
  return out

end Sparkle.IP.Crypto.Keccak256
