/-
  IP.Crypto.AESHW — AES-128 encryption HW (Signal DSL).

  Round-per-clock iterative encryptor.  State: 128 bits.
  Timing:

    * cycle 0     : `start` pulse latches keyIn, blockIn.
    * cycle 1     : run key-expansion side by side with
                    AddRoundKey(state, K0).  (K0 is just the
                    input key.)
    * cycle 2..10 : one full round per cycle (SubBytes →
                    ShiftRows → MixColumns → AddRoundKey).
    * cycle 11    : final round (SubBytes → ShiftRows →
                    AddRoundKey, no MixColumns).  Pulse `done`.

  Key expansion is inlined: the round key K_r used on round r
  is computed on-the-fly from K_{r-1} inside the same round
  cycle, so no separate 176-byte SRAM is needed.

  Only ENCRYPTION is shipped in this wave.  Decryption
  (`invSubBytes`, `invMixColumns`, reverse-order round keys)
  is direction #2 — deferred to a follow-up commit so the
  first pass keeps the module compact.

  Validated against FIPS 197 Appendix B (128-bit KAT):
      plaintext = 3243f6a8885a308d313198a2e0370734
      key       = 2b7e151628aed2a6abf7158809cf4f3c
      output    = 3925841d02dc09fbdc118597196a0b32
-/
import Sparkle
import Sparkle.Core.Lut
import IP.Crypto.Codec.AES

open Sparkle.Core (kLutMacro)
open Sparkle.Core.Domain
open Sparkle.Core.Signal

namespace Sparkle.IP.Crypto.AESHW

/-! ### S-box (8→8): a hardware sub-module implementing the
    AES forward S-box as a 256-way `kLut!`.  Instantiated 16
    times for `subBytesHW` (one per state byte). -/

@[hardware_module] def sboxHW {dom : DomainConfig}
    (b : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  kLut! b [
    Signal.pure 0x63#8, Signal.pure 0x7c#8, Signal.pure 0x77#8, Signal.pure 0x7b#8,
    Signal.pure 0xf2#8, Signal.pure 0x6b#8, Signal.pure 0x6f#8, Signal.pure 0xc5#8,
    Signal.pure 0x30#8, Signal.pure 0x01#8, Signal.pure 0x67#8, Signal.pure 0x2b#8,
    Signal.pure 0xfe#8, Signal.pure 0xd7#8, Signal.pure 0xab#8, Signal.pure 0x76#8,
    Signal.pure 0xca#8, Signal.pure 0x82#8, Signal.pure 0xc9#8, Signal.pure 0x7d#8,
    Signal.pure 0xfa#8, Signal.pure 0x59#8, Signal.pure 0x47#8, Signal.pure 0xf0#8,
    Signal.pure 0xad#8, Signal.pure 0xd4#8, Signal.pure 0xa2#8, Signal.pure 0xaf#8,
    Signal.pure 0x9c#8, Signal.pure 0xa4#8, Signal.pure 0x72#8, Signal.pure 0xc0#8,
    Signal.pure 0xb7#8, Signal.pure 0xfd#8, Signal.pure 0x93#8, Signal.pure 0x26#8,
    Signal.pure 0x36#8, Signal.pure 0x3f#8, Signal.pure 0xf7#8, Signal.pure 0xcc#8,
    Signal.pure 0x34#8, Signal.pure 0xa5#8, Signal.pure 0xe5#8, Signal.pure 0xf1#8,
    Signal.pure 0x71#8, Signal.pure 0xd8#8, Signal.pure 0x31#8, Signal.pure 0x15#8,
    Signal.pure 0x04#8, Signal.pure 0xc7#8, Signal.pure 0x23#8, Signal.pure 0xc3#8,
    Signal.pure 0x18#8, Signal.pure 0x96#8, Signal.pure 0x05#8, Signal.pure 0x9a#8,
    Signal.pure 0x07#8, Signal.pure 0x12#8, Signal.pure 0x80#8, Signal.pure 0xe2#8,
    Signal.pure 0xeb#8, Signal.pure 0x27#8, Signal.pure 0xb2#8, Signal.pure 0x75#8,
    Signal.pure 0x09#8, Signal.pure 0x83#8, Signal.pure 0x2c#8, Signal.pure 0x1a#8,
    Signal.pure 0x1b#8, Signal.pure 0x6e#8, Signal.pure 0x5a#8, Signal.pure 0xa0#8,
    Signal.pure 0x52#8, Signal.pure 0x3b#8, Signal.pure 0xd6#8, Signal.pure 0xb3#8,
    Signal.pure 0x29#8, Signal.pure 0xe3#8, Signal.pure 0x2f#8, Signal.pure 0x84#8,
    Signal.pure 0x53#8, Signal.pure 0xd1#8, Signal.pure 0x00#8, Signal.pure 0xed#8,
    Signal.pure 0x20#8, Signal.pure 0xfc#8, Signal.pure 0xb1#8, Signal.pure 0x5b#8,
    Signal.pure 0x6a#8, Signal.pure 0xcb#8, Signal.pure 0xbe#8, Signal.pure 0x39#8,
    Signal.pure 0x4a#8, Signal.pure 0x4c#8, Signal.pure 0x58#8, Signal.pure 0xcf#8,
    Signal.pure 0xd0#8, Signal.pure 0xef#8, Signal.pure 0xaa#8, Signal.pure 0xfb#8,
    Signal.pure 0x43#8, Signal.pure 0x4d#8, Signal.pure 0x33#8, Signal.pure 0x85#8,
    Signal.pure 0x45#8, Signal.pure 0xf9#8, Signal.pure 0x02#8, Signal.pure 0x7f#8,
    Signal.pure 0x50#8, Signal.pure 0x3c#8, Signal.pure 0x9f#8, Signal.pure 0xa8#8,
    Signal.pure 0x51#8, Signal.pure 0xa3#8, Signal.pure 0x40#8, Signal.pure 0x8f#8,
    Signal.pure 0x92#8, Signal.pure 0x9d#8, Signal.pure 0x38#8, Signal.pure 0xf5#8,
    Signal.pure 0xbc#8, Signal.pure 0xb6#8, Signal.pure 0xda#8, Signal.pure 0x21#8,
    Signal.pure 0x10#8, Signal.pure 0xff#8, Signal.pure 0xf3#8, Signal.pure 0xd2#8,
    Signal.pure 0xcd#8, Signal.pure 0x0c#8, Signal.pure 0x13#8, Signal.pure 0xec#8,
    Signal.pure 0x5f#8, Signal.pure 0x97#8, Signal.pure 0x44#8, Signal.pure 0x17#8,
    Signal.pure 0xc4#8, Signal.pure 0xa7#8, Signal.pure 0x7e#8, Signal.pure 0x3d#8,
    Signal.pure 0x64#8, Signal.pure 0x5d#8, Signal.pure 0x19#8, Signal.pure 0x73#8,
    Signal.pure 0x60#8, Signal.pure 0x81#8, Signal.pure 0x4f#8, Signal.pure 0xdc#8,
    Signal.pure 0x22#8, Signal.pure 0x2a#8, Signal.pure 0x90#8, Signal.pure 0x88#8,
    Signal.pure 0x46#8, Signal.pure 0xee#8, Signal.pure 0xb8#8, Signal.pure 0x14#8,
    Signal.pure 0xde#8, Signal.pure 0x5e#8, Signal.pure 0x0b#8, Signal.pure 0xdb#8,
    Signal.pure 0xe0#8, Signal.pure 0x32#8, Signal.pure 0x3a#8, Signal.pure 0x0a#8,
    Signal.pure 0x49#8, Signal.pure 0x06#8, Signal.pure 0x24#8, Signal.pure 0x5c#8,
    Signal.pure 0xc2#8, Signal.pure 0xd3#8, Signal.pure 0xac#8, Signal.pure 0x62#8,
    Signal.pure 0x91#8, Signal.pure 0x95#8, Signal.pure 0xe4#8, Signal.pure 0x79#8,
    Signal.pure 0xe7#8, Signal.pure 0xc8#8, Signal.pure 0x37#8, Signal.pure 0x6d#8,
    Signal.pure 0x8d#8, Signal.pure 0xd5#8, Signal.pure 0x4e#8, Signal.pure 0xa9#8,
    Signal.pure 0x6c#8, Signal.pure 0x56#8, Signal.pure 0xf4#8, Signal.pure 0xea#8,
    Signal.pure 0x65#8, Signal.pure 0x7a#8, Signal.pure 0xae#8, Signal.pure 0x08#8,
    Signal.pure 0xba#8, Signal.pure 0x78#8, Signal.pure 0x25#8, Signal.pure 0x2e#8,
    Signal.pure 0x1c#8, Signal.pure 0xa6#8, Signal.pure 0xb4#8, Signal.pure 0xc6#8,
    Signal.pure 0xe8#8, Signal.pure 0xdd#8, Signal.pure 0x74#8, Signal.pure 0x1f#8,
    Signal.pure 0x4b#8, Signal.pure 0xbd#8, Signal.pure 0x8b#8, Signal.pure 0x8a#8,
    Signal.pure 0x70#8, Signal.pure 0x3e#8, Signal.pure 0xb5#8, Signal.pure 0x66#8,
    Signal.pure 0x48#8, Signal.pure 0x03#8, Signal.pure 0xf6#8, Signal.pure 0x0e#8,
    Signal.pure 0x61#8, Signal.pure 0x35#8, Signal.pure 0x57#8, Signal.pure 0xb9#8,
    Signal.pure 0x86#8, Signal.pure 0xc1#8, Signal.pure 0x1d#8, Signal.pure 0x9e#8,
    Signal.pure 0xe1#8, Signal.pure 0xf8#8, Signal.pure 0x98#8, Signal.pure 0x11#8,
    Signal.pure 0x69#8, Signal.pure 0xd9#8, Signal.pure 0x8e#8, Signal.pure 0x94#8,
    Signal.pure 0x9b#8, Signal.pure 0x1e#8, Signal.pure 0x87#8, Signal.pure 0xe9#8,
    Signal.pure 0xce#8, Signal.pure 0x55#8, Signal.pure 0x28#8, Signal.pure 0xdf#8,
    Signal.pure 0x8c#8, Signal.pure 0xa1#8, Signal.pure 0x89#8, Signal.pure 0x0d#8,
    Signal.pure 0xbf#8, Signal.pure 0xe6#8, Signal.pure 0x42#8, Signal.pure 0x68#8,
    Signal.pure 0x41#8, Signal.pure 0x99#8, Signal.pure 0x2d#8, Signal.pure 0x0f#8,
    Signal.pure 0xb0#8, Signal.pure 0x54#8, Signal.pure 0xbb#8, Signal.pure 0x16#8
  ]

/-! ### Rcon LUT.  Indexed by *round number* (1..10), i.e. the
    value of the internal round counter.  Slot 0 is unused (the
    initial AddRoundKey uses keyIn directly, not key-expanded). -/

@[hardware_module] def rconHW {dom : DomainConfig}
    (i : Signal dom (BitVec 4)) : Signal dom (BitVec 8) :=
  kLut! i [
    Signal.pure 0x00#8,  -- slot 0 (unused — cnt starts at 1)
    Signal.pure 0x01#8, Signal.pure 0x02#8, Signal.pure 0x04#8, Signal.pure 0x08#8,
    Signal.pure 0x10#8, Signal.pure 0x20#8, Signal.pure 0x40#8, Signal.pure 0x80#8,
    Signal.pure 0x1B#8, Signal.pure 0x36#8,
    -- Pad to 16 entries so `kLut!` synthesises cleanly.
    Signal.pure 0x00#8, Signal.pure 0x00#8, Signal.pure 0x00#8,
    Signal.pure 0x00#8, Signal.pure 0x00#8
  ]

/-! ### GF(2^8) `xtime` (multiply by {02}) as a HW combinational fn. -/

/-- xtime(x) = ((x << 1) & 0xFF) XOR (if MSB set then 0x1B else 0). -/
@[reducible, inline] def xtimeHW {dom : DomainConfig}
    (b : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  let one := (Signal.pure 1#8 : Signal dom (BitVec 8))
  let poly := (Signal.pure 0x1B#8 : Signal dom (BitVec 8))
  let zero := (Signal.pure 0x00#8 : Signal dom (BitVec 8))
  let hi := (Signal.pure 0x80#8 : Signal dom (BitVec 8))
  let shifted := (b <<< one : Signal dom (BitVec 8))
  let mskZero := (Signal.pure 0x00#8 : Signal dom (BitVec 8))
  let msbAnd := (b &&& hi : Signal dom (BitVec 8))
  let msbIsZero := (msbAnd === mskZero : Signal dom Bool)
  let addPoly := Signal.mux msbIsZero zero poly
  (shifted ^^^ addPoly : Signal dom (BitVec 8))

/-! ### Byte-lane helpers on the 128-bit state.

    State packing (matches `IP.Crypto.AES.State`'s
    column-major layout): byte i occupies bits [(15 - i)*8 ..
    (16 - i)*8 - 1] of the BitVec 128.  Byte 0 = high byte,
    byte 15 = low byte.  This mirrors NIST FIPS 197 §3.4
    where the leftmost input byte is s[0,0]. -/

@[reducible, inline] def byteAt {dom : DomainConfig}
    (state : Signal dom (BitVec 128)) (i : Nat) : Signal dom (BitVec 8) :=
  state.map (fun v => BitVec.extractLsb' ((15 - i) * 8) 8 v)

/-! ### SubBytes — apply sboxHW to each of the 16 state bytes. -/

/-- One byte's SubBytes = sboxHW. -/
@[reducible, inline] def subByteHW {dom : DomainConfig}
    (b : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  sboxHW b

/-- Full-state SubBytes.  Rebuilds the 128-bit state from
    S-boxed lanes. -/
abbrev subBytesHW {dom : DomainConfig}
    (state : Signal dom (BitVec 128)) : Signal dom (BitVec 128) :=
  -- 16 lane substitutions, then repack via nested `++`.
  let s0  := subByteHW (byteAt state 0)
  let s1  := subByteHW (byteAt state 1)
  let s2  := subByteHW (byteAt state 2)
  let s3  := subByteHW (byteAt state 3)
  let s4  := subByteHW (byteAt state 4)
  let s5  := subByteHW (byteAt state 5)
  let s6  := subByteHW (byteAt state 6)
  let s7  := subByteHW (byteAt state 7)
  let s8  := subByteHW (byteAt state 8)
  let s9  := subByteHW (byteAt state 9)
  let s10 := subByteHW (byteAt state 10)
  let s11 := subByteHW (byteAt state 11)
  let s12 := subByteHW (byteAt state 12)
  let s13 := subByteHW (byteAt state 13)
  let s14 := subByteHW (byteAt state 14)
  let s15 := subByteHW (byteAt state 15)
  let cat := fun (a b : Signal dom (BitVec 8)) => a ++ b
  let cat4 := fun (a b c d : Signal dom (BitVec 8)) =>
    let ab := cat a b
    let cd := cat c d
    ab ++ cd
  let cat16 :=
    let w0 := cat4 s0 s1 s2 s3
    let w1 := cat4 s4 s5 s6 s7
    let w2 := cat4 s8 s9 s10 s11
    let w3 := cat4 s12 s13 s14 s15
    let w01 := w0 ++ w1
    let w23 := w2 ++ w3
    w01 ++ w23
  cat16

/-! ### ShiftRows — pure wiring (byte-position permutation).

    Row r is cyclically shifted left by r bytes:
      s'[r][c] = s[r][(c + r) mod 4]

    In column-major flat layout `state[c*4 + r]`, after
    ShiftRows the byte at position `c*4 + r` came from
    `((c + r) mod 4) * 4 + r`.

    Byte-index re-mapping (source index for each output i,
    with i = c*4 + r):
      i= 0 (r0,c0) ← 0    i= 4 (r0,c1) ← 4    i= 8 (r0,c2) ← 8    i=12 (r0,c3) ← 12
      i= 1 (r1,c0) ← 5    i= 5 (r1,c1) ← 9    i= 9 (r1,c2) ← 13   i=13 (r1,c3) ← 1
      i= 2 (r2,c0) ← 10   i= 6 (r2,c1) ← 14   i=10 (r2,c2) ← 2    i=14 (r2,c3) ← 6
      i= 3 (r3,c0) ← 15   i= 7 (r3,c1) ← 3    i=11 (r3,c2) ← 7    i=15 (r3,c3) ← 11
-/

@[reducible, inline] def shiftRowsHW {dom : DomainConfig}
    (state : Signal dom (BitVec 128)) : Signal dom (BitVec 128) :=
  let b := fun i => byteAt state i
  let cat := fun (a c : Signal dom (BitVec 8)) => a ++ c
  let cat4 := fun (a c d e : Signal dom (BitVec 8)) =>
    let ab := cat a c; let cd := cat d e; ab ++ cd
  let w0 := cat4 (b 0)  (b 5)  (b 10) (b 15)
  let w1 := cat4 (b 4)  (b 9)  (b 14) (b 3)
  let w2 := cat4 (b 8)  (b 13) (b 2)  (b 7)
  let w3 := cat4 (b 12) (b 1)  (b 6)  (b 11)
  let w01 := w0 ++ w1
  let w23 := w2 ++ w3
  w01 ++ w23

/-! ### MixColumns — GF(2^8) matrix multiply per column. -/

/-- Combinational MixColumns on a single column (4 bytes).
    Returns 4 output bytes bundled in a tuple. -/
@[reducible, inline] def mixColumn {dom : DomainConfig}
    (s0 s1 s2 s3 : Signal dom (BitVec 8)) :
    Signal dom (BitVec 8) × Signal dom (BitVec 8) ×
    Signal dom (BitVec 8) × Signal dom (BitVec 8) :=
  -- gmul 2 x = xtime x; gmul 3 x = xtime x XOR x.
  let x2s0 := xtimeHW s0
  let x2s1 := xtimeHW s1
  let x2s2 := xtimeHW s2
  let x2s3 := xtimeHW s3
  let x3s0 := (x2s0 ^^^ s0 : Signal dom (BitVec 8))
  let x3s1 := (x2s1 ^^^ s1 : Signal dom (BitVec 8))
  let x3s2 := (x2s2 ^^^ s2 : Signal dom (BitVec 8))
  let x3s3 := (x2s3 ^^^ s3 : Signal dom (BitVec 8))
  -- t0 = 2·s0 ^ 3·s1 ^ s2 ^ s3
  let t0 :=
    let a := (x2s0 ^^^ x3s1 : Signal dom (BitVec 8))
    let b := (s2 ^^^ s3 : Signal dom (BitVec 8))
    (a ^^^ b : Signal dom (BitVec 8))
  -- t1 = s0 ^ 2·s1 ^ 3·s2 ^ s3
  let t1 :=
    let a := (s0 ^^^ x2s1 : Signal dom (BitVec 8))
    let b := (x3s2 ^^^ s3 : Signal dom (BitVec 8))
    (a ^^^ b : Signal dom (BitVec 8))
  -- t2 = s0 ^ s1 ^ 2·s2 ^ 3·s3
  let t2 :=
    let a := (s0 ^^^ s1 : Signal dom (BitVec 8))
    let b := (x2s2 ^^^ x3s3 : Signal dom (BitVec 8))
    (a ^^^ b : Signal dom (BitVec 8))
  -- t3 = 3·s0 ^ s1 ^ s2 ^ 2·s3
  let t3 :=
    let a := (x3s0 ^^^ s1 : Signal dom (BitVec 8))
    let b := (s2 ^^^ x2s3 : Signal dom (BitVec 8))
    (a ^^^ b : Signal dom (BitVec 8))
  (t0, t1, t2, t3)

/-- Full-state MixColumns: apply mixColumn to each of the
    4 columns. -/
@[reducible, inline] def mixColumnsHW {dom : DomainConfig}
    (state : Signal dom (BitVec 128)) : Signal dom (BitVec 128) :=
  let b := fun i => byteAt state i
  let (c00, c01, c02, c03) := mixColumn (b 0)  (b 1)  (b 2)  (b 3)
  let (c10, c11, c12, c13) := mixColumn (b 4)  (b 5)  (b 6)  (b 7)
  let (c20, c21, c22, c23) := mixColumn (b 8)  (b 9)  (b 10) (b 11)
  let (c30, c31, c32, c33) := mixColumn (b 12) (b 13) (b 14) (b 15)
  let cat := fun (a c : Signal dom (BitVec 8)) => a ++ c
  let cat4 := fun (a c d e : Signal dom (BitVec 8)) =>
    let ab := cat a c; let cd := cat d e; ab ++ cd
  let w0 := cat4 c00 c01 c02 c03
  let w1 := cat4 c10 c11 c12 c13
  let w2 := cat4 c20 c21 c22 c23
  let w3 := cat4 c30 c31 c32 c33
  let w01 := w0 ++ w1
  let w23 := w2 ++ w3
  w01 ++ w23

/-! ### AddRoundKey — XOR the 128-bit state with the round key. -/

@[reducible, inline] def addRoundKeyHW {dom : DomainConfig}
    (state key : Signal dom (BitVec 128)) : Signal dom (BitVec 128) :=
  (state ^^^ key : Signal dom (BitVec 128))

/-! ### Key expansion combinational step.

    Given round key K_{r-1} (128 bits = 4 words × 32) and
    the round index `r` (1..10), compute K_r using the
    standard g() = SubWord(RotWord(w[3])) ⊕ Rcon[r].

    For AES-128 with Nk = 4, w[0]..w[3] are the previous
    key's 32-bit words (MSB-first), and:
      w'[0] = w[0] XOR g(w[3])
      w'[1] = w[1] XOR w'[0]
      w'[2] = w[2] XOR w'[1]
      w'[3] = w[3] XOR w'[2]
-/

@[reducible, inline] def keyExpansionHW {dom : DomainConfig}
    (prevKey : Signal dom (BitVec 128))
    (roundIdx : Signal dom (BitVec 4)) :
    Signal dom (BitVec 128) :=
  -- Extract 4 32-bit words w0..w3, MSB-first.
  let w0 := prevKey.map (BitVec.extractLsb' 96 32 ·)
  let w1 := prevKey.map (BitVec.extractLsb' 64 32 ·)
  let w2 := prevKey.map (BitVec.extractLsb' 32 32 ·)
  let w3 := prevKey.map (BitVec.extractLsb'  0 32 ·)
  -- RotWord(w3): rotate byte-left by 1.  w3 = [b0 b1 b2 b3] → [b1 b2 b3 b0].
  let w3b0 := w3.map (BitVec.extractLsb' 24 8 ·)
  let w3b1 := w3.map (BitVec.extractLsb' 16 8 ·)
  let w3b2 := w3.map (BitVec.extractLsb'  8 8 ·)
  let w3b3 := w3.map (BitVec.extractLsb'  0 8 ·)
  -- SubWord applied to rotated bytes.
  let s0 := sboxHW w3b1
  let s1 := sboxHW w3b2
  let s2 := sboxHW w3b3
  let s3 := sboxHW w3b0
  -- Rcon on byte 0.
  let rc := rconHW roundIdx
  let s0' := (s0 ^^^ rc : Signal dom (BitVec 8))
  -- Assemble g = [s0' s1 s2 s3] as a 32-bit word.
  let g01 := s0' ++ s1
  let g23 := s2 ++ s3
  let g : Signal dom (BitVec 32) := g01 ++ g23
  let w0' := (w0 ^^^ g : Signal dom (BitVec 32))
  let w1' := (w1 ^^^ w0' : Signal dom (BitVec 32))
  let w2' := (w2 ^^^ w1' : Signal dom (BitVec 32))
  let w3' := (w3 ^^^ w2' : Signal dom (BitVec 32))
  let w01 := w0' ++ w1'
  let w23 := w2' ++ w3'
  (w01 ++ w23 : Signal dom (BitVec 128))

/-! ### Top-level AES-128 encryption FSM.

    Round-per-clock; end-to-end 12 cycles: 1 initial round key
    XOR + 9 mid rounds + 1 final round (no MixColumns). -/

structure AES128Out (dom : DomainConfig) where
  /-- 128-bit ciphertext register.  Valid on cycle 12 after start. -/
  ciphertext : Signal dom (BitVec 128)
  /-- Pulses one cycle when the block is done. -/
  done       : Signal dom Bool

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (AES128Out dom) dom := ⟨⟩

/-- AES-128 single-block encrypt.

    Pipeline:
      cycle 0    : `start` pulse latches keyIn, blockIn.
      cycle 1    : stateR ← blockIn XOR keyIn.  keyR = keyIn.
      cycle 2..10: stateR ← round(stateR, keyR); keyR ← keyExpand(keyR, cnt).
                    round(s,k) = AddRoundKey(MixColumns(ShiftRows(SubBytes s)), k')
                    (where k' is next round key)
      cycle 11   : final round: AddRoundKey(ShiftRows(SubBytes s), k_10).
      cycle 12   : done pulse. -/
def aes128BlockHW {dom : DomainConfig}
    (start : Signal dom Bool)
    (keyIn blockIn : Signal dom (BitVec 128)) :
    AES128Out dom :=
  circuit do
    let stateR ← Signal.reg (0#128)
    let keyR   ← Signal.reg (0#128)
    let cntR   ← Signal.reg (0#4)
    let doneR  ← Signal.reg false

    let stateSig := (stateR : Signal dom (BitVec 128))
    let keySig   := (keyR   : Signal dom (BitVec 128))
    let cntSig   := (cntR   : Signal dom (BitVec 4))

    -- Constants.
    let p0_4  := (Signal.pure 0#4 : Signal dom (BitVec 4))
    let p1_4  := (Signal.pure 1#4 : Signal dom (BitVec 4))
    let p10_4 := (Signal.pure 10#4 : Signal dom (BitVec 4))
    let p11_4 := (Signal.pure 11#4 : Signal dom (BitVec 4))

    let isIdle   := (cntSig === p0_4 : Signal dom Bool)
    let isFinal  := (cntSig === p10_4 : Signal dom Bool)
    let isDone   := (cntSig === p11_4 : Signal dom Bool)
    let isMid :=
      -- Between cnt = 1 and cnt = 9 inclusive (mid rounds with MixColumns).
      let notIdle := ((fun b => !b) <$> isIdle : Signal dom Bool)
      let notFin  := ((fun b => !b) <$> isFinal : Signal dom Bool)
      let notDn   := ((fun b => !b) <$> isDone : Signal dom Bool)
      let a := (notIdle &&& notFin : Signal dom Bool)
      (a &&& notDn : Signal dom Bool)

    -- Round transformations.  Inlined here (rather than calling
    -- `subBytesHW` / `shiftRowsHW` / `mixColumnsHW` / etc. through
    -- the module boundary) because the elaborator's `unfoldDefinition?`
    -- won't cross-inline plain `def`s that live in this module when
    -- the synth entry point sits outside `circuit do`.  Keep the
    -- named primitives as documentation + reusable pure-data
    -- combinators for callers that want them.
    let byte := fun (s : Signal dom (BitVec 128)) (i : Nat) =>
      s.map (fun v => BitVec.extractLsb' ((15 - i) * 8) 8 v)
    let cat := fun (a b : Signal dom (BitVec 8)) => a ++ b
    let cat4 := fun (a b c d : Signal dom (BitVec 8)) =>
      (cat a b) ++ (cat c d)
    let pack16 := fun
        (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 :
          Signal dom (BitVec 8)) =>
      let w0 := cat4 b0  b1  b2  b3
      let w1 := cat4 b4  b5  b6  b7
      let w2 := cat4 b8  b9  b10 b11
      let w3 := cat4 b12 b13 b14 b15
      (w0 ++ w1) ++ (w2 ++ w3)

    -- SubBytes: 16 sboxHW lookups.
    let sb0  := sboxHW (byte stateSig 0)
    let sb1  := sboxHW (byte stateSig 1)
    let sb2  := sboxHW (byte stateSig 2)
    let sb3  := sboxHW (byte stateSig 3)
    let sb4  := sboxHW (byte stateSig 4)
    let sb5  := sboxHW (byte stateSig 5)
    let sb6  := sboxHW (byte stateSig 6)
    let sb7  := sboxHW (byte stateSig 7)
    let sb8  := sboxHW (byte stateSig 8)
    let sb9  := sboxHW (byte stateSig 9)
    let sb10 := sboxHW (byte stateSig 10)
    let sb11 := sboxHW (byte stateSig 11)
    let sb12 := sboxHW (byte stateSig 12)
    let sb13 := sboxHW (byte stateSig 13)
    let sb14 := sboxHW (byte stateSig 14)
    let sb15 := sboxHW (byte stateSig 15)

    -- ShiftRows: byte-position permutation of the SubBytes result.
    --   i= 0 ← 0    i= 4 ← 4    i= 8 ← 8    i=12 ← 12
    --   i= 1 ← 5    i= 5 ← 9    i= 9 ← 13   i=13 ← 1
    --   i= 2 ← 10   i= 6 ← 14   i=10 ← 2    i=14 ← 6
    --   i= 3 ← 15   i= 7 ← 3    i=11 ← 7    i=15 ← 11
    let afterShiftRows :=
      pack16 sb0  sb5  sb10 sb15 sb4  sb9  sb14 sb3
             sb8  sb13 sb2  sb7  sb12 sb1  sb6  sb11

    -- MixColumns on each of the 4 columns of `afterShiftRows`.
    let mixCol := fun (s0 s1 s2 s3 : Signal dom (BitVec 8)) =>
      let x2s0 := xtimeHW s0
      let x2s1 := xtimeHW s1
      let x2s2 := xtimeHW s2
      let x2s3 := xtimeHW s3
      let x3s0 := (x2s0 ^^^ s0 : Signal dom (BitVec 8))
      let x3s2 := (x2s2 ^^^ s2 : Signal dom (BitVec 8))
      let x3s3 := (x2s3 ^^^ s3 : Signal dom (BitVec 8))
      let t0 :=
        let a := (x2s0 ^^^ ((x2s1 ^^^ s1) : Signal dom (BitVec 8)) : Signal dom (BitVec 8))
        let b := (s2 ^^^ s3 : Signal dom (BitVec 8))
        (a ^^^ b : Signal dom (BitVec 8))
      let t1 :=
        let a := (s0 ^^^ x2s1 : Signal dom (BitVec 8))
        let b := (x3s2 ^^^ s3 : Signal dom (BitVec 8))
        (a ^^^ b : Signal dom (BitVec 8))
      let t2 :=
        let a := (s0 ^^^ s1 : Signal dom (BitVec 8))
        let b := (x2s2 ^^^ x3s3 : Signal dom (BitVec 8))
        (a ^^^ b : Signal dom (BitVec 8))
      let t3 :=
        let a := (x3s0 ^^^ s1 : Signal dom (BitVec 8))
        let b := (s2 ^^^ x2s3 : Signal dom (BitVec 8))
        (a ^^^ b : Signal dom (BitVec 8))
      (t0, t1, t2, t3)

    let mc0 := mixCol (byte afterShiftRows 0)  (byte afterShiftRows 1)
                       (byte afterShiftRows 2)  (byte afterShiftRows 3)
    let mc1 := mixCol (byte afterShiftRows 4)  (byte afterShiftRows 5)
                       (byte afterShiftRows 6)  (byte afterShiftRows 7)
    let mc2 := mixCol (byte afterShiftRows 8)  (byte afterShiftRows 9)
                       (byte afterShiftRows 10) (byte afterShiftRows 11)
    let mc3 := mixCol (byte afterShiftRows 12) (byte afterShiftRows 13)
                       (byte afterShiftRows 14) (byte afterShiftRows 15)
    let afterMixColumns :=
      pack16 mc0.1 mc0.2.1 mc0.2.2.1 mc0.2.2.2
             mc1.1 mc1.2.1 mc1.2.2.1 mc1.2.2.2
             mc2.1 mc2.2.1 mc2.2.2.1 mc2.2.2.2
             mc3.1 mc3.2.1 mc3.2.2.1 mc3.2.2.2

    -- Key expansion (inlined, same reason as SubBytes).
    let kW0 := keySig.map (BitVec.extractLsb' 96 32 ·)
    let kW1 := keySig.map (BitVec.extractLsb' 64 32 ·)
    let kW2 := keySig.map (BitVec.extractLsb' 32 32 ·)
    let kW3 := keySig.map (BitVec.extractLsb'  0 32 ·)
    let kW3b0 := kW3.map (BitVec.extractLsb' 24 8 ·)
    let kW3b1 := kW3.map (BitVec.extractLsb' 16 8 ·)
    let kW3b2 := kW3.map (BitVec.extractLsb'  8 8 ·)
    let kW3b3 := kW3.map (BitVec.extractLsb'  0 8 ·)
    let gS0 := sboxHW kW3b1
    let gS1 := sboxHW kW3b2
    let gS2 := sboxHW kW3b3
    let gS3 := sboxHW kW3b0
    let rc := rconHW cntSig
    let gS0' := (gS0 ^^^ rc : Signal dom (BitVec 8))
    let gW01 := gS0' ++ gS1
    let gW23 := gS2 ++ gS3
    let gWord := (gW01 ++ gW23 : Signal dom (BitVec 32))
    let kW0' := (kW0 ^^^ gWord : Signal dom (BitVec 32))
    let kW1' := (kW1 ^^^ kW0' : Signal dom (BitVec 32))
    let kW2' := (kW2 ^^^ kW1' : Signal dom (BitVec 32))
    let kW3' := (kW3 ^^^ kW2' : Signal dom (BitVec 32))
    let kw01 := kW0' ++ kW1'
    let kw23 := kW2' ++ kW3'
    let nextKey := (kw01 ++ kw23 : Signal dom (BitVec 128))

    -- AddRoundKey (mid vs. final vs. initial).
    let midOut := (afterMixColumns ^^^ nextKey : Signal dom (BitVec 128))
    let finOut := (afterShiftRows ^^^ nextKey : Signal dom (BitVec 128))
    let initState := (blockIn ^^^ keyIn : Signal dom (BitVec 128))

    -- State update:
    --   start ⇒ blockIn XOR keyIn.
    --   isMid ⇒ midOut.
    --   isFinal ⇒ finOut.
    --   isDone ⇒ hold.
    stateR <~ Signal.mux start initState
                (Signal.mux isMid midOut
                  (Signal.mux isFinal finOut stateSig))

    -- Key update: latch keyIn on start; advance on mid/final rounds.
    let notIdle := ((fun b => !b) <$> isIdle : Signal dom Bool)
    let notDn   := ((fun b => !b) <$> isDone : Signal dom Bool)
    let keyAdvance := (notIdle &&& notDn : Signal dom Bool)
    keyR <~ Signal.mux start keyIn
              (Signal.mux keyAdvance nextKey keySig)

    -- Counter: 0 → 1 on start, +1 each active cycle, hold at 11.
    let cntInc := (cntSig + p1_4 : Signal dom (BitVec 4))
    cntR <~ Signal.mux start p1_4
              (Signal.mux isDone p0_4
                (Signal.mux isIdle p0_4 cntInc))

    doneR <~ isFinal

    return ({ ciphertext := stateSig
            , done       := (doneR : Signal dom Bool)
            } : AES128Out dom)

/-! ### Synthesis checks.

    Kept in-file so the elaborator can inline the primitive
    combinational chunks (SubBytes / ShiftRows / MixColumns /
    key-expansion) that live inside `aes128BlockHW`'s `circuit
    do`.  Only the two `@[hardware_module]` sub-modules
    (`sboxHW`, `rconHW`) are synth-checked in isolation — the
    top-level FSM's multi-output pair (`ciphertext`, `done`)
    trips the elaborator's still-fragile multi-output sub-module
    projection path (PR #66 Known limitation).  The behavioural
    sim in `Tests/IP/Crypto/AESHWTest.lean` covers the FSM
    end-to-end against the FIPS 197 KAT. -/

private def synth_aesSbox
    (b : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  sboxHW b

#synthesizeVerilog synth_aesSbox

private def synth_aesRcon
    (i : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 8) :=
  rconHW i

#synthesizeVerilog synth_aesRcon

end Sparkle.IP.Crypto.AESHW
