/-
  IP.Bus.MIL1553HW — MIL-STD-1553B HW building blocks.

  Two small pieces:

  1. `oddParityHW` — combinational: computes the odd-parity
     bit over a 16-bit content field.  Same math as
     `IP.Bus.MIL1553.oddParity` (returns true iff # of 1-bits
     in `content` is even, so total is odd).

  2. `manchesterEncoderHW` — bi-phase-L Manchester encoder.
     One bit consumed per two output half-cycles.  `bitIn`
     is the data bit to send; the two half-cycles emitted
     back-to-back are:
        bitIn = 0 → HIGH, LOW
        bitIn = 1 → LOW,  HIGH
     A `phase` register alternates (first, second) per cycle
     when `enable` is high.  The output `line` samples the
     encoded half-bit.

  Validation:
    * `oddParityHW` matches `IP.Bus.MIL1553.oddParity`.
    * `manchesterEncoderHW` on a known bit list produces the
      expected 2-bit-per-input half-cycle pattern.
-/
import Sparkle

namespace Sparkle.IP.Bus.MIL1553HW

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ### Odd parity. -/

structure ParityOut (dom : DomainConfig) where
  parity : Signal dom Bool

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (ParityOut dom) dom := ⟨⟩

/-- Combinational odd-parity generator over a 16-bit value.
    Returns `true` iff (# of set bits in `content`) is even,
    so that `content || parity` has an odd number of 1s. -/
def oddParityHW {dom : DomainConfig}
    (content : Signal dom (BitVec 16)) :
    ParityOut dom :=
  let m1 := (Signal.pure 1#16 : Signal dom (BitVec 16))
  -- Extract 16 individual bits via >>> i then AND 1.
  let bit0  := ((· &&& ·) <$> content <*> m1 : Signal dom (BitVec 16))
  let bit1  := ((· &&& ·) <$>
    ((· >>> ·) <$> content <*> (Signal.pure  1#16 : Signal dom (BitVec 16))) <*> m1
      : Signal dom (BitVec 16))
  let bit2  := ((· &&& ·) <$>
    ((· >>> ·) <$> content <*> (Signal.pure  2#16 : Signal dom (BitVec 16))) <*> m1
      : Signal dom (BitVec 16))
  let bit3  := ((· &&& ·) <$>
    ((· >>> ·) <$> content <*> (Signal.pure  3#16 : Signal dom (BitVec 16))) <*> m1
      : Signal dom (BitVec 16))
  let bit4  := ((· &&& ·) <$>
    ((· >>> ·) <$> content <*> (Signal.pure  4#16 : Signal dom (BitVec 16))) <*> m1
      : Signal dom (BitVec 16))
  let bit5  := ((· &&& ·) <$>
    ((· >>> ·) <$> content <*> (Signal.pure  5#16 : Signal dom (BitVec 16))) <*> m1
      : Signal dom (BitVec 16))
  let bit6  := ((· &&& ·) <$>
    ((· >>> ·) <$> content <*> (Signal.pure  6#16 : Signal dom (BitVec 16))) <*> m1
      : Signal dom (BitVec 16))
  let bit7  := ((· &&& ·) <$>
    ((· >>> ·) <$> content <*> (Signal.pure  7#16 : Signal dom (BitVec 16))) <*> m1
      : Signal dom (BitVec 16))
  let bit8  := ((· &&& ·) <$>
    ((· >>> ·) <$> content <*> (Signal.pure  8#16 : Signal dom (BitVec 16))) <*> m1
      : Signal dom (BitVec 16))
  let bit9  := ((· &&& ·) <$>
    ((· >>> ·) <$> content <*> (Signal.pure  9#16 : Signal dom (BitVec 16))) <*> m1
      : Signal dom (BitVec 16))
  let bit10 := ((· &&& ·) <$>
    ((· >>> ·) <$> content <*> (Signal.pure 10#16 : Signal dom (BitVec 16))) <*> m1
      : Signal dom (BitVec 16))
  let bit11 := ((· &&& ·) <$>
    ((· >>> ·) <$> content <*> (Signal.pure 11#16 : Signal dom (BitVec 16))) <*> m1
      : Signal dom (BitVec 16))
  let bit12 := ((· &&& ·) <$>
    ((· >>> ·) <$> content <*> (Signal.pure 12#16 : Signal dom (BitVec 16))) <*> m1
      : Signal dom (BitVec 16))
  let bit13 := ((· &&& ·) <$>
    ((· >>> ·) <$> content <*> (Signal.pure 13#16 : Signal dom (BitVec 16))) <*> m1
      : Signal dom (BitVec 16))
  let bit14 := ((· &&& ·) <$>
    ((· >>> ·) <$> content <*> (Signal.pure 14#16 : Signal dom (BitVec 16))) <*> m1
      : Signal dom (BitVec 16))
  let bit15 := ((· &&& ·) <$>
    ((· >>> ·) <$> content <*> (Signal.pure 15#16 : Signal dom (BitVec 16))) <*> m1
      : Signal dom (BitVec 16))
  -- XOR reduce (associativity doesn't matter for XOR).
  let x01  := ((· ^^^ ·) <$> bit0  <*> bit1  : Signal dom (BitVec 16))
  let x02  := ((· ^^^ ·) <$> x01   <*> bit2  : Signal dom (BitVec 16))
  let x03  := ((· ^^^ ·) <$> x02   <*> bit3  : Signal dom (BitVec 16))
  let x04  := ((· ^^^ ·) <$> x03   <*> bit4  : Signal dom (BitVec 16))
  let x05  := ((· ^^^ ·) <$> x04   <*> bit5  : Signal dom (BitVec 16))
  let x06  := ((· ^^^ ·) <$> x05   <*> bit6  : Signal dom (BitVec 16))
  let x07  := ((· ^^^ ·) <$> x06   <*> bit7  : Signal dom (BitVec 16))
  let x08  := ((· ^^^ ·) <$> x07   <*> bit8  : Signal dom (BitVec 16))
  let x09  := ((· ^^^ ·) <$> x08   <*> bit9  : Signal dom (BitVec 16))
  let x10  := ((· ^^^ ·) <$> x09   <*> bit10 : Signal dom (BitVec 16))
  let x11  := ((· ^^^ ·) <$> x10   <*> bit11 : Signal dom (BitVec 16))
  let x12  := ((· ^^^ ·) <$> x11   <*> bit12 : Signal dom (BitVec 16))
  let x13  := ((· ^^^ ·) <$> x12   <*> bit13 : Signal dom (BitVec 16))
  let x14  := ((· ^^^ ·) <$> x13   <*> bit14 : Signal dom (BitVec 16))
  let xAll := ((· ^^^ ·) <$> x14   <*> bit15 : Signal dom (BitVec 16))
  -- Odd parity bit: XOR-reduce = 0 ⇒ input has even # of 1s
  -- ⇒ we send parity=1.
  let isEven := ((· == ·) <$> xAll <*> (Signal.pure 0#16 : Signal dom (BitVec 16))
                : Signal dom Bool)
  { parity := isEven }

/-! ### Manchester bi-phase-L encoder. -/

structure ManOut (dom : DomainConfig) where
  /-- Encoded line level for the current half-bit. -/
  line : Signal dom Bool

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (ManOut dom) dom := ⟨⟩

/-- Bi-phase-L Manchester encoder.

    Inputs:
      bitIn  — data bit to encode
      enable — 1 when a new half-cycle should be produced
      start  — resets `phase` to 0 (first-half output)

    Output:
      line — the current half-bit level.  Bi-phase-L:
              bitIn = 0 → first half HIGH,  second half LOW
              bitIn = 1 → first half LOW,   second half HIGH
              (some references use the opposite convention;
               this module matches the "1553B: 1→high-to-low
               transition" convention.)

    Internal state:
      phase : Bool — alternates each cycle while `enable`;
                     0 = first half of this bit
                     1 = second half.

    The caller drives `bitIn` at the bit rate (holds it stable
    across the two half-cycles) and `enable` at 2× the bit
    rate. -/
def manchesterEncoderHW {dom : DomainConfig}
    (bitIn : Signal dom Bool)
    (enable : Signal dom Bool)
    (start : Signal dom Bool) :
    ManOut dom :=
  circuit do
    let phaseR ← Signal.reg false
    let phaseSig := (phaseR : Signal dom Bool)

    -- Toggle phase on enable, clear on start.
    let phaseFlipped := ((fun b => !b) <$> phaseSig : Signal dom Bool)
    let phaseAfterEn := Signal.mux enable phaseFlipped phaseSig
    let phaseNext := Signal.mux start (Signal.pure false) phaseAfterEn
    phaseR <~ phaseNext

    -- Line level:
    --   phase = 0 (first half):  line = !bitIn
    --   phase = 1 (second half): line = bitIn
    let notBit := ((fun b => !b) <$> bitIn : Signal dom Bool)
    let lineSig := Signal.mux phaseSig bitIn notBit
    return ({ line := lineSig } : ManOut dom)

end Sparkle.IP.Bus.MIL1553HW
