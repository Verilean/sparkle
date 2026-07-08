/-
  IP.Bus.LINHW — LIN 2.2A HW building blocks.

  Two small pieces:

  1. `pidParityHW` — combinational: computes the 2-bit PID
     parity nibble (P1 P0) for a 6-bit LIN ID.  Same math as
     `IP.Bus.LIN.pidParity`.

  2. `checksumHW` — running "sum with carry into next" (also
     called "one's-complement carry-add") accumulator with a
     final inversion.  Feed it a stream of bytes with `valid`
     high; the accumulator register plus the `chkOut` output
     (invert of accumulator) always reflects the checksum the
     way `IP.Bus.LIN.computeChecksum` would compute it over
     the same bytes.

     Selection of classic vs enhanced is a caller choice: for
     enhanced, present the PID byte as the first stream byte
     before the data bytes.  This HW module doesn't care.

  Validation: cycle-by-cycle equivalence to
  `IP.Bus.LIN.pidParity` (combinational) and to
  `IP.Bus.LIN.computeChecksum` fed the same byte sequence.
-/
import Sparkle

namespace Sparkle.IP.Bus.LINHW

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-- Output of the PID parity generator. -/
structure PidOut (dom : DomainConfig) where
  /-- 2-bit parity (bit 1 = P1, bit 0 = P0). -/
  parity : Signal dom (BitVec 2)

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (PidOut dom) dom := ⟨⟩

/-- Combinational PID parity generator.
    Input: 6-bit LIN ID.  Output: 2-bit parity.
      P0 = ID0 XOR ID1 XOR ID2 XOR ID4
      P1 = NOT (ID1 XOR ID3 XOR ID4 XOR ID5)

    Implemented with explicit Signal-level BitVec ops so the
    synthesizer sees pure combinational shift/AND/XOR.  Each
    bit is a BitVec 6 in {0,1}; the final packing extracts
    the low 2 bits. -/
def pidParityHW {dom : DomainConfig}
    (idIn : Signal dom (BitVec 6)) :
    PidOut dom :=
  let mask1 := (Signal.pure 1#6 : Signal dom (BitVec 6))
  -- Per-bit projections.
  let b0 := (idIn &&& mask1 : Signal dom (BitVec 6))
  let b1 :=
    ((· &&& ·) <$>
      (idIn >>> (Signal.pure 1#6 : Signal dom (BitVec 6)))
      <*> mask1 : Signal dom (BitVec 6))
  let b2 :=
    ((· &&& ·) <$>
      (idIn >>> (Signal.pure 2#6 : Signal dom (BitVec 6)))
      <*> mask1 : Signal dom (BitVec 6))
  let b3 :=
    ((· &&& ·) <$>
      (idIn >>> (Signal.pure 3#6 : Signal dom (BitVec 6)))
      <*> mask1 : Signal dom (BitVec 6))
  let b4 :=
    ((· &&& ·) <$>
      (idIn >>> (Signal.pure 4#6 : Signal dom (BitVec 6)))
      <*> mask1 : Signal dom (BitVec 6))
  let b5 :=
    ((· &&& ·) <$>
      (idIn >>> (Signal.pure 5#6 : Signal dom (BitVec 6)))
      <*> mask1 : Signal dom (BitVec 6))
  -- P0 = b0 XOR b1 XOR b2 XOR b4
  let p0a := (b0 ^^^ b1 : Signal dom (BitVec 6))
  let p0b := (p0a ^^^ b2 : Signal dom (BitVec 6))
  let p0  := (p0b ^^^ b4 : Signal dom (BitVec 6))
  -- P1 = 1 XOR (b1 XOR b3 XOR b4 XOR b5)
  let x1 := (b1 ^^^ b3 : Signal dom (BitVec 6))
  let x2 := (x1 ^^^ b4 : Signal dom (BitVec 6))
  let x3 := (x2 ^^^ b5 : Signal dom (BitVec 6))
  let p1 := (x3 ^^^ mask1 : Signal dom (BitVec 6))
  -- Combine: (p1 << 1) | p0, then narrow to BitVec 2.
  let p1s := (p1 <<< mask1 : Signal dom (BitVec 6))
  let combined := (p1s ||| p0 : Signal dom (BitVec 6))
  let narrowed := combined.map (BitVec.extractLsb' 0 2 ·)
  { parity := narrowed }

/-- Output of the LIN checksum accumulator. -/
structure ChkOut (dom : DomainConfig) where
  /-- Current running "sum with carry" accumulator. -/
  acc  : Signal dom (BitVec 8)
  /-- Final on-wire checksum byte (= NOT acc). -/
  chk  : Signal dom (BitVec 8)

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (ChkOut dom) dom := ⟨⟩

/-- Byte-serial LIN checksum accumulator with "sum + carry
    into next" arithmetic.

    Wire semantics:
      s = acc + byteIn (9-bit)
      acc_next = if s ≥ 0x100 then (s + 1) & 0xFF else s

    On `start` the accumulator resets to 0.  On `valid` a
    byte is folded in.  `chk` is the final one's-complement
    of the accumulator, ready for wire transmission. -/
def checksumHW {dom : DomainConfig}
    (start : Signal dom Bool)
    (byteIn : Signal dom (BitVec 8))
    (valid : Signal dom Bool) :
    ChkOut dom :=
  circuit do
    let accR ← Signal.reg (0#8)
    let accSig := (accR : Signal dom (BitVec 8))

    let p0    := (Signal.pure 0#8    : Signal dom (BitVec 8))
    let pFF   := (Signal.pure 0xFF#8 : Signal dom (BitVec 8))
    let p1    := (Signal.pure 1#8    : Signal dom (BitVec 8))

    -- 9-bit sum: widen both to BitVec 9 by (0#1 ++ ·).
    let zeroBit := (Signal.pure 0#1 : Signal dom (BitVec 1))
    let accW := (zeroBit ++ accSig : Signal dom (BitVec 9))
    let byteW := (zeroBit ++ byteIn : Signal dom (BitVec 9))
    let sumW := (accW + byteW : Signal dom (BitVec 9))

    -- Detect carry: top bit of the 9-bit sum.
    let p1_9 := (Signal.pure 1#9 : Signal dom (BitVec 9))
    let p8_9 := (Signal.pure 8#9 : Signal dom (BitVec 9))
    let carryShift := (sumW >>> p8_9 : Signal dom (BitVec 9))
    let carryMasked := (carryShift &&& p1_9 : Signal dom (BitVec 9))
    let p0_9 := (Signal.pure 0#9 : Signal dom (BitVec 9))
    let isCarryZero := (carryMasked === p0_9 : Signal dom Bool)
    let carry := ((fun b => !b) <$> isCarryZero : Signal dom Bool)

    -- Truncate low 8 bits via extractLsb'.
    let sumLo := sumW.map (BitVec.extractLsb' 0 8 ·)
    let sumLoP1 := (sumLo + p1 : Signal dom (BitVec 8))
    let folded := Signal.mux carry sumLoP1 sumLo

    -- Update: start → 0; valid → folded; else hold.
    accR <~ Signal.mux start p0 (Signal.mux valid folded accSig)

    -- Final checksum = NOT acc = 0xFF XOR acc.
    let chkSig := (accSig ^^^ pFF : Signal dom (BitVec 8))
    return ({ acc := accSig, chk := chkSig } : ChkOut dom)

end Sparkle.IP.Bus.LINHW
