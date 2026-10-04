/-
  IP.Bus.CANHW — CAN MAC HW building blocks (Sparkle Signal DSL).

  Implements the CRC-15 LFSR (the trickiest HW-specific piece
  of a CAN MAC) as a `circuit do` module.  Each cycle that
  `valid` is high, the LFSR consumes one bit and updates its
  15-bit state per the Bosch CAN-2.0B polynomial 0x4599.

  Wiring:
      reset / start  → bring crcR to 0 on next cycle
      bitIn          → one input bit (the next message bit)
      valid          → 1 when bitIn should be consumed
      crcOut         → current 15-bit CRC register

  Validation: cycle-by-cycle equivalence to
  `IP.Bus.CAN.crc15` on small bit lists (Compiler C2 ⇒
  Signal.val k cycle cost is now O(k), so this is feasible).
-/
import Sparkle

namespace Sparkle.IP.Bus.CANHW

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-- Output of the CRC-15 HW unit. -/
structure CRC15Out (dom : DomainConfig) where
  /-- 15-bit CRC register, sampled on each cycle. -/
  crc : Signal dom (BitVec 15)

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (CRC15Out dom) dom := ⟨⟩

/-- CRC-15 LFSR (Bosch CAN poly 0x4599) as a Sparkle HW
    module.  Per CAN spec:
      crc_bit15 = (crc >> 14) & 1
      xor_bit   = crc_bit15 XOR input_bit
      shifted   = (crc << 1) & 0x7FFF
      crc_next  = if xor_bit then shifted XOR 0x4599 else shifted

    `start` is a one-cycle pulse that resets the register to 0
    (asynchronous start of a new frame).  `valid` is high on
    cycles where `bitIn` should be consumed; on `!valid` the
    register holds. -/
def crc15HW {dom : DomainConfig}
    (start : Signal dom Bool)
    (bitIn : Signal dom Bool)
    (valid : Signal dom Bool) :
    CRC15Out dom :=
  circuit do
    let crcR ← Signal.reg (0#15)
    let crcSig := (crcR : Signal dom (BitVec 15))

    -- Constants.
    let p0 := (Signal.pure 0#15 : Signal dom (BitVec 15))
    let pPoly := (Signal.pure 0x4599#15 : Signal dom (BitVec 15))
    let p1c := (Signal.pure 1#15 : Signal dom (BitVec 15))
    let pMask := (Signal.pure 0x4000#15 : Signal dom (BitVec 15))   -- bit 14

    -- crcBit14 = (crc >>> 14) & 1, derived via AND with the
    -- top-bit mask then comparing to 0.
    let topAnd := (crcSig &&& pMask : Signal dom (BitVec 15))
    let topIsZero := (topAnd === p0 : Signal dom Bool)
    let topBit := (~~~topIsZero : Signal dom Bool)

    -- xorBit = topBit XOR bitIn  (use Bool ^^ as bitwise XOR)
    let xorBit := ((· ^^ ·) <$> topBit <*> bitIn : Signal dom Bool)

    -- shifted = (crc <<< 1)  (mask to 15 bits is implicit
    --   in BitVec 15 arithmetic).
    let shifted := (crcSig <<< p1c : Signal dom (BitVec 15))
    -- shifted XOR poly  vs. shifted
    let shiftedXor := (shifted ^^^ pPoly : Signal dom (BitVec 15))
    let crcNextWhenValid := Signal.mux xorBit shiftedXor shifted

    -- Update logic:
    --   start  → 0
    --   valid  → crcNextWhenValid
    --   else   → hold
    crcR <~ Signal.mux start p0 (Signal.mux valid crcNextWhenValid crcSig)

    return ({ crc := crcSig } : CRC15Out dom)

end Sparkle.IP.Bus.CANHW
