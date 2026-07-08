/-
  IP.Bus.CRSFHW — TBS Crossfire HW building blocks.

  Implements the CRC-8 (polynomial 0xD5) LFSR as a Sparkle
  `circuit do` module.  Each cycle that `valid` is high, the
  LFSR consumes one input byte (bit-serial internally,
  materialised here as an 8-bit XOR-shift step) and updates
  the 8-bit CRC register.

  Wiring:
      start / reset  → bring crcR to 0 on next cycle
      byteIn         → one input byte (payload byte)
      valid          → 1 when byteIn should be consumed
      crcOut         → current 8-bit CRC register

  Validation: cycle-by-cycle equivalence to `IP.Bus.CRSF.crc8`
  on small byte lists.
-/
import Sparkle

namespace Sparkle.IP.Bus.CRSFHW

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-- Output of the CRC-8 HW unit. -/
structure CRC8Out (dom : DomainConfig) where
  /-- 8-bit CRC register, sampled on each cycle. -/
  crc : Signal dom (BitVec 8)

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (CRC8Out dom) dom := ⟨⟩

/-- One bit-serial step of the CRC-8 unroll.  Given current
    CRC candidate `c`, produces the next.

      if (c & 0x80) ≠ 0 then (c << 1) XOR 0xD5
      else                   (c << 1) -/
def crc8Step {dom : DomainConfig} (c : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  let p0    := (Signal.pure 0#8    : Signal dom (BitVec 8))
  let pPoly := (Signal.pure 0xD5#8 : Signal dom (BitVec 8))
  let p1    := (Signal.pure 1#8    : Signal dom (BitVec 8))
  let pMSB  := (Signal.pure 0x80#8 : Signal dom (BitVec 8))
  let msbAnd := (c &&& pMSB : Signal dom (BitVec 8))
  let msbNZ := (~~~(msbAnd === p0 : Signal dom Bool)
                : Signal dom Bool)
  let shifted := (c <<< p1 : Signal dom (BitVec 8))
  let shiftedXor := (shifted ^^^ pPoly : Signal dom (BitVec 8))
  Signal.mux msbNZ shiftedXor shifted

/-- Byte-serial CRC-8 poly 0xD5 (CRSF).  Per byte:
      c := crc XOR byte
      repeat 8 times:
        if (c & 0x80) ≠ 0 then c := (c << 1) XOR 0xD5
        else                   c := (c << 1)
      crc := c

    Building this as a combinational round-per-cycle would take
    8 sub-cycles per byte.  Since Sparkle's `circuit do` is
    single-cycle-per-statement, we unroll the 8 shift steps
    combinationally with a chain of muxes: at every step we
    inspect the current MSB and choose whether to XOR the
    polynomial after shifting. -/
def crc8HW {dom : DomainConfig}
    (start : Signal dom Bool)
    (byteIn : Signal dom (BitVec 8))
    (valid : Signal dom Bool) :
    CRC8Out dom :=
  circuit do
    let crcR ← Signal.reg (0#8)
    let crcSig := (crcR : Signal dom (BitVec 8))

    let p0    := (Signal.pure 0#8    : Signal dom (BitVec 8))

    let c0 := (crcSig ^^^ byteIn : Signal dom (BitVec 8))
    let c1 := crc8Step c0
    let c2 := crc8Step c1
    let c3 := crc8Step c2
    let c4 := crc8Step c3
    let c5 := crc8Step c4
    let c6 := crc8Step c5
    let c7 := crc8Step c6
    let c8 := crc8Step c7

    crcR <~ Signal.mux start p0 (Signal.mux valid c8 crcSig)

    return ({ crc := crcSig } : CRC8Out dom)

end Sparkle.IP.Bus.CRSFHW
