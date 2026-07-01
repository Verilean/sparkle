/-
  IP.Bus.SBUSHW — Futaba S.BUS HW building blocks.

  S.BUS frames are 25 bytes long, header 0x0F, footer 0x00.
  This module implements a **byte-serial frame accumulator**:
  it consumes one incoming byte per cycle (already de-UARTed)
  and tracks the byte index within the frame, plus a
  `frameValid` flag that pulses on the cycle we've just seen
  byte 24 (footer) with the expected footer value AND byte 0
  saw the expected header.

  Additionally exposes an 11-bit channel-0 output — the low
  11 bits of the concatenation (byte1 || byte2 << 8) that
  the S.BUS packChannels function assigns to channel 0.

  Wiring:
      start   : reset byte counter to 0 (external framing tick)
      byteIn  : one payload byte per cycle
      valid   : byteIn is meaningful this cycle
      idxOut  : 0..24 (BitVec 5) — current byte position
      headerOk: pulse when byte 0 = 0x0F was seen
      footerOk: pulse when byte 24 = 0x00 was seen AND byte 0
                was 0x0F
      ch0     : 11-bit sample of channel 0 (updated on byte 2)

  Validation: feed a hand-built 25-byte frame and check that
  `footerOk` pulses on cycle 25 (after byte 24), and
  `ch0.val` equals the pure-data
  `IP.Bus.SBUS.unpackChannels` result at cycle 3 (after
  bytes 1 and 2 have been latched).
-/
import Sparkle

namespace Sparkle.IP.Bus.SBUSHW

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-- Output of the S.BUS frame accumulator. -/
structure FrameOut (dom : DomainConfig) where
  idxOut   : Signal dom (BitVec 5)
  headerOk : Signal dom Bool
  footerOk : Signal dom Bool
  ch0      : Signal dom (BitVec 11)

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (FrameOut dom) dom := ⟨⟩

/-- S.BUS frame byte accumulator.  Byte 0 must be 0x0F,
    byte 24 must be 0x00.  Channels are packed 11 bits each
    across bytes 1..22 (LSB first).  We expose only channel 0
    for a lean HW footprint. -/
def frameAccumulatorHW {dom : DomainConfig}
    (start : Signal dom Bool)
    (byteIn : Signal dom (BitVec 8))
    (valid : Signal dom Bool) :
    FrameOut dom :=
  circuit do
    let idxR   ← Signal.reg (0#5)
    let hdrR   ← Signal.reg false
    -- Store byte1 and byte2 so we can assemble channel 0 (11 bits).
    let b1R    ← Signal.reg (0#8)
    let b2R    ← Signal.reg (0#8)

    let idxSig := (idxR : Signal dom (BitVec 5))
    let hdrSig := (hdrR : Signal dom Bool)
    let b1Sig  := (b1R  : Signal dom (BitVec 8))
    let b2Sig  := (b2R  : Signal dom (BitVec 8))

    let p1_5  := (Signal.pure 1#5 : Signal dom (BitVec 5))
    let p0_5  := (Signal.pure 0#5 : Signal dom (BitVec 5))
    let p24_5 := (Signal.pure 24#5 : Signal dom (BitVec 5))
    let p1b_5 := (Signal.pure 1#5 : Signal dom (BitVec 5))
    let p2b_5 := (Signal.pure 2#5 : Signal dom (BitVec 5))

    let pHdr := (Signal.pure 0x0F#8 : Signal dom (BitVec 8))
    let pFtr := (Signal.pure 0x00#8 : Signal dom (BitVec 8))

    -- Position flags.
    let isIdx0 := ((· == ·) <$> idxSig <*> p0_5 : Signal dom Bool)
    let isIdx1 := ((· == ·) <$> idxSig <*> p1b_5 : Signal dom Bool)
    let isIdx2 := ((· == ·) <$> idxSig <*> p2b_5 : Signal dom Bool)
    let isIdx24 := ((· == ·) <$> idxSig <*> p24_5 : Signal dom Bool)

    -- byteIn matches expected header / footer?
    let byteIsHdr := ((· == ·) <$> byteIn <*> pHdr : Signal dom Bool)
    let byteIsFtr := ((· == ·) <$> byteIn <*> pFtr : Signal dom Bool)

    -- headerOk asserts this cycle iff idx=0, valid, byteIn=0x0F
    let hdrValid := ((· && ·) <$> valid <*> isIdx0 : Signal dom Bool)
    let hdrThisCyc := ((· && ·) <$> hdrValid <*> byteIsHdr : Signal dom Bool)

    -- footerOk asserts this cycle iff idx=24, valid, byteIn=0x00,
    -- AND we saw header at position 0 (hdrSig latched)
    let ftrValid := ((· && ·) <$> valid <*> isIdx24 : Signal dom Bool)
    let ftrValFtr := ((· && ·) <$> ftrValid <*> byteIsFtr : Signal dom Bool)
    let ftrOk := ((· && ·) <$> ftrValFtr <*> hdrSig : Signal dom Bool)

    -- Latch byte1 on cycle idx=1, valid.
    let b1Load := ((· && ·) <$> valid <*> isIdx1 : Signal dom Bool)
    let b1Next := Signal.mux b1Load byteIn b1Sig
    -- Latch byte2 on cycle idx=2, valid.
    let b2Load := ((· && ·) <$> valid <*> isIdx2 : Signal dom Bool)
    let b2Next := Signal.mux b2Load byteIn b2Sig

    -- Index advance on valid: idx := if start then 0 else if valid then idx+1 else idx
    let idxPlus1 := ((· + ·) <$> idxSig <*> p1_5 : Signal dom (BitVec 5))
    let idxAfterValid := Signal.mux valid idxPlus1 idxSig
    let idxNext := Signal.mux start p0_5 idxAfterValid

    -- Update header latch: start resets to false, hdrThisCyc sets true, else hold.
    let hdrSet := Signal.mux hdrThisCyc (Signal.pure true) hdrSig
    let hdrNext := Signal.mux start (Signal.pure false) hdrSet

    idxR <~ idxNext
    hdrR <~ hdrNext
    b1R  <~ b1Next
    b2R  <~ b2Next

    -- ch0 (11 bits LSB-first over byte1..byte2 low 3 bits):
    --   channel 0 = byte1 | (byte2 & 0x07) << 8    (11 bits)
    -- Assemble as BitVec 11: extract 3-bit low nibble of byte2,
    -- concat with byte1 (byte2_lo3 in upper bits, byte1 in lower).
    let b2lo3 := b2Sig.map (BitVec.extractLsb' 0 3 ·)
    let ch0Sig := ((· ++ ·) <$> b2lo3 <*> b1Sig : Signal dom (BitVec 11))

    return ({ idxOut := idxSig, headerOk := hdrSig, footerOk := ftrOk, ch0 := ch0Sig } : FrameOut dom)

end Sparkle.IP.Bus.SBUSHW
