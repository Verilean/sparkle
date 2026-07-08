/-
  IP.Crypto.RLPHW — byte-serial RLP prefix emitter (Signal DSL).

  Focus: the RLP-specific piece a HW writer can't avoid — computing
  the length-prefix header for a byte string.  Given an input
  payload length (11-bit, 0..2047 covers everything a wallet
  actually emits), emit either:

    * a single header byte  [0x80 + len]                  for len ≤ 55
    * two header bytes      [0xb8, len]                   for 56 ≤ len ≤ 255
    * three header bytes    [0xb9, hiByte, loByte]        for 256 ≤ len ≤ 2047

  Interface:
    inputs  start (Bool pulse), lenIn (BitVec 11), isList (Bool)
    outputs headerByte (BitVec 8), headerValid (Bool),
            headerLen (BitVec 2), done (Bool pulse)

  Pipeline:
    cycle 0    — start pulse; latches lenIn / isList, computes
                 header shape, emits first header byte + valid=1.
    cycle 1..2 — subsequent header bytes if any (valid=1).
    cycle ≥K   — done pulse (K = header length in bytes),
                 valid=0.

  Payload emission (the raw bytes after the header) is the
  caller's job — this HW closes the *hardware-specific* piece,
  which is the prefix decode.  Concatenating a caller-supplied
  payload stream is a plain 8-bit mux/pass, no state.

  Validation: cycle-by-cycle vs a byte-list obtained by taking
  the first K bytes of `RLP.encode (.bytes (Array.replicate len 0))`
  (i.e. only the prefix).
-/
import Sparkle
import IP.Crypto.Codec.RLP

namespace Sparkle.IP.Crypto.RLPHW

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-- Output record for the header emitter. -/
structure HeaderOut (dom : DomainConfig) where
  /-- Current header byte on this cycle (undefined when `valid = false`). -/
  headerByte  : Signal dom (BitVec 8)
  /-- High while a header byte is being emitted (cycles 0..K-1). -/
  headerValid : Signal dom Bool
  /-- Total header length in bytes (1, 2, or 3).  Latched on start. -/
  headerLen   : Signal dom (BitVec 2)
  /-- Pulses one cycle after the last header byte is emitted. -/
  done        : Signal dom Bool

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (HeaderOut dom) dom := ⟨⟩

/-- Byte-serial RLP header emitter.

    On `start`:
      * If lenIn ≤ 55: emit [offsetShort + len]; K = 1.
      * If 56 ≤ lenIn ≤ 255: emit [offsetShort + 55 + 1, len];  K = 2.
      * Else (up to 2047): emit [offsetShort + 55 + 2, hi, lo]; K = 3.

    `offsetShort` = 0x80 for byte strings, 0xc0 for lists — selected
    by `isList`.

    A 2-bit round counter (`cnt`) walks 0..K-1 emitting one header
    byte per cycle, then pulses `done` and returns to idle. -/
def rlpHeaderHW {dom : DomainConfig}
    (start : Signal dom Bool)
    (lenIn : Signal dom (BitVec 11))
    (isList : Signal dom Bool) :
    HeaderOut dom :=
  circuit do
    -- Latched inputs.
    let lenR    ← Signal.reg (0#11)
    let listR   ← Signal.reg false
    -- Cycle counter (0 = idle, 1..3 = emitting).
    let cntR    ← Signal.reg (0#3)
    -- Latched header length (1..3).
    let hLenR   ← Signal.reg (0#2)
    -- `done` strobe.
    let doneR   ← Signal.reg false

    let lenSig  := (lenR : Signal dom (BitVec 11))
    let listSig := (listR : Signal dom Bool)
    let cntSig  := (cntR : Signal dom (BitVec 3))
    let hLenSig := (hLenR : Signal dom (BitVec 2))

    -- Constants.
    let p0_3   := (Signal.pure 0#3 : Signal dom (BitVec 3))
    let p1_3   := (Signal.pure 1#3 : Signal dom (BitVec 3))
    let p2_3   := (Signal.pure 2#3 : Signal dom (BitVec 3))
    let p3_3   := (Signal.pure 3#3 : Signal dom (BitVec 3))
    let p55_11 := (Signal.pure 55#11 : Signal dom (BitVec 11))
    let p255_11 := (Signal.pure 255#11 : Signal dom (BitVec 11))
    let p1_2   := (Signal.pure 1#2 : Signal dom (BitVec 2))
    let p2_2   := (Signal.pure 2#2 : Signal dom (BitVec 2))
    let p3_2   := (Signal.pure 3#2 : Signal dom (BitVec 2))
    let p0x80  := (Signal.pure 0x80#8 : Signal dom (BitVec 8))
    let p0xc0  := (Signal.pure 0xc0#8 : Signal dom (BitVec 8))
    let p0xb7  := (Signal.pure 0xb7#8 : Signal dom (BitVec 8))
    let p0xf7  := (Signal.pure 0xf7#8 : Signal dom (BitVec 8))

    -- Length-class predicates on the (latched) length.  Use
    -- `BitVec.ule` (in the synth op table) rather than `decide`
    -- on `.toNat`.
    let lenLe55 := ((BitVec.ule · ·) <$> lenSig <*> p55_11 : Signal dom Bool)
    let lenLe255 := ((BitVec.ule · ·) <$> lenSig <*> p255_11 : Signal dom Bool)
    let is1B := lenLe55
    let notLe55 := (~~~lenLe55 : Signal dom Bool)
    let is2B := (notLe55 &&& lenLe255 : Signal dom Bool)

    -- On start, compute the length class from lenIn *before* latching.
    let startLe55  := ((BitVec.ule · ·) <$> lenIn <*> p55_11  : Signal dom Bool)
    let startLe255 := ((BitVec.ule · ·) <$> lenIn <*> p255_11 : Signal dom Bool)
    let startNotLe55 := (~~~startLe55 : Signal dom Bool)
    let startIs2 := (startNotLe55 &&& startLe255 : Signal dom Bool)
    let hLenNext :=
      Signal.mux startLe55 p1_2 (Signal.mux startIs2 p2_2 p3_2)

    -- Offset base.
    let offShort := Signal.mux listSig p0xc0 p0x80
    let offLong  := Signal.mux listSig p0xf7 p0xb7

    -- Byte-slicing helpers.  Widen the 11-bit length to 16 bits
    -- so the (bit 8..15) hi slot is well-defined.
    let lenSig16 :=
      lenSig.map (fun v => BitVec.append (0#5) v)
    let lenLoByte :=
      lenSig16.map (fun v => BitVec.extractLsb' 0 8 v)
    let lenHiByte :=
      lenSig16.map (fun v => BitVec.extractLsb' 8 8 v)
    -- offsetShort + len (only used when is1B).
    let short1 :=
      (offShort + lenLoByte : Signal dom (BitVec 8))
    -- offsetLong + 1 (used when is2B, cycle 0).
    let long2H :=
      (offLong + (Signal.pure 1#8 : Signal dom (BitVec 8)))
    -- offsetLong + 2 (used when 3B, cycle 0).
    let long3H :=
      (offLong + (Signal.pure 2#8 : Signal dom (BitVec 8)))

    -- Cycle-0 byte: header start byte.
    let byte0 :=
      Signal.mux is1B short1
        (Signal.mux is2B long2H long3H)

    -- Cycle-1 byte: length (2B: lo, 3B: hi).
    let byte1 :=
      Signal.mux is2B lenLoByte lenHiByte
    -- Cycle-2 byte: length lo (only 3B).
    let byte2 := lenLoByte

    -- Which cycle are we on?
    let isC0 := (cntSig === p1_3 : Signal dom Bool)  -- emitting byte 0
    let isC1 := (cntSig === p2_3 : Signal dom Bool)
    let isC2 := (cntSig === p3_3 : Signal dom Bool)
    let isIdle := (cntSig === p0_3 : Signal dom Bool)

    -- Header byte on the current cycle.
    let curByte :=
      Signal.mux isC0 byte0 (Signal.mux isC1 byte1 byte2)

    -- Header valid: not idle and not-past-the-header.
    -- Zero-extend hLenSig (BitVec 2) to BitVec 3 to compare with cntSig.
    let hLenSig3 :=
      hLenSig.map (fun v => BitVec.append (0#1) v)
    let cntLeHLen := ((BitVec.ule · ·) <$> cntSig <*> hLenSig3 : Signal dom Bool)
    let notIdle := (~~~isIdle : Signal dom Bool)
    let valid := (notIdle &&& cntLeHLen : Signal dom Bool)

    -- done pulses when cnt == hLen (i.e. we just emitted the last byte
    -- and are transitioning back to idle).
    let cntEqHLen := (cntSig === hLenSig3 : Signal dom Bool)
    let doneNow := (notIdle &&& cntEqHLen : Signal dom Bool)

    -- Register updates.
    lenR <~ Signal.mux start lenIn lenSig
    listR <~ Signal.mux start isList listSig
    hLenR <~ Signal.mux start hLenNext hLenSig
    -- Counter: 0 → 1 on start, +1 while emitting, → 0 after doneNow.
    let cntInc := (cntSig + p1_3 : Signal dom (BitVec 3))
    cntR <~ Signal.mux start p1_3
              (Signal.mux doneNow p0_3
                (Signal.mux isIdle p0_3 cntInc))
    doneR <~ doneNow

    return ({ headerByte  := curByte
            , headerValid := valid
            , headerLen   := hLenSig
            , done        := (doneR : Signal dom Bool)
            } : HeaderOut dom)

end Sparkle.IP.Crypto.RLPHW
