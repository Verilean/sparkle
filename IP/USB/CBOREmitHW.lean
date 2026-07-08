/-
  IP.USB.CBOREmitHW — byte-serial CBOR head emitter (M3).

  A CBOR data item begins with a "head": the initial byte
  `(major << 5) | additionalInfo`, optionally followed by 1/2/4/8
  big-endian argument bytes.  This is the hardware analogue of the
  pure `IP.Crypto.CBOR.hdr`, and the byte-serial structural twin of
  `IP.Crypto.RLPHW.rlpHeaderHW` (a round-counter FSM emitting the
  prefix bytes one per cycle, then a `done` pulse).

  Encoding (shortest form, canonical):
    arg < 24        : 1 byte  = (major<<5) | arg
    arg < 0x100     : 2 bytes = (major<<5)|24, arg(1)
    arg < 0x10000   : 3 bytes = (major<<5)|25, arg(2, BE)
    arg < 0x1_0000_0000 : 5 bytes = (major<<5)|26, arg(4, BE)

  (The 8-byte / additionalInfo 27 form is unused by a minimal
  authenticator — every CBOR length or integer it emits fits in
  32 bits.)  The variable payload bytes after the head (COSE x/y,
  authData, DER sig) are streamed by the caller behind an 8-bit
  mux, exactly as RLPHW leaves payload emission to the caller.
-/
import Sparkle
import IP.Crypto.Codec.CBOR

namespace Sparkle.IP.USB.CBOREmitHW

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-- Output record for the head emitter. -/
structure HeadOut (dom : DomainConfig) where
  /-- Head byte this cycle (valid when `headValid`). -/
  headByte  : Signal dom (BitVec 8)
  /-- High while a head byte is being emitted. -/
  headValid : Signal dom Bool
  /-- Total head length in bytes (1, 2, 3, or 5), latched on start. -/
  headLen   : Signal dom (BitVec 3)
  /-- Pulses one cycle after the last head byte is emitted. -/
  done      : Signal dom Bool

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (HeadOut dom) dom := ⟨⟩

/-- Byte-serial CBOR head emitter.  On `start`, latch `major`
    (3-bit) and `arg` (32-bit), compute the head length class, and
    stream the head bytes MSB-first over the following cycles. -/
def cborHeadHW {dom : DomainConfig}
    (start : Signal dom Bool)
    (major : Signal dom (BitVec 3))
    (arg : Signal dom (BitVec 32)) :
    HeadOut dom :=
  circuit do
    let majR  ← Signal.reg (0#3)
    let argR  ← Signal.reg (0#32)
    -- Cycle counter (0 = idle, 1..5 = emitting byte index cnt-1).
    let cntR  ← Signal.reg (0#3)
    let hLenR ← Signal.reg (0#3)
    let doneR ← Signal.reg false

    let majSig  := (majR : Signal dom (BitVec 3))
    let argSig  := (argR : Signal dom (BitVec 32))
    let cntSig  := (cntR : Signal dom (BitVec 3))
    let hLenSig := (hLenR : Signal dom (BitVec 3))

    -- Length-class thresholds on `arg`.
    let p24    := (Signal.pure 24#32   : Signal dom (BitVec 32))
    let p256   := (Signal.pure 256#32  : Signal dom (BitVec 32))
    let p65536 := (Signal.pure 65536#32 : Signal dom (BitVec 32))
    let argLt24  := ((BitVec.ult · ·) <$> arg <*> p24 : Signal dom Bool)
    let argLt256 := ((BitVec.ult · ·) <$> arg <*> p256 : Signal dom Bool)
    let argLt64k := ((BitVec.ult · ·) <$> arg <*> p65536 : Signal dom Bool)
    -- head length = 1 / 2 / 3 / 5.
    let p1_3 := (Signal.pure 1#3 : Signal dom (BitVec 3))
    let p2_3 := (Signal.pure 2#3 : Signal dom (BitVec 3))
    let p3_3 := (Signal.pure 3#3 : Signal dom (BitVec 3))
    let p5_3 := (Signal.pure 5#3 : Signal dom (BitVec 3))
    let hLenNext :=
      Signal.mux argLt24 p1_3
        (Signal.mux argLt256 p2_3
          (Signal.mux argLt64k p3_3 p5_3))

    -- additionalInfo for the initial byte.
    let p0_3   := (Signal.pure 0#3 : Signal dom (BitVec 3))
    let pAi24  := (Signal.pure 24#8 : Signal dom (BitVec 8))
    let pAi25  := (Signal.pure 25#8 : Signal dom (BitVec 8))
    let pAi26  := (Signal.pure 26#8 : Signal dom (BitVec 8))
    -- major<<5 as an 8-bit value: append major(3) ‖ 00000(5).
    let majShift := (majSig.map (fun v => BitVec.append v (0#5)) : Signal dom (BitVec 8))
    -- arg low 5 bits as an 8-bit value (for the inline arg<24 case).
    let argLo5 := (argSig.map (fun v => BitVec.extractLsb' 0 8 v) : Signal dom (BitVec 8))
    -- initial byte for each class.
    let ib1 := (majShift ||| argLo5 : Signal dom (BitVec 8))   -- major | arg
    let ib2 := (majShift ||| pAi24 : Signal dom (BitVec 8))
    let ib3 := (majShift ||| pAi25 : Signal dom (BitVec 8))
    let ib5 := (majShift ||| pAi26 : Signal dom (BitVec 8))
    let initByte :=
      Signal.mux argLt24 ib1 (Signal.mux argLt256 ib2 (Signal.mux argLt64k ib3 ib5))

    -- arg bytes (big-endian), selected by cnt within the tail.
    let argB0 := (argSig.map (fun v => BitVec.extractLsb' 0 8 v)  : Signal dom (BitVec 8))  -- LSB
    let argB1 := (argSig.map (fun v => BitVec.extractLsb' 8 8 v)  : Signal dom (BitVec 8))
    let argB2 := (argSig.map (fun v => BitVec.extractLsb' 16 8 v) : Signal dom (BitVec 8))
    let argB3 := (argSig.map (fun v => BitVec.extractLsb' 24 8 v) : Signal dom (BitVec 8))

    -- Byte index within the head: cnt=1 → initByte; cnt≥2 → arg bytes.
    -- For a 2-byte head (arg<256): cnt=2 → argB0.
    -- For 3-byte (arg<64k): cnt=2 → argB1(hi), cnt=3 → argB0(lo).
    -- For 5-byte: cnt=2..5 → argB3,argB2,argB1,argB0 (BE).
    let p1c := (Signal.pure 1#3 : Signal dom (BitVec 3))
    let p2c := (Signal.pure 2#3 : Signal dom (BitVec 3))
    let p3c := (Signal.pure 3#3 : Signal dom (BitVec 3))
    let p4c := (Signal.pure 4#3 : Signal dom (BitVec 3))
    let p5c := (Signal.pure 5#3 : Signal dom (BitVec 3))
    let isC1 := (cntSig === p1c : Signal dom Bool)
    let isC2 := (cntSig === p2c : Signal dom Bool)
    let isC3 := (cntSig === p3c : Signal dom Bool)
    let isC4 := (cntSig === p4c : Signal dom Bool)
    -- tail byte for the current class + cnt.  Compute per class then mux.
    let tail2 := argB0                                   -- 2-byte head tail
    let tail3 := Signal.mux isC2 argB1 argB0             -- 3-byte head tail
    let tail5 := Signal.mux isC2 argB3 (Signal.mux isC3 argB2 (Signal.mux isC4 argB1 argB0))
    let tailByte := Signal.mux argLt256 tail2 (Signal.mux argLt64k tail3 tail5)
    let outByte := Signal.mux isC1 initByte tailByte

    -- Emit while cnt in 1..hLen.  Position/counter management.
    let cntInc := (cntSig + (Signal.pure 1#3 : Signal dom (BitVec 3)) : Signal dom (BitVec 3))
    let atLast := (cntSig === hLenSig : Signal dom Bool)
    let isIdle := (cntSig === p0_3 : Signal dom Bool)
    let emitting := (~~~isIdle : Signal dom Bool)

    -- Latch inputs + length on start.
    majR  <~ Signal.mux start major majSig
    argR  <~ Signal.mux start arg argSig
    hLenR <~ Signal.mux start hLenNext hLenSig
    -- cnt: 1 on start; +1 while emitting until atLast, then 0.
    cntR  <~ Signal.mux start p1c
              (Signal.mux atLast p0_3
                (Signal.mux isIdle p0_3 cntInc))
    doneR <~ atLast

    return ({ headByte := outByte
            , headValid := emitting
            , headLen := hLenSig
            , done := (doneR : Signal dom Bool)
            } : HeadOut dom)

end Sparkle.IP.USB.CBOREmitHW
