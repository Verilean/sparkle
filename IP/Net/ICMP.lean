/-
  IP.Net.ICMP — minimal ICMP echo request / reply (RFC 792).

  ICMP echo packet layout (over IPv4):
    offset  field          size
    0       Type           1     0x08 = request, 0x00 = reply
    1       Code           1     0x00
    2       Checksum       2     one's-complement over ICMP header + payload
    4       Identifier     2     opaque, echo back unchanged
    6       Sequence       2     opaque, echo back unchanged
    8       Payload        N     echo back unchanged

  This file implements *header-only* echo (no payload bytes
  echoed yet — the responder emits an 8-byte ICMP echo reply
  with the same identifier/sequence as the inbound request).
  Sufficient for the "Sparkle can ping itself in sim" demo;
  payload echoing is straightforward to bolt on once we wire
  a payload buffer.

  Two modules:

    * `icmpEchoResponder` — parses an incoming ICMP echo
      request byte stream (caller provides byte/valid/sopIcmp).
      When `done && type == 0x08`, emits an 8-byte echo reply
      with the captured identifier/sequence and a recomputed
      checksum.

    * `icmpEchoRequester` — trigger-driven one-shot.  On a
      `trigger` pulse, latches caller-provided
      identifier/sequence and emits an 8-byte echo request.
      On the wire-side incoming stream, captures replies and
      reports `replyOk` when one matches the most-recent
      identifier/sequence.

  The header-checksum field is recomputed on emit (taking the
  4 16-bit words: type/code, identifier, sequence, 0 for the
  checksum-field itself).
-/

import Sparkle
import IP.Net.IPv4

open Sparkle.Core.Domain
open Sparkle.Core.Signal

namespace Sparkle.IP.Net.ICMP

/-! ### Constants. -/

abbrev icmpProto    : BitVec 8  := 0x01#8
abbrev icmpTypeReq  : BitVec 8  := 0x08#8
abbrev icmpTypeRep  : BitVec 8  := 0x00#8
abbrev icmpCode     : BitVec 8  := 0x00#8

/-! ### Helpers. -/

@[inline] private def byte16 {dom : DomainConfig}
    (v : Signal dom (BitVec 16)) (k : Nat) :
    Signal dom (BitVec 8) :=
  let lo := (1 - k) * 8
  v.map (BitVec.extractLsb' lo 8 ·)

/-! ### ICMP header checksum.

    For an 8-byte echo header with no payload (the demo case),
    the four 16-bit words are:
      w0 = Type << 8  | Code
      w1 = Identifier
      w2 = Sequence
      w3 = 0   (checksum field treated as 0 for the compute)
    Sum with end-around carry, invert. -/

@[inline] def icmpEchoChecksum
    (typ : BitVec 8) (ident seq : BitVec 16) : BitVec 16 :=
  -- w0 = (type << 8) | code, code = 0; equivalent to
  -- concat-with-zero in the low byte.
  let w0 : BitVec 16 := typ ++ (0#8 : BitVec 8)
  let s1 := IPv4.onesAdd16 w0 ident
  let s2 := IPv4.onesAdd16 s1 seq
  BitVec.not s2

/-- Signal-side checksum.  Same 2-arg `<$> <*>` chain pattern
    as IPv4's, kept inline so handleApplicative can fold each
    `onesAdd16` step. -/
@[inline] def icmpEchoChecksumSig {dom : DomainConfig}
    (typ   : Signal dom (BitVec 8))
    (ident : Signal dom (BitVec 16))
    (seq   : Signal dom (BitVec 16)) :
    Signal dom (BitVec 16) :=
  -- w0 = (type << 8) | code (code=0), expressed as a concat
  -- of type into the high byte and a zero low byte.  Using
  -- concat (which the emitter recognises) instead of `<<<`
  -- avoids a known emitter limitation with constant-shift
  -- through `Signal.map` closures.
  let w0 : Signal dom (BitVec 16) :=
    (· ++ ·) <$> typ <*> (Signal.pure (0#8 : BitVec 8) : Signal dom (BitVec 8))
  let s1 := IPv4.onesAdd16Sig w0 ident
  let s2 := IPv4.onesAdd16Sig s1 seq
  s2.map (BitVec.not ·)

/-! ### Echo reply byte emitter. -/

structure IcmpTxOut (dom : DomainConfig) where
  byte  : Signal dom (BitVec 8)
  valid : Signal dom Bool
  /-- One-cycle strobe on byte 7 (last byte of the 8-byte
      echo header — no payload yet). -/
  last  : Signal dom Bool
  /-- One-cycle strobe co-aligned with byte 0. -/
  start : Signal dom Bool

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (IcmpTxOut dom) dom := ⟨⟩

/-- Per-cycle byte selector for the 8-byte ICMP header.
    `cntSig` should be 1..8 (where 1 = offset 0, 8 = offset
    7); 0 = idle.

    `chksum` is precomputed and passed in by the caller
    (same convention as IPv4 to keep the byte mux separate
    from the parallel-adder compute). -/
@[hardware_module] def icmpHeaderByte {dom : DomainConfig}
    (typ    : Signal dom (BitVec 8))
    (ident  : Signal dom (BitVec 16))
    (seq    : Signal dom (BitVec 16))
    (chksum : Signal dom (BitVec 16))
    (cntSig : Signal dom (BitVec 4)) :
    Signal dom (BitVec 8) :=
  let b0  := typ
  let b1  : Signal dom (BitVec 8) := Signal.pure icmpCode
  let b2  := byte16 chksum 0
  let b3  := byte16 chksum 1
  let b4  := byte16 ident 0
  let b5  := byte16 ident 1
  let b6  := byte16 seq 0
  let b7  := byte16 seq 1
  let p1  := (Signal.pure 1#4 : Signal dom (BitVec 4))
  let p2  := (Signal.pure 2#4 : Signal dom (BitVec 4))
  let p3  := (Signal.pure 3#4 : Signal dom (BitVec 4))
  let p4  := (Signal.pure 4#4 : Signal dom (BitVec 4))
  let p5  := (Signal.pure 5#4 : Signal dom (BitVec 4))
  let p6  := (Signal.pure 6#4 : Signal dom (BitVec 4))
  let p7  := (Signal.pure 7#4 : Signal dom (BitVec 4))
  let e1  := (· == ·) <$> cntSig <*> p1
  let e2  := (· == ·) <$> cntSig <*> p2
  let e3  := (· == ·) <$> cntSig <*> p3
  let e4  := (· == ·) <$> cntSig <*> p4
  let e5  := (· == ·) <$> cntSig <*> p5
  let e6  := (· == ·) <$> cntSig <*> p6
  let e7  := (· == ·) <$> cntSig <*> p7
  Signal.mux e1 b0
    (Signal.mux e2 b1
      (Signal.mux e3 b2
        (Signal.mux e4 b3
          (Signal.mux e5 b4
            (Signal.mux e6 b5
              (Signal.mux e7 b6 b7))))))

/-! ### Echo request / reply RX parser. -/

structure IcmpRxOut (dom : DomainConfig) where
  typ      : Signal dom (BitVec 8)
  ident    : Signal dom (BitVec 16)
  seq      : Signal dom (BitVec 16)
  done     : Signal dom Bool

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (IcmpRxOut dom) dom := ⟨⟩

@[inline] private def shiftIn16 {dom : DomainConfig}
    (acc : Signal dom (BitVec 16)) (b : Signal dom (BitVec 8)) :
    Signal dom (BitVec 16) :=
  (acc <<< (8#16 : BitVec 16)) ||| ((0#8 : BitVec 8) ++ b)

def icmpRxParser {dom : DomainConfig}
    (byte   : Signal dom (BitVec 8))
    (valid  : Signal dom Bool)
    (sopIcmp : Signal dom Bool) :
    IcmpRxOut dom :=
  circuit do
    let cnt    ← Signal.reg (0#4)
    let typR   ← Signal.reg (0#8)
    let idR    ← Signal.reg (0#16)
    let seqR   ← Signal.reg (0#16)
    let doneR  ← Signal.reg false

    let cntSig := (cnt : Signal dom (BitVec 4))
    let typSig := (typR : Signal dom (BitVec 8))
    let idSig  := (idR  : Signal dom (BitVec 16))
    let seqSig := (seqR : Signal dom (BitVec 16))
    let doneSig := (doneR : Signal dom Bool)

    -- Offset selectors: sopIcmp covers offset 0 (Type byte);
    -- cnt==1 covers Code; cnt==4..5 = Ident; cnt==6..7 = Seq;
    -- isLast at cnt==7.
    let p1 := (Signal.pure 1#4 : Signal dom (BitVec 4))
    let p4 := (Signal.pure 4#4 : Signal dom (BitVec 4))
    let p5 := (Signal.pure 5#4 : Signal dom (BitVec 4))
    let p6 := (Signal.pure 6#4 : Signal dom (BitVec 4))
    let p7 := (Signal.pure 7#4 : Signal dom (BitVec 4))
    let inIdent := (((· == ·) <$> cntSig <*> p4) |||
                    ((· == ·) <$> cntSig <*> p5))
    let inSeq   := (((· == ·) <$> cntSig <*> p6) |||
                    ((· == ·) <$> cntSig <*> p7))
    let isLast  := (· == ·) <$> cntSig <*> p7

    let idNext  := shiftIn16 idSig byte
    let seqNext := shiftIn16 seqSig byte
    let cntInc := (· + ·) <$> cntSig <*> p1
    cnt   <~ Signal.mux sopIcmp p1
              (Signal.mux valid cntInc cntSig)
    typR  <~ Signal.mux sopIcmp byte typSig
    idR   <~ Signal.mux (valid &&& inIdent) idNext idSig
    seqR  <~ Signal.mux (valid &&& inSeq)   seqNext seqSig
    doneR <~ valid &&& isLast

    return ({ typ   := typSig
            , ident := idSig
            , seq   := seqSig
            , done  := doneSig
            } : IcmpRxOut dom)

/-! ### Echo responder.

    Pipes the parser into an 8-byte reply emitter.  On the
    parser's `done` pulse, if `typ == 0x08` (echo request),
    load txCnt=1 and start emitting the reply with type=0x00
    and the captured identifier/sequence echoed back. -/

structure IcmpResponderOut (dom : DomainConfig) where
  txByte  : Signal dom (BitVec 8)
  txValid : Signal dom Bool
  txLast  : Signal dom Bool
  txStart : Signal dom Bool
  /-- Mirrors txStart for clarity / wiring. -/
  fireReply : Signal dom Bool

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (IcmpResponderOut dom) dom := ⟨⟩

def icmpEchoResponder {dom : DomainConfig}
    (byte    : Signal dom (BitVec 8))
    (valid   : Signal dom Bool)
    (sopIcmp : Signal dom Bool) :
    IcmpResponderOut dom :=
  let parsed := icmpRxParser byte valid sopIcmp
  circuit do
    let txCnt   ← Signal.reg (0#4)
    let typLatch ← Signal.reg (0#8)
    let idLatch  ← Signal.reg (0#16)
    let seqLatch ← Signal.reg (0#16)

    let txCntSig := (txCnt : Signal dom (BitVec 4))
    let typSig   := (typLatch : Signal dom (BitVec 8))
    let idSig    := (idLatch  : Signal dom (BitVec 16))
    let seqSig   := (seqLatch : Signal dom (BitVec 16))

    let p0 := (Signal.pure 0#4 : Signal dom (BitVec 4))
    let p1 := (Signal.pure 1#4 : Signal dom (BitVec 4))
    let p8 := (Signal.pure 8#4 : Signal dom (BitVec 4))
    let isIdle := (· == ·) <$> txCntSig <*> p0
    let isLast := (· == ·) <$> txCntSig <*> p8
    let isEmitting := (fun b => !b) <$> isIdle

    -- Match check: parser done AND captured type == echo request.
    let pReq := (Signal.pure icmpTypeReq : Signal dom (BitVec 8))
    let isReq := (· == ·) <$> parsed.typ <*> pReq
    let matchPulse := parsed.done &&& isReq

    -- Reply fields: type=Reply, ident/seq echoed back.
    let replyType := (Signal.pure icmpTypeRep : Signal dom (BitVec 8))
    let chksum := icmpEchoChecksumSig replyType idSig seqSig
    let byteOut := icmpHeaderByte replyType idSig seqSig chksum txCntSig

    let txCntInc := (· + ·) <$> txCntSig <*> p1
    txCnt <~ Signal.mux matchPulse p1
              (Signal.mux isLast p0
                (Signal.mux isEmitting txCntInc txCntSig))
    -- Capture identifier/sequence on matchPulse so they stay
    -- stable during the 8-cycle emit window even if a new
    -- inbound packet starts arriving (single-buffer single-
    -- in-flight assumption).
    typLatch <~ Signal.mux matchPulse parsed.typ typSig
    idLatch  <~ Signal.mux matchPulse parsed.ident idSig
    seqLatch <~ Signal.mux matchPulse parsed.seq seqSig

    return ({ txByte    := byteOut
            , txValid   := isEmitting
            , txLast    := isLast
            , txStart   := matchPulse
            , fireReply := matchPulse
            } : IcmpResponderOut dom)

/-! ### Echo requester.

    Trigger-driven: emits an 8-byte echo request burst with
    caller-supplied identifier/sequence.  On the RX side,
    pipes the same parser; flags `replyOk` when a reply
    arrives matching the most-recent identifier/sequence. -/

structure IcmpRequesterOut (dom : DomainConfig) where
  txByte  : Signal dom (BitVec 8)
  txValid : Signal dom Bool
  txLast  : Signal dom Bool
  txStart : Signal dom Bool
  /-- High after a matching echo reply is received; reset on
      the next trigger. -/
  replyOk    : Signal dom Bool

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (IcmpRequesterOut dom) dom := ⟨⟩

def icmpEchoRequester {dom : DomainConfig}
    (trigger : Signal dom Bool)
    (identIn : Signal dom (BitVec 16))
    (seqIn   : Signal dom (BitVec 16))
    (byte    : Signal dom (BitVec 8))
    (valid   : Signal dom Bool)
    (sopIcmp : Signal dom Bool) :
    IcmpRequesterOut dom :=
  let parsed := icmpRxParser byte valid sopIcmp
  circuit do
    let txCnt    ← Signal.reg (0#4)
    let idReg    ← Signal.reg (0#16)
    let seqReg   ← Signal.reg (0#16)
    let okR      ← Signal.reg false

    let txCntSig := (txCnt : Signal dom (BitVec 4))
    let idSig    := (idReg  : Signal dom (BitVec 16))
    let seqSig   := (seqReg : Signal dom (BitVec 16))
    let okSig    := (okR    : Signal dom Bool)

    let p0 := (Signal.pure 0#4 : Signal dom (BitVec 4))
    let p1 := (Signal.pure 1#4 : Signal dom (BitVec 4))
    let p8 := (Signal.pure 8#4 : Signal dom (BitVec 4))
    let isIdle := (· == ·) <$> txCntSig <*> p0
    let isLast := (· == ·) <$> txCntSig <*> p8
    let isEmitting := (fun b => !b) <$> isIdle

    -- Outgoing reply: type = request, ident/seq from
    -- live trigger inputs or latched registers.
    let reqType := (Signal.pure icmpTypeReq : Signal dom (BitVec 8))
    let idNow  := Signal.mux trigger identIn idSig
    let seqNow := Signal.mux trigger seqIn   seqSig
    let chksum := icmpEchoChecksumSig reqType idNow seqNow
    let byteOut := icmpHeaderByte reqType idNow seqNow chksum txCntSig

    let txCntInc := (· + ·) <$> txCntSig <*> p1
    txCnt  <~ Signal.mux trigger p1
                (Signal.mux isLast p0
                  (Signal.mux isEmitting txCntInc txCntSig))
    idReg  <~ Signal.mux trigger identIn idSig
    seqReg <~ Signal.mux trigger seqIn   seqSig

    -- Reply capture: parser.done AND type == reply AND
    -- ident/seq match the latched values.
    let pRep := (Signal.pure icmpTypeRep : Signal dom (BitVec 8))
    let isRep := (· == ·) <$> parsed.typ <*> pRep
    let idMatch := (· == ·) <$> parsed.ident <*> idSig
    let seqMatch := (· == ·) <$> parsed.seq <*> seqSig
    let captureP := parsed.done &&& isRep &&& idMatch &&& seqMatch
    okR <~ Signal.mux trigger (Signal.pure false)
            (Signal.mux captureP (Signal.pure true) okSig)

    return ({ txByte  := byteOut
            , txValid := isEmitting
            , txLast  := isLast
            , txStart := trigger
            , replyOk := okSig
            } : IcmpRequesterOut dom)

end Sparkle.IP.Net.ICMP
