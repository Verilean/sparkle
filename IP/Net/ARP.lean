/-
  IP.Net.ARP — minimal ARP (IPv4) parser / responder / requester.

  ARP packet layout (RFC 826, IPv4-over-Ethernet specialisation —
  28 bytes total, MSB-first on the wire):

    offset  field     size
    0       HTYPE     2     0x0001 (Ethernet)
    2       PTYPE     2     0x0800 (IPv4)
    4       HLEN      1     6      (MAC length)
    5       PLEN      1     4      (IPv4 length)
    6       OPER      2     1 = request, 2 = reply
    8       SHA       6     sender hardware address
    14      SPA       4     sender protocol address (IPv4)
    18      THA       6     target hardware address (zero in a
                              request; sender's MAC in a reply)
    24      TPA       4     target protocol address (IPv4)

  Two modules in this file:

    * `arpResponder` — consumes the *payload byte stream* from
      the Ethernet RX framer (i.e. starts at offset 0 of the
      ARP packet; the upstream is expected to have stripped the
      14-byte Ethernet header and gated on `ethType == 0x0806`).
      When the parsed `OPER == 1` (request) AND `TPA ==
      ownIp`, emit an ARP reply frame's 28 bytes through the
      TX framer's `payloadByte` / `payloadValid` /
      `payloadLast` lines.  `start` is co-pulsed for the
      Ethernet TX framer.

    * `arpRequester` — drives a one-shot ARP request burst when
      its `trigger` input pulses.  Source IP / MAC are
      compile-time configurable; the target IP is sampled
      live from `tpaIn`.  On a reply (consumed via
      `arpResponder`-style parser), latches the resolved MAC
      into a single-entry `cache` register and asserts
      `cacheValid`.

  Both modules share the same internal byte-stream packet
  encoder (`arpReplyByte` / `arpRequestByte`) — they only
  differ in when they fire and what they do with the
  resulting bytes.

  No multi-entry cache, no aging, no gratuitous ARP yet.
  HFT use-case has a single peer; that's all that matters
  for the demo.
-/

import Sparkle
import IP.Net.Ethernet

open Sparkle.Core.Domain
open Sparkle.Core.Signal

namespace Sparkle.IP.Net.ARP

/-! ### Constants. -/

abbrev arpEthType  : BitVec 16 := 0x0806#16
abbrev arpHtype    : BitVec 16 := 0x0001#16
abbrev arpPtype    : BitVec 16 := 0x0800#16
abbrev arpHlen     : BitVec 8  := 6#8
abbrev arpPlen     : BitVec 8  := 4#8
abbrev arpOpRequest : BitVec 16 := 1#16
abbrev arpOpReply   : BitVec 16 := 2#16

/-! ### Per-state index helpers — same byte-extract idiom as
    `Ethernet.macByte` (`signal.map (BitVec.extractLsb' lo 8 ·)`). -/

@[inline] private def byte48 {dom : DomainConfig}
    (mac : Signal dom (BitVec 48)) (k : Nat) :
    Signal dom (BitVec 8) :=
  let lo := (5 - k) * 8
  mac.map (BitVec.extractLsb' lo 8 ·)

@[inline] private def byte32 {dom : DomainConfig}
    (ip : Signal dom (BitVec 32)) (k : Nat) :
    Signal dom (BitVec 8) :=
  let lo := (3 - k) * 8
  ip.map (BitVec.extractLsb' lo 8 ·)

@[inline] private def byte16 {dom : DomainConfig}
    (v : Signal dom (BitVec 16)) (k : Nat) :
    Signal dom (BitVec 8) :=
  let lo := (1 - k) * 8
  v.map (BitVec.extractLsb' lo 8 ·)

/-! ### ARP packet encoder — 28 bytes, MSB-first.

    `arpPacketByte` returns the byte at the given offset (0..27)
    of an ARP packet with the supplied fields filled in.  Used
    by both the responder (to emit reply) and the requester
    (to emit request).

    Note the offset is a runtime *cycle-tracking* index — we
    pre-compute all 28 byte signals up front and pick via mux
    chain.  Verbose but synth-clean: every selector is a
    `BitVec 5` equality. -/

structure ArpFields (dom : DomainConfig) where
  oper : Signal dom (BitVec 16)
  sha  : Signal dom (BitVec 48)
  spa  : Signal dom (BitVec 32)
  tha  : Signal dom (BitVec 48)
  tpa  : Signal dom (BitVec 32)

/-- Select one of the 28 ARP packet bytes by cycle counter.
    `cntSig` should hold values 1..28 (where 1 = ARP offset 0,
    28 = ARP offset 27); 0 = idle, returns the last byte
    (don't-care, gated externally by `payloadValid`).

    Takes the 5 ARP fields as per-Signal arguments (rather than
    bundled in an `ArpFields` record).  The IR elaborator
    can't reliably unpack record-typed function arguments at
    sub-call boundaries — same convention as
    `Ethernet.rxFramer` / `Ethernet.txFramer`. -/
@[hardware_module] def arpPacketByte {dom : DomainConfig}
    (oper : Signal dom (BitVec 16))
    (sha  : Signal dom (BitVec 48))
    (spa  : Signal dom (BitVec 32))
    (tha  : Signal dom (BitVec 48))
    (tpa  : Signal dom (BitVec 32))
    (cntSig : Signal dom (BitVec 6)) :
    Signal dom (BitVec 8) :=
  -- Constant header bytes — write Signal.pure inline rather
  -- than via a `let pure8 (b : BitVec 8) := ...` closure, which
  -- the IR elaborator can't unfold across.
  let b0 : Signal dom (BitVec 8) := Signal.pure (BitVec.extractLsb' 8 8 arpHtype)
  let b1 : Signal dom (BitVec 8) := Signal.pure (BitVec.extractLsb' 0 8 arpHtype)
  let b2 : Signal dom (BitVec 8) := Signal.pure (BitVec.extractLsb' 8 8 arpPtype)
  let b3 : Signal dom (BitVec 8) := Signal.pure (BitVec.extractLsb' 0 8 arpPtype)
  let b4 : Signal dom (BitVec 8) := Signal.pure arpHlen
  let b5 : Signal dom (BitVec 8) := Signal.pure arpPlen
  let b6  := byte16 oper 0
  let b7  := byte16 oper 1
  let b8  := byte48 sha 0
  let b9  := byte48 sha 1
  let b10 := byte48 sha 2
  let b11 := byte48 sha 3
  let b12 := byte48 sha 4
  let b13 := byte48 sha 5
  let b14 := byte32 spa 0
  let b15 := byte32 spa 1
  let b16 := byte32 spa 2
  let b17 := byte32 spa 3
  let b18 := byte48 tha 0
  let b19 := byte48 tha 1
  let b20 := byte48 tha 2
  let b21 := byte48 tha 3
  let b22 := byte48 tha 4
  let b23 := byte48 tha 5
  let b24 := byte32 tpa 0
  let b25 := byte32 tpa 1
  let b26 := byte32 tpa 2
  let b27 := byte32 tpa 3
  -- Pre-built selector signals: cntSig == k+1, k = 0..26.
  let p1  := (Signal.pure 1#6  : Signal dom (BitVec 6))
  let p2  := (Signal.pure 2#6  : Signal dom (BitVec 6))
  let p3  := (Signal.pure 3#6  : Signal dom (BitVec 6))
  let p4  := (Signal.pure 4#6  : Signal dom (BitVec 6))
  let p5  := (Signal.pure 5#6  : Signal dom (BitVec 6))
  let p6  := (Signal.pure 6#6  : Signal dom (BitVec 6))
  let p7  := (Signal.pure 7#6  : Signal dom (BitVec 6))
  let p8  := (Signal.pure 8#6  : Signal dom (BitVec 6))
  let p9  := (Signal.pure 9#6  : Signal dom (BitVec 6))
  let p10 := (Signal.pure 10#6 : Signal dom (BitVec 6))
  let p11 := (Signal.pure 11#6 : Signal dom (BitVec 6))
  let p12 := (Signal.pure 12#6 : Signal dom (BitVec 6))
  let p13 := (Signal.pure 13#6 : Signal dom (BitVec 6))
  let p14 := (Signal.pure 14#6 : Signal dom (BitVec 6))
  let p15 := (Signal.pure 15#6 : Signal dom (BitVec 6))
  let p16 := (Signal.pure 16#6 : Signal dom (BitVec 6))
  let p17 := (Signal.pure 17#6 : Signal dom (BitVec 6))
  let p18 := (Signal.pure 18#6 : Signal dom (BitVec 6))
  let p19 := (Signal.pure 19#6 : Signal dom (BitVec 6))
  let p20 := (Signal.pure 20#6 : Signal dom (BitVec 6))
  let p21 := (Signal.pure 21#6 : Signal dom (BitVec 6))
  let p22 := (Signal.pure 22#6 : Signal dom (BitVec 6))
  let p23 := (Signal.pure 23#6 : Signal dom (BitVec 6))
  let p24 := (Signal.pure 24#6 : Signal dom (BitVec 6))
  let p25 := (Signal.pure 25#6 : Signal dom (BitVec 6))
  let p26 := (Signal.pure 26#6 : Signal dom (BitVec 6))
  let p27 := (Signal.pure 27#6 : Signal dom (BitVec 6))
  let e1  := cntSig === p1
  let e2  := cntSig === p2
  let e3  := cntSig === p3
  let e4  := cntSig === p4
  let e5  := cntSig === p5
  let e6  := cntSig === p6
  let e7  := cntSig === p7
  let e8  := cntSig === p8
  let e9  := cntSig === p9
  let e10 := cntSig === p10
  let e11 := cntSig === p11
  let e12 := cntSig === p12
  let e13 := cntSig === p13
  let e14 := cntSig === p14
  let e15 := cntSig === p15
  let e16 := cntSig === p16
  let e17 := cntSig === p17
  let e18 := cntSig === p18
  let e19 := cntSig === p19
  let e20 := cntSig === p20
  let e21 := cntSig === p21
  let e22 := cntSig === p22
  let e23 := cntSig === p23
  let e24 := cntSig === p24
  let e25 := cntSig === p25
  let e26 := cntSig === p26
  let e27 := cntSig === p27
  Signal.mux e1 b0
    (Signal.mux e2 b1
      (Signal.mux e3 b2
        (Signal.mux e4 b3
          (Signal.mux e5 b4
            (Signal.mux e6 b5
              (Signal.mux e7 b6
                (Signal.mux e8 b7
                  (Signal.mux e9 b8
                    (Signal.mux e10 b9
                      (Signal.mux e11 b10
                        (Signal.mux e12 b11
                          (Signal.mux e13 b12
                            (Signal.mux e14 b13
                              (Signal.mux e15 b14
                                (Signal.mux e16 b15
                                  (Signal.mux e17 b16
                                    (Signal.mux e18 b17
                                      (Signal.mux e19 b18
                                        (Signal.mux e20 b19
                                          (Signal.mux e21 b20
                                            (Signal.mux e22 b21
                                              (Signal.mux e23 b22
                                                (Signal.mux e24 b23
                                                  (Signal.mux e25 b24
                                                    (Signal.mux e26 b25
                                                      (Signal.mux e27 b26 b27))))))))))))))))))))))))))

/-! ### ARP-packet shift-in parser.

    Symmetric to the Ethernet `shiftIn48` / `shiftIn16` helpers.
    Walks an incoming byte stream and accumulates SHA, SPA,
    OPER, TPA into registers.  Other fields (HTYPE / PTYPE /
    HLEN / PLEN / THA) are skipped — they're not used by the
    responder's `is this for me?` check or by the requester's
    cache update.

    Counter `cnt` runs 0..27.  Caller pulses `sopArp` on the
    cycle where the first ARP-payload byte arrives; subsequent
    cycles increment `cnt` while `valid` is high.  After byte
    27 the parser asserts `done` for one cycle (the cycle
    after byte 27 has been latched).
-/

@[inline] private def shiftIn48Of {dom : DomainConfig}
    (acc : Signal dom (BitVec 48)) (b : Signal dom (BitVec 8)) :
    Signal dom (BitVec 48) :=
  (acc <<< (8#48 : BitVec 48)) ||| ((0#40 : BitVec 40) ++ b)

@[inline] private def shiftIn32Of {dom : DomainConfig}
    (acc : Signal dom (BitVec 32)) (b : Signal dom (BitVec 8)) :
    Signal dom (BitVec 32) :=
  (acc <<< (8#32 : BitVec 32)) ||| ((0#24 : BitVec 24) ++ b)

@[inline] private def shiftIn16Of {dom : DomainConfig}
    (acc : Signal dom (BitVec 16)) (b : Signal dom (BitVec 8)) :
    Signal dom (BitVec 16) :=
  (acc <<< (8#16 : BitVec 16)) ||| ((0#8 : BitVec 8) ++ b)

/-- Output of the ARP byte-stream parser. -/
structure ArpRxOut (dom : DomainConfig) where
  oper     : Signal dom (BitVec 16)
  sha      : Signal dom (BitVec 48)
  spa      : Signal dom (BitVec 32)
  tpa      : Signal dom (BitVec 32)
  /-- High for the single cycle after the 28th ARP byte is
      latched.  Consumers (responder / requester) latch the
      decision on this edge. -/
  done     : Signal dom Bool

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (ArpRxOut dom) dom := ⟨⟩

def arpRxParser {dom : DomainConfig}
    (byte  : Signal dom (BitVec 8))
    (valid : Signal dom Bool)
    (sopArp : Signal dom Bool) :
    ArpRxOut dom :=
  circuit do
    -- Byte counter (5-bit covers 0..27).  0 = idle; 1..28 =
    -- ingested-byte index.  Done strobes when cnt rolls from
    -- 28 back to 0.
    let cnt   ← Signal.reg (0#6)
    let oReg  ← Signal.reg (0#16)
    let shaR  ← Signal.reg (0#48)
    let spaR  ← Signal.reg (0#32)
    let tpaR  ← Signal.reg (0#32)
    let dnR   ← Signal.reg false

    let cntSig := (cnt : Signal dom (BitVec 6))
    -- `cntSig` carries the offset of the byte arriving on the
    -- WIRE this cycle (so it indexes the byte that's about to
    -- be shifted into a register on the next posedge).  On the
    -- `sopArp` cycle the wire byte is at offset 0 and the
    -- register holds 0; the next cycle, cntSig = 1; and so on.
    let p6  := (Signal.pure 6#6 : Signal dom (BitVec 6))
    let p7  := (Signal.pure 7#6 : Signal dom (BitVec 6))
    let p8  := (Signal.pure 8#6 : Signal dom (BitVec 6))
    let p9  := (Signal.pure 9#6 : Signal dom (BitVec 6))
    let p10 := (Signal.pure 10#6 : Signal dom (BitVec 6))
    let p11 := (Signal.pure 11#6 : Signal dom (BitVec 6))
    let p12 := (Signal.pure 12#6 : Signal dom (BitVec 6))
    let p13 := (Signal.pure 13#6 : Signal dom (BitVec 6))
    let p14 := (Signal.pure 14#6 : Signal dom (BitVec 6))
    let p15 := (Signal.pure 15#6 : Signal dom (BitVec 6))
    let p16 := (Signal.pure 16#6 : Signal dom (BitVec 6))
    let p17 := (Signal.pure 17#6 : Signal dom (BitVec 6))
    let p24 := (Signal.pure 24#6 : Signal dom (BitVec 6))
    let p25 := (Signal.pure 25#6 : Signal dom (BitVec 6))
    let p26 := (Signal.pure 26#6 : Signal dom (BitVec 6))
    let p27 := (Signal.pure 27#6 : Signal dom (BitVec 6))
    let eq6  := cntSig === p6
    let eq7  := cntSig === p7
    let eq8  := cntSig === p8
    let eq9  := cntSig === p9
    let eq10 := cntSig === p10
    let eq11 := cntSig === p11
    let eq12 := cntSig === p12
    let eq13 := cntSig === p13
    let eq14 := cntSig === p14
    let eq15 := cntSig === p15
    let eq16 := cntSig === p16
    let eq17 := cntSig === p17
    let eq24 := cntSig === p24
    let eq25 := cntSig === p25
    let eq26 := cntSig === p26
    let eq27 := cntSig === p27
    let inOper := eq6 ||| eq7
    let inSha  := eq8  ||| eq9  ||| eq10 ||| eq11 ||| eq12 ||| eq13
    let inSpa  := eq14 ||| eq15 ||| eq16 ||| eq17
    let inTpa  := eq24 ||| eq25 ||| eq26 ||| eq27
    let isLast := eq27

    let oNext   := shiftIn16Of oReg byte
    let shaNext := shiftIn48Of shaR byte
    let spaNext := shiftIn32Of spaR byte
    let tpaNext := shiftIn32Of tpaR byte

    let oReadSig   := (oReg : Signal dom (BitVec 16))
    let shaReadSig := (shaR : Signal dom (BitVec 48))
    let spaReadSig := (spaR : Signal dom (BitVec 32))
    let tpaReadSig := (tpaR : Signal dom (BitVec 32))

    -- Counter update:
    --   `sopArp` → set to 1 (we just latched byte 0).
    --   `valid` and counting → cnt + 1.
    --   Else                 → hold.
    -- Roll-over to 0 implicitly on the next sopArp (or when
    -- the caller stops asserting valid past byte 28).
    let cntInc := (· + ·) <$> cntSig
                    <*> (Signal.pure 1#6 : Signal dom (BitVec 6))
    cnt  <~ Signal.mux sopArp (Signal.pure 1#6)
              (Signal.mux valid cntInc cntSig)
    oReg  <~ Signal.mux (valid &&& inOper) oNext oReadSig
    shaR  <~ Signal.mux (valid &&& inSha)  shaNext shaReadSig
    spaR  <~ Signal.mux (valid &&& inSpa)  spaNext spaReadSig
    tpaR  <~ Signal.mux (valid &&& inTpa)  tpaNext tpaReadSig
    dnR   <~ valid &&& isLast

    return ({ oper := oReadSig
            , sha  := shaReadSig
            , spa  := spaReadSig
            , tpa  := tpaReadSig
            , done := (dnR : Signal dom Bool)
            } : ArpRxOut dom)

/-! ### ARP responder.

    Glue layer that combines `arpRxParser` with an inverted
    `arpPacketByte` byte emitter.  When the parser asserts
    `done`:
      * If `oper == 1` (request) and `tpa == ownIp`, transition
        into the "emitting reply" state, latch the resolved
        `sha`/`spa` into the THA/TPA fields of the outgoing
        packet, and start streaming bytes 0..27.
      * Otherwise (not for us, or it's a reply), stay idle.

    The output `txStart` strobes one cycle before the byte
    stream begins, matching the Ethernet TX framer's
    `start`/`payloadValid` interface.  The caller is
    responsible for wiring the responder's outputs into
    `txFramer` (or an equivalent Ethernet TX block) along with
    the response's DMAC/SMAC/EthType header.
-/

structure ArpResponderOut (dom : DomainConfig) where
  /-- Reply DMAC = requester's MAC.  Valid concurrently with
      `txStart`. -/
  replyDmac : Signal dom (BitVec 48)
  /-- Reply EthType = 0x0806. -/
  replyEthType : Signal dom (BitVec 16)
  /-- The byte being emitted on the reply byte stream. -/
  payloadByte  : Signal dom (BitVec 8)
  /-- High while emitting the 28 reply bytes. -/
  payloadValid : Signal dom Bool
  /-- Strobes on the last (28th) byte. -/
  payloadLast  : Signal dom Bool
  /-- One-cycle strobe co-aligned with the first reply byte;
      use as the `start` input to the Ethernet TX framer. -/
  txStart      : Signal dom Bool

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (ArpResponderOut dom) dom := ⟨⟩

def arpResponder {dom : DomainConfig}
    (rxByte  : Signal dom (BitVec 8))
    (rxValid : Signal dom Bool)
    (sopArp  : Signal dom Bool)
    (ownMac  : Signal dom (BitVec 48))
    (ownIp   : Signal dom (BitVec 32)) :
    ArpResponderOut dom :=
  let parsed := arpRxParser rxByte rxValid sopArp
  circuit do
    -- TX-side byte counter.  0 = idle; 1..28 = emitting byte
    -- (offset = txCnt - 1).
    let txCnt   ← Signal.reg (0#6)
    -- Latched reply fields: SHA = requester's SHA (from
    -- parsed.sha), TPA = requester's SPA (from parsed.spa).
    -- We don't need to re-latch SHA/SPA separately because we
    -- copy them straight from parsed.* — held by parsed's own
    -- registers until the next sopArp.
    let txCntSig := (txCnt : Signal dom (BitVec 6))

    -- Match check: parser is done AND oper == request AND
    -- tpa == ownIp.  The match latches just for one cycle
    -- (done is one-cycle); use it to load txCnt = 1.
    let pOpReq := (Signal.pure arpOpRequest : Signal dom (BitVec 16))
    let isReq  := parsed.oper === pOpReq
    let isForMe := parsed.tpa === ownIp
    let matchPulse := parsed.done &&& isReq &&& isForMe

    -- Emit-state predicates: txCnt > 0 AND txCnt <= 28.
    let pTxZero := (Signal.pure 0#6  : Signal dom (BitVec 6))
    let p28     := (Signal.pure 28#6 : Signal dom (BitVec 6))
    let p1      := (Signal.pure 1#6  : Signal dom (BitVec 6))
    let isIdle  := txCntSig === pTxZero
    let isLastB := txCntSig === p28
    let isEmitting := ~~~isIdle

    -- Reply fields: swap requester/responder roles.
    let byteOut := arpPacketByte
      (Signal.pure arpOpReply)
      ownMac           -- our MAC
      ownIp            -- our IP
      parsed.sha       -- requester's MAC → THA
      parsed.spa       -- requester's IP  → TPA
      txCntSig

    -- Counter update: load on matchPulse; +1 while emitting
    -- (txCnt < 28); roll back to 0 after byte 28.
    let txCntInc := txCntSig + p1
    txCnt <~ Signal.mux matchPulse p1
              (Signal.mux isLastB pTxZero
                (Signal.mux isEmitting txCntInc txCntSig))

    return ({ replyDmac    := parsed.sha
            , replyEthType := Signal.pure arpEthType
            , payloadByte  := byteOut
            , payloadValid := isEmitting
            , payloadLast  := isLastB
            , txStart      := matchPulse
            } : ArpResponderOut dom)

/-! ### ARP requester.

    Trigger-driven one-shot: on a `trigger` pulse, latches the
    `tpaIn` (the IP we want to resolve) and starts streaming a
    request frame.  Receives replies through the same
    `arpRxParser` byte stream and, when a matching reply
    arrives (oper == 2 && spa == latchedTpa), captures the
    sender's MAC into `cache` and asserts `cacheValid` until
    the next trigger.

    Source IP / MAC are inputs (not compile-time constants) so
    the same module can serve multiple namespaces — the demo
    just wires them to host constants.
-/

structure ArpRequesterOut (dom : DomainConfig) where
  /-- Reply DMAC for the *outgoing request*.  Always
      0xFFFFFFFFFFFF (broadcast). -/
  reqDmac : Signal dom (BitVec 48)
  reqEthType : Signal dom (BitVec 16)
  payloadByte  : Signal dom (BitVec 8)
  payloadValid : Signal dom Bool
  payloadLast  : Signal dom Bool
  txStart      : Signal dom Bool
  /-- Resolved MAC for the latest target. -/
  cache        : Signal dom (BitVec 48)
  /-- High once a reply has been seen for the most-recent
      target; resets on the next `trigger` pulse. -/
  cacheValid   : Signal dom Bool

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (ArpRequesterOut dom) dom := ⟨⟩

def arpRequester {dom : DomainConfig}
    (trigger : Signal dom Bool)
    (tpaIn   : Signal dom (BitVec 32))
    (ownMac  : Signal dom (BitVec 48))
    (ownIp   : Signal dom (BitVec 32))
    (rxByte  : Signal dom (BitVec 8))
    (rxValid : Signal dom Bool)
    (sopArp  : Signal dom Bool) :
    ArpRequesterOut dom :=
  let parsed := arpRxParser rxByte rxValid sopArp
  circuit do
    -- Outgoing-burst counter and latched target IP.
    let txCnt   ← Signal.reg (0#6)
    let tpaReg  ← Signal.reg (0#32)
    let cacheReg ← Signal.reg (0#48)
    let cValidR ← Signal.reg false

    let txCntSig := (txCnt : Signal dom (BitVec 6))
    let tpaSig   := (tpaReg : Signal dom (BitVec 32))
    let cacheSig := (cacheReg : Signal dom (BitVec 48))
    let cValidSig := (cValidR : Signal dom Bool)

    let pTxZero := (Signal.pure 0#6  : Signal dom (BitVec 6))
    let p28     := (Signal.pure 28#6 : Signal dom (BitVec 6))
    let p1      := (Signal.pure 1#6  : Signal dom (BitVec 6))
    let isIdle    := txCntSig === pTxZero
    let isLastB   := txCntSig === p28
    let isEmitting := ~~~isIdle

    -- Request fields: broadcast THA placeholder (0); target IP
    -- from latched tpaReg, or live tpaIn on the trigger cycle
    -- (the reg hasn't been written yet).
    let byteOut := arpPacketByte
      (Signal.pure arpOpRequest)
      ownMac
      ownIp
      (Signal.pure (0#48))
      (Signal.mux trigger tpaIn tpaSig)
      txCntSig

    let txCntInc := txCntSig + p1
    txCnt <~ Signal.mux trigger p1
              (Signal.mux isLastB pTxZero
                (Signal.mux isEmitting txCntInc txCntSig))
    tpaReg <~ Signal.mux trigger tpaIn tpaSig

    -- Reply-capture: when parser.done && oper == 2 && spa
    -- matches latched tpa, latch parser.sha into cache.
    let pOpReply := (Signal.pure arpOpReply : Signal dom (BitVec 16))
    let isReply  := parsed.oper === pOpReply
    let spaMatch := parsed.spa === tpaSig
    let captureP := parsed.done &&& isReply &&& spaMatch

    cacheReg <~ Signal.mux captureP parsed.sha cacheSig
    -- Reset cacheValid on a new trigger; set on capture.
    cValidR  <~ Signal.mux trigger (Signal.pure false)
                  (Signal.mux captureP (Signal.pure true) cValidSig)

    return ({ reqDmac      := Signal.pure (0xFFFFFFFFFFFF#48)
            , reqEthType   := Signal.pure arpEthType
            , payloadByte  := byteOut
            , payloadValid := isEmitting
            , payloadLast  := isLastB
            , txStart      := trigger
            , cache        := cacheSig
            , cacheValid   := cValidSig
            } : ArpRequesterOut dom)

end Sparkle.IP.Net.ARP
