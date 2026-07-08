/-
  IP.Net.TCP — header parse / emit + pseudo-header checksum.

  TCP header layout (20 bytes, no options for this MVP):
    offset  field         size
    0       SrcPort       2
    2       DstPort       2
    4       SeqNum        4
    8       AckNum        4
    12      DataOff(4)+Rsvd(3)+NS(1)+Flags(8)   2
              Flags (MSB→LSB): CWR ECE URG ACK PSH RST SYN FIN
    14      Window        2
    16      Checksum      2   one's-complement over pseudo-header
                              + TCP segment (header + payload)
    18      UrgentPtr     2

  Pseudo-header for checksum (IPv4, RFC 793 §3.1, 12 bytes):
    SrcIP(4) | DstIP(4) | Zero(1) | Protocol(1) | TcpLength(2)
  Then sum the TCP header (with Checksum field = 0) and payload.

  No options support: DataOffset is always 5 (20 / 4) and the
  Reserved/NS bits are zeroed.  Flag bits are exposed to the
  caller as individual Bool signals so the state machine can
  pattern-match cleanly.

  Provides:
    * `tcpFlags`     : packed-bit accessors (BitVec 8 → bool)
    * `tcpHeaderByte` (`@[hardware_module]`): per-cycle byte
      mux over the 20-byte header.
    * `tcpChecksumSig`: signal-side pseudo-header + payload
      checksum.  For now, takes the full TCP-segment length
      (header bytes only — no payload yet) so the demo can
      progress without a payload buffer.
    * `tcpRxParser`  : byte-stream → all 9 header fields.
-/

import Sparkle
import IP.Net.IPv4

open Sparkle.Core.Domain
open Sparkle.Core.Signal

namespace Sparkle.IP.Net.TCP

/-! ### Flag bit masks (within the 8-bit flag byte at offset 13). -/
abbrev flagFin : BitVec 8 := 0x01#8
abbrev flagSyn : BitVec 8 := 0x02#8
abbrev flagRst : BitVec 8 := 0x04#8
abbrev flagPsh : BitVec 8 := 0x08#8
abbrev flagAck : BitVec 8 := 0x10#8
abbrev flagUrg : BitVec 8 := 0x20#8
abbrev flagEce : BitVec 8 := 0x40#8
abbrev flagCwr : BitVec 8 := 0x80#8

abbrev protoTcp : BitVec 8 := 0x06#8

/-! ### Byte helpers. -/

@[inline] private def byte16 {dom : DomainConfig}
    (v : Signal dom (BitVec 16)) (k : Nat) :
    Signal dom (BitVec 8) :=
  let lo := (1 - k) * 8
  v.map (BitVec.extractLsb' lo 8 ·)

@[inline] private def byte32 {dom : DomainConfig}
    (v : Signal dom (BitVec 32)) (k : Nat) :
    Signal dom (BitVec 8) :=
  let lo := (3 - k) * 8
  v.map (BitVec.extractLsb' lo 8 ·)

/-! ### Pure-data and Signal-side TCP checksum.

    The pseudo-header is a fixed 12-byte structure prepended
    to the TCP segment for checksum purposes (not actually
    transmitted).  For a 20-byte header with no payload, the
    full checksum input is 32 bytes = 16 16-bit words:

      6 from pseudo-header (srcIP×2, dstIP×2, zero+proto, len)
      10 from TCP header (with Checksum field = 0)

    Sum with end-around carry, invert.  We reuse
    `IPv4.onesAdd16Sig` per step. -/

/-- Pure-data TCP checksum over header-only segment (no
    payload yet).  Used by tests to build reference values. -/
@[inline] def tcpHeaderChecksum
    (srcIP dstIP : BitVec 32) (tcpLen : BitVec 16)
    (srcPort dstPort : BitVec 16)
    (seqNum ackNum : BitVec 32)
    (dataOffFlags : BitVec 16)
    (window urgent : BitVec 16) : BitVec 16 :=
  let srcHi : BitVec 16 := BitVec.extractLsb' 16 16 srcIP
  let srcLo : BitVec 16 := BitVec.extractLsb' 0 16 srcIP
  let dstHi : BitVec 16 := BitVec.extractLsb' 16 16 dstIP
  let dstLo : BitVec 16 := BitVec.extractLsb' 0 16 dstIP
  let zeroProto : BitVec 16 := (0#8 : BitVec 8) ++ protoTcp
  let seqHi : BitVec 16 := BitVec.extractLsb' 16 16 seqNum
  let seqLo : BitVec 16 := BitVec.extractLsb' 0 16 seqNum
  let ackHi : BitVec 16 := BitVec.extractLsb' 16 16 ackNum
  let ackLo : BitVec 16 := BitVec.extractLsb' 0 16 ackNum
  -- Pseudo-header (6 words):
  let s := IPv4.onesAdd16 srcHi srcLo
  let s := IPv4.onesAdd16 s dstHi
  let s := IPv4.onesAdd16 s dstLo
  let s := IPv4.onesAdd16 s zeroProto
  let s := IPv4.onesAdd16 s tcpLen
  -- TCP segment (10 words; checksum field=0 is implicit by
  -- skipping it):
  let s := IPv4.onesAdd16 s srcPort
  let s := IPv4.onesAdd16 s dstPort
  let s := IPv4.onesAdd16 s seqHi
  let s := IPv4.onesAdd16 s seqLo
  let s := IPv4.onesAdd16 s ackHi
  let s := IPv4.onesAdd16 s ackLo
  let s := IPv4.onesAdd16 s dataOffFlags
  let s := IPv4.onesAdd16 s window
  let s := IPv4.onesAdd16 s urgent
  BitVec.not s

/-- Signal-side checksum.  Same chaining of `onesAdd16Sig`
    sub-module instances as IPv4 — works because
    `onesAdd16Sig` is now built from Signal-native primitives
    (concat + add + slice). -/
@[hardware_module] def tcpHeaderChecksumSig {dom : DomainConfig}
    (srcIP dstIP : Signal dom (BitVec 32))
    (tcpLen : Signal dom (BitVec 16))
    (srcPort dstPort : Signal dom (BitVec 16))
    (seqNum ackNum : Signal dom (BitVec 32))
    (dataOffFlags : Signal dom (BitVec 16))
    (window urgent : Signal dom (BitVec 16)) :
    Signal dom (BitVec 16) :=
  let srcHi : Signal dom (BitVec 16) :=
    srcIP.map (BitVec.extractLsb' 16 16 ·)
  let srcLo : Signal dom (BitVec 16) :=
    srcIP.map (BitVec.extractLsb' 0 16 ·)
  let dstHi : Signal dom (BitVec 16) :=
    dstIP.map (BitVec.extractLsb' 16 16 ·)
  let dstLo : Signal dom (BitVec 16) :=
    dstIP.map (BitVec.extractLsb' 0 16 ·)
  let zeroProto : Signal dom (BitVec 16) :=
    Signal.pure ((0#8 : BitVec 8) ++ protoTcp)
  let seqHi : Signal dom (BitVec 16) :=
    seqNum.map (BitVec.extractLsb' 16 16 ·)
  let seqLo : Signal dom (BitVec 16) :=
    seqNum.map (BitVec.extractLsb' 0 16 ·)
  let ackHi : Signal dom (BitVec 16) :=
    ackNum.map (BitVec.extractLsb' 16 16 ·)
  let ackLo : Signal dom (BitVec 16) :=
    ackNum.map (BitVec.extractLsb' 0 16 ·)
  let s := IPv4.onesAdd16Sig srcHi srcLo
  let s := IPv4.onesAdd16Sig s dstHi
  let s := IPv4.onesAdd16Sig s dstLo
  let s := IPv4.onesAdd16Sig s zeroProto
  let s := IPv4.onesAdd16Sig s tcpLen
  let s := IPv4.onesAdd16Sig s srcPort
  let s := IPv4.onesAdd16Sig s dstPort
  let s := IPv4.onesAdd16Sig s seqHi
  let s := IPv4.onesAdd16Sig s seqLo
  let s := IPv4.onesAdd16Sig s ackHi
  let s := IPv4.onesAdd16Sig s ackLo
  let s := IPv4.onesAdd16Sig s dataOffFlags
  let s := IPv4.onesAdd16Sig s window
  let s := IPv4.onesAdd16Sig s urgent
  s.map (BitVec.not ·)

/-! ### TCP header emit — 20-byte byte mux. -/

structure TcpTxOut (dom : DomainConfig) where
  byte  : Signal dom (BitVec 8)
  valid : Signal dom Bool
  last  : Signal dom Bool
  start : Signal dom Bool

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (TcpTxOut dom) dom := ⟨⟩

/-- Per-cycle byte selector for the 20-byte TCP header.
    `cntSig` 1..20 = offset 0..19; 0 = idle. -/
@[hardware_module] def tcpHeaderByte {dom : DomainConfig}
    (srcPort dstPort : Signal dom (BitVec 16))
    (seqNum ackNum : Signal dom (BitVec 32))
    (dataOffFlags : Signal dom (BitVec 16))
    (window : Signal dom (BitVec 16))
    (chksum : Signal dom (BitVec 16))
    (urgent : Signal dom (BitVec 16))
    (cntSig : Signal dom (BitVec 5)) :
    Signal dom (BitVec 8) :=
  let b0  := byte16 srcPort 0
  let b1  := byte16 srcPort 1
  let b2  := byte16 dstPort 0
  let b3  := byte16 dstPort 1
  let b4  := byte32 seqNum 0
  let b5  := byte32 seqNum 1
  let b6  := byte32 seqNum 2
  let b7  := byte32 seqNum 3
  let b8  := byte32 ackNum 0
  let b9  := byte32 ackNum 1
  let b10 := byte32 ackNum 2
  let b11 := byte32 ackNum 3
  let b12 := byte16 dataOffFlags 0
  let b13 := byte16 dataOffFlags 1
  let b14 := byte16 window 0
  let b15 := byte16 window 1
  let b16 := byte16 chksum 0
  let b17 := byte16 chksum 1
  let b18 := byte16 urgent 0
  let b19 := byte16 urgent 1
  let p1  := (Signal.pure 1#5  : Signal dom (BitVec 5))
  let p2  := (Signal.pure 2#5  : Signal dom (BitVec 5))
  let p3  := (Signal.pure 3#5  : Signal dom (BitVec 5))
  let p4  := (Signal.pure 4#5  : Signal dom (BitVec 5))
  let p5  := (Signal.pure 5#5  : Signal dom (BitVec 5))
  let p6  := (Signal.pure 6#5  : Signal dom (BitVec 5))
  let p7  := (Signal.pure 7#5  : Signal dom (BitVec 5))
  let p8  := (Signal.pure 8#5  : Signal dom (BitVec 5))
  let p9  := (Signal.pure 9#5  : Signal dom (BitVec 5))
  let p10 := (Signal.pure 10#5 : Signal dom (BitVec 5))
  let p11 := (Signal.pure 11#5 : Signal dom (BitVec 5))
  let p12 := (Signal.pure 12#5 : Signal dom (BitVec 5))
  let p13 := (Signal.pure 13#5 : Signal dom (BitVec 5))
  let p14 := (Signal.pure 14#5 : Signal dom (BitVec 5))
  let p15 := (Signal.pure 15#5 : Signal dom (BitVec 5))
  let p16 := (Signal.pure 16#5 : Signal dom (BitVec 5))
  let p17 := (Signal.pure 17#5 : Signal dom (BitVec 5))
  let p18 := (Signal.pure 18#5 : Signal dom (BitVec 5))
  let p19 := (Signal.pure 19#5 : Signal dom (BitVec 5))
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
                                      (Signal.mux e19 b18 b19))))))))))))))))))

/-! ### TCP RX header parser. -/

structure TcpRxOut (dom : DomainConfig) where
  srcPort      : Signal dom (BitVec 16)
  dstPort      : Signal dom (BitVec 16)
  seqNum       : Signal dom (BitVec 32)
  ackNum       : Signal dom (BitVec 32)
  dataOffFlags : Signal dom (BitVec 16)
  window       : Signal dom (BitVec 16)
  chksum       : Signal dom (BitVec 16)
  urgent       : Signal dom (BitVec 16)
  /-- High for one cycle after the 20th header byte is latched. -/
  done         : Signal dom Bool

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (TcpRxOut dom) dom := ⟨⟩

@[inline] private def shiftIn32 {dom : DomainConfig}
    (acc : Signal dom (BitVec 32)) (b : Signal dom (BitVec 8)) :
    Signal dom (BitVec 32) :=
  (acc <<< (8#32 : BitVec 32)) ||| ((0#24 : BitVec 24) ++ b)

@[inline] private def shiftIn16 {dom : DomainConfig}
    (acc : Signal dom (BitVec 16)) (b : Signal dom (BitVec 8)) :
    Signal dom (BitVec 16) :=
  (acc <<< (8#16 : BitVec 16)) ||| ((0#8 : BitVec 8) ++ b)

def tcpRxParser {dom : DomainConfig}
    (byte  : Signal dom (BitVec 8))
    (valid : Signal dom Bool)
    (sopTcp : Signal dom Bool) :
    TcpRxOut dom :=
  circuit do
    let cnt   ← Signal.reg (0#5)
    let spR   ← Signal.reg (0#16)
    let dpR   ← Signal.reg (0#16)
    let seqR  ← Signal.reg (0#32)
    let ackR  ← Signal.reg (0#32)
    let dfR   ← Signal.reg (0#16)
    let wndR  ← Signal.reg (0#16)
    let chkR  ← Signal.reg (0#16)
    let urgR  ← Signal.reg (0#16)
    let doneR ← Signal.reg false

    let cntSig := (cnt : Signal dom (BitVec 5))
    let spSig := (spR  : Signal dom (BitVec 16))
    let dpSig := (dpR  : Signal dom (BitVec 16))
    let seqSig := (seqR : Signal dom (BitVec 32))
    let ackSig := (ackR : Signal dom (BitVec 32))
    let dfSig  := (dfR  : Signal dom (BitVec 16))
    let wndSig := (wndR : Signal dom (BitVec 16))
    let chkSig := (chkR : Signal dom (BitVec 16))
    let urgSig := (urgR : Signal dom (BitVec 16))
    let doneSig := (doneR : Signal dom Bool)

    -- Offset selectors.  cnt holds the offset (0..19) of the
    -- byte currently on the wire.  sopTcp = offset 0.
    let p1  := (Signal.pure 1#5  : Signal dom (BitVec 5))
    let p2  := (Signal.pure 2#5  : Signal dom (BitVec 5))
    let p3  := (Signal.pure 3#5  : Signal dom (BitVec 5))
    let p4  := (Signal.pure 4#5  : Signal dom (BitVec 5))
    let p5  := (Signal.pure 5#5  : Signal dom (BitVec 5))
    let p6  := (Signal.pure 6#5  : Signal dom (BitVec 5))
    let p7  := (Signal.pure 7#5  : Signal dom (BitVec 5))
    let p8  := (Signal.pure 8#5  : Signal dom (BitVec 5))
    let p9  := (Signal.pure 9#5  : Signal dom (BitVec 5))
    let p10 := (Signal.pure 10#5 : Signal dom (BitVec 5))
    let p11 := (Signal.pure 11#5 : Signal dom (BitVec 5))
    let p12 := (Signal.pure 12#5 : Signal dom (BitVec 5))
    let p13 := (Signal.pure 13#5 : Signal dom (BitVec 5))
    let p14 := (Signal.pure 14#5 : Signal dom (BitVec 5))
    let p15 := (Signal.pure 15#5 : Signal dom (BitVec 5))
    let p16 := (Signal.pure 16#5 : Signal dom (BitVec 5))
    let p17 := (Signal.pure 17#5 : Signal dom (BitVec 5))
    let p18 := (Signal.pure 18#5 : Signal dom (BitVec 5))
    let p19 := (Signal.pure 19#5 : Signal dom (BitVec 5))
    let eqK0 := sopTcp                                       -- offset 0
    let eqK1  := cntSig === p1
    let eqK2  := cntSig === p2
    let eqK3  := cntSig === p3
    let eqK4  := cntSig === p4
    let eqK5  := cntSig === p5
    let eqK6  := cntSig === p6
    let eqK7  := cntSig === p7
    let eqK8  := cntSig === p8
    let eqK9  := cntSig === p9
    let eqK10 := cntSig === p10
    let eqK11 := cntSig === p11
    let eqK12 := cntSig === p12
    let eqK13 := cntSig === p13
    let eqK14 := cntSig === p14
    let eqK15 := cntSig === p15
    let eqK16 := cntSig === p16
    let eqK17 := cntSig === p17
    let eqK18 := cntSig === p18
    let eqK19 := cntSig === p19
    let inSp  := eqK0  ||| eqK1
    let inDp  := eqK2  ||| eqK3
    let inSeq := eqK4  ||| eqK5  ||| eqK6  ||| eqK7
    let inAck := eqK8  ||| eqK9  ||| eqK10 ||| eqK11
    let inDf  := eqK12 ||| eqK13
    let inWnd := eqK14 ||| eqK15
    let inChk := eqK16 ||| eqK17
    let inUrg := eqK18 ||| eqK19
    let isLast := eqK19

    let spNext  := shiftIn16 spSig byte
    let dpNext  := shiftIn16 dpSig byte
    let seqNext := shiftIn32 seqSig byte
    let ackNext := shiftIn32 ackSig byte
    let dfNext  := shiftIn16 dfSig byte
    let wndNext := shiftIn16 wndSig byte
    let chkNext := shiftIn16 chkSig byte
    let urgNext := shiftIn16 urgSig byte

    let cntInc := cntSig + p1
    cnt   <~ Signal.mux sopTcp p1
              (Signal.mux valid cntInc cntSig)
    spR   <~ Signal.mux (valid &&& inSp)  spNext spSig
    dpR   <~ Signal.mux (valid &&& inDp)  dpNext dpSig
    seqR  <~ Signal.mux (valid &&& inSeq) seqNext seqSig
    ackR  <~ Signal.mux (valid &&& inAck) ackNext ackSig
    dfR   <~ Signal.mux (valid &&& inDf)  dfNext dfSig
    wndR  <~ Signal.mux (valid &&& inWnd) wndNext wndSig
    chkR  <~ Signal.mux (valid &&& inChk) chkNext chkSig
    urgR  <~ Signal.mux (valid &&& inUrg) urgNext urgSig
    doneR <~ valid &&& isLast

    return ({ srcPort      := spSig
            , dstPort      := dpSig
            , seqNum       := seqSig
            , ackNum       := ackSig
            , dataOffFlags := dfSig
            , window       := wndSig
            , chksum       := chkSig
            , urgent       := urgSig
            , done         := doneSig
            } : TcpRxOut dom)

end Sparkle.IP.Net.TCP
