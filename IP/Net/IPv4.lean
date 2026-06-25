/-
  IP.Net.IPv4 — minimal IPv4 parser + TX header builder.

  Header layout (20 bytes, no options, MSB-first):
    offset  field             size
    0       Ver(4)+IHL(4)     1     0x45  (IPv4, 5-dword header)
    1       DSCP/ECN          1     0x00
    2       TotalLength       2
    4       Identification    2
    6       Flags+FragOffset  2     0x4000 (DF, no frag)
    8       TTL               1     0x40
    9       Protocol          1     0x01=ICMP, 0x06=TCP, 0x11=UDP
    10      HeaderChecksum    2
    12      SrcIP             4
    16      DstIP             4

  Two modules:

    * `ipv4RxParser` — byte-stream from Ethernet payload to
      latched (srcIp, dstIp, proto, totalLen, headerOk, done).
      `headerOk` = checksum verifies AND version/IHL/protocol
      are sane.  Caller gates downstream logic on
      (done && headerOk).

    * `ipv4TxBuilder` — emits a 20-byte IPv4 header byte by
      byte, with `totalLen` / `proto` / `srcIp` / `dstIp`
      latched on `start`.  Header checksum is *also* computed
      on-the-fly and inserted at offsets 10..11.  Caller
      drives the payload stream after the 20 header bytes.

  Checksum: one's-complement 16-bit sum.  We pre-compute it
  combinationally over the input fields (which are all
  available at start time) rather than streaming.

  No options, no fragmentation, no version != 4 — single
  flat header path optimized for the HFT scope.
-/

import Sparkle
import IP.Net.Ethernet

open Sparkle.Core.Domain
open Sparkle.Core.Signal

namespace Sparkle.IP.Net.IPv4

/-! ### Constants. -/

abbrev ipv4EthType : BitVec 16 := 0x0800#16
abbrev protoIcmp   : BitVec 8  := 0x01#8
abbrev protoTcp    : BitVec 8  := 0x06#8
abbrev protoUdp    : BitVec 8  := 0x11#8

/-! ### Byte-extract helpers. -/

@[inline] private def byte48 {dom : DomainConfig}
    (v : Signal dom (BitVec 48)) (k : Nat) :
    Signal dom (BitVec 8) :=
  let lo := (5 - k) * 8
  v.map (BitVec.extractLsb' lo 8 ·)

@[inline] private def byte32 {dom : DomainConfig}
    (v : Signal dom (BitVec 32)) (k : Nat) :
    Signal dom (BitVec 8) :=
  let lo := (3 - k) * 8
  v.map (BitVec.extractLsb' lo 8 ·)

@[inline] private def byte16 {dom : DomainConfig}
    (v : Signal dom (BitVec 16)) (k : Nat) :
    Signal dom (BitVec 8) :=
  let lo := (1 - k) * 8
  v.map (BitVec.extractLsb' lo 8 ·)

/-! ### One's-complement 16-bit checksum.

    Sums the 10 16-bit words of the header (skipping the
    checksum field itself which is treated as 0), folds the
    carry, and inverts.  All combinational — no register.

    Inputs are the variable header fields (the rest are
    constants baked into the header layout). -/

/-- Add two 16-bit words with end-around carry into a 16-bit
    result (one's-complement add).  Compute the 17-bit sum
    using a concat-with-zero (rather than `BitVec.zeroExtend`,
    which the IR elaborator doesn't recognise as a hardware
    op), then fold the carry bit back into the low 16 bits.

    Signal-side calls should use `onesAdd16Sig` below — that
    wrapper is `@[hardware_module]` so the IR elaborator emits
    one reusable Verilog sub-module and instantiates it per
    add step, rather than trying to inline this whole
    `BitVec`-arithmetic body through a Signal Applicative
    lift (which `handleApplicative` rejects because the
    lifted lambda contains `let`s rather than a single
    primitive op). -/
def onesAdd16 (a b : BitVec 16) : BitVec 16 :=
  let a17 : BitVec 17 := (0#1 : BitVec 1) ++ a
  let b17 : BitVec 17 := (0#1 : BitVec 1) ++ b
  let s17 : BitVec 17 := a17 + b17
  let low : BitVec 16 := BitVec.extractLsb' 0 16 s17
  let carBit : BitVec 1 := BitVec.extractLsb' 16 1 s17
  let car16 : BitVec 16 := (0#15 : BitVec 15) ++ carBit
  low + car16

/-- Signal-lifted one's-complement add — built up out of
    Signal-native primitives (concat, `+`, slice).  Each step
    is a single op the IR elaborator recognises, so the
    enclosing checksum module synthesizes cleanly.

    Avoid the temptation of `onesAdd16 <$> a <*> b` — that
    handing of a user-defined function to `handleApplicative`
    only works when the function head is a Sparkle-known
    primitive, and `onesAdd16` isn't. -/
@[inline] def onesAdd16Sig {dom : DomainConfig}
    (a b : Signal dom (BitVec 16)) : Signal dom (BitVec 16) :=
  -- 17-bit sum via zero-prepend concat
  let a17 : Signal dom (BitVec 17) :=
    (· ++ ·) <$> (Signal.pure (0#1 : BitVec 1) : Signal dom (BitVec 1)) <*> a
  let b17 : Signal dom (BitVec 17) :=
    (· ++ ·) <$> (Signal.pure (0#1 : BitVec 1) : Signal dom (BitVec 1)) <*> b
  let s17 : Signal dom (BitVec 17) := (· + ·) <$> a17 <*> b17
  -- Low 16 bits and the carry bit (zero-extended back to 16).
  let low    : Signal dom (BitVec 16) :=
    s17.map (BitVec.extractLsb' 0 16 ·)
  let carBit : Signal dom (BitVec 1)  :=
    s17.map (BitVec.extractLsb' 16 1 ·)
  let car16  : Signal dom (BitVec 16) :=
    (· ++ ·) <$> (Signal.pure (0#15 : BitVec 15) : Signal dom (BitVec 15)) <*> carBit
  (· + ·) <$> low <*> car16

/-- Pure-data IPv4 header checksum (RFC 1071): sum of all
    16-bit header words with end-around carry, then inverted.
    The HeaderChecksum field is summed as 0. -/
@[inline] def ipv4HeaderChecksum
    (totalLen : BitVec 16)
    (identification : BitVec 16)
    (flagsFrag : BitVec 16)   -- 0x4000 = DF, no frag
    (ttlProto : BitVec 16)    -- TTL <<8 | Protocol
    (srcIp dstIp : BitVec 32) : BitVec 16 :=
  let verIhl_dscp : BitVec 16 := 0x4500#16
  let srcHi : BitVec 16 := BitVec.extractLsb' 16 16 srcIp
  let srcLo : BitVec 16 := BitVec.extractLsb' 0 16 srcIp
  let dstHi : BitVec 16 := BitVec.extractLsb' 16 16 dstIp
  let dstLo : BitVec 16 := BitVec.extractLsb' 0 16 dstIp
  let s := onesAdd16 verIhl_dscp totalLen
  let s := onesAdd16 s identification
  let s := onesAdd16 s flagsFrag
  let s := onesAdd16 s ttlProto
  let s := onesAdd16 s srcHi
  let s := onesAdd16 s srcLo
  let s := onesAdd16 s dstHi
  let s := onesAdd16 s dstLo
  ~~~s

/-- Signal-side checksum.  Built by chaining 8 sub-module
    calls to `onesAdd16Sig` (one per 16-bit word) and
    inverting the result.  Tagged `@[hardware_module]` so the
    whole compute lands as a reusable sub-module — the
    caller sees a 4-input / 1-output leaf and doesn't pay
    the inline cost.  See `onesAdd16Sig` for the per-step
    sub-module breakdown. -/
@[hardware_module] def ipv4HeaderChecksumSig {dom : DomainConfig}
    (totalLen : Signal dom (BitVec 16))
    (proto    : Signal dom (BitVec 8))
    (srcIp dstIp : Signal dom (BitVec 32)) :
    Signal dom (BitVec 16) :=
  let verIhl_dscp : Signal dom (BitVec 16) := Signal.pure 0x4500#16
  let ident       : Signal dom (BitVec 16) := Signal.pure 0#16
  let flagsFrag   : Signal dom (BitVec 16) := Signal.pure 0x4000#16
  let ttlProto    : Signal dom (BitVec 16) :=
    proto.map (fun p => 0x4000#16 ||| ((0#8 : BitVec 8) ++ p))
  let srcHi : Signal dom (BitVec 16) :=
    srcIp.map (BitVec.extractLsb' 16 16 ·)
  let srcLo : Signal dom (BitVec 16) :=
    srcIp.map (BitVec.extractLsb' 0 16 ·)
  let dstHi : Signal dom (BitVec 16) :=
    dstIp.map (BitVec.extractLsb' 16 16 ·)
  let dstLo : Signal dom (BitVec 16) :=
    dstIp.map (BitVec.extractLsb' 0 16 ·)
  let s1 := onesAdd16Sig verIhl_dscp totalLen
  let s2 := onesAdd16Sig s1 ident
  let s3 := onesAdd16Sig s2 flagsFrag
  let s4 := onesAdd16Sig s3 ttlProto
  let s5 := onesAdd16Sig s4 srcHi
  let s6 := onesAdd16Sig s5 srcLo
  let s7 := onesAdd16Sig s6 dstHi
  let s8 := onesAdd16Sig s7 dstLo
  s8.map (BitVec.not ·)

/-! ### IPv4 TX header builder. -/

structure Ipv4TxOut (dom : DomainConfig) where
  headerByte  : Signal dom (BitVec 8)
  headerValid : Signal dom Bool
  /-- High on the cycle of byte 19 (the last header byte). -/
  headerLast  : Signal dom Bool

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (Ipv4TxOut dom) dom := ⟨⟩

/-- Per-cycle byte selector for the 20-byte IPv4 header.
    `cntSig` should be 1..20 (where 1 = offset 0, 20 = offset
    19); 0 = idle.

    Takes the precomputed `chksum` as an input rather than
    computing it internally; the wrapping driver
    (`ipv4TxBuilder`) calls `ipv4HeaderChecksumSig` once
    outside the byte mux and feeds the result here.  Same
    splitting pattern as ARP's `arpPacketByte`: keeps the
    deeply-nested mux tree separate from the parallel-adder
    checksum compute. -/
@[hardware_module] def ipv4HeaderByte {dom : DomainConfig}
    (totalLen : Signal dom (BitVec 16))
    (proto    : Signal dom (BitVec 8))
    (srcIp    : Signal dom (BitVec 32))
    (dstIp    : Signal dom (BitVec 32))
    (chksum   : Signal dom (BitVec 16))
    (cntSig   : Signal dom (BitVec 5)) :
    Signal dom (BitVec 8) :=
  -- Constants
  let b0  : Signal dom (BitVec 8) := Signal.pure 0x45#8   -- Version(4)+IHL(5)
  let b1  : Signal dom (BitVec 8) := Signal.pure 0x00#8   -- DSCP/ECN
  let b2  := byte16 totalLen 0
  let b3  := byte16 totalLen 1
  let b4  : Signal dom (BitVec 8) := Signal.pure 0x00#8   -- Ident hi
  let b5  : Signal dom (BitVec 8) := Signal.pure 0x00#8   -- Ident lo
  let b6  : Signal dom (BitVec 8) := Signal.pure 0x40#8   -- Flags=DF
  let b7  : Signal dom (BitVec 8) := Signal.pure 0x00#8   -- FragOffset
  let b8  : Signal dom (BitVec 8) := Signal.pure 0x40#8   -- TTL=64
  let b9  := proto
  let b10 := byte16 chksum 0
  let b11 := byte16 chksum 1
  let b12 := byte32 srcIp 0
  let b13 := byte32 srcIp 1
  let b14 := byte32 srcIp 2
  let b15 := byte32 srcIp 3
  let b16 := byte32 dstIp 0
  let b17 := byte32 dstIp 1
  let b18 := byte32 dstIp 2
  let b19 := byte32 dstIp 3
  -- Selector signals
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
  let e1  := (· == ·) <$> cntSig <*> p1
  let e2  := (· == ·) <$> cntSig <*> p2
  let e3  := (· == ·) <$> cntSig <*> p3
  let e4  := (· == ·) <$> cntSig <*> p4
  let e5  := (· == ·) <$> cntSig <*> p5
  let e6  := (· == ·) <$> cntSig <*> p6
  let e7  := (· == ·) <$> cntSig <*> p7
  let e8  := (· == ·) <$> cntSig <*> p8
  let e9  := (· == ·) <$> cntSig <*> p9
  let e10 := (· == ·) <$> cntSig <*> p10
  let e11 := (· == ·) <$> cntSig <*> p11
  let e12 := (· == ·) <$> cntSig <*> p12
  let e13 := (· == ·) <$> cntSig <*> p13
  let e14 := (· == ·) <$> cntSig <*> p14
  let e15 := (· == ·) <$> cntSig <*> p15
  let e16 := (· == ·) <$> cntSig <*> p16
  let e17 := (· == ·) <$> cntSig <*> p17
  let e18 := (· == ·) <$> cntSig <*> p18
  let e19 := (· == ·) <$> cntSig <*> p19
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

/-! ### IPv4 TX driver — wraps `ipv4HeaderByte` with a
    20-cycle byte counter. -/

def ipv4TxBuilder {dom : DomainConfig}
    (totalLen : Signal dom (BitVec 16))
    (proto    : Signal dom (BitVec 8))
    (srcIp    : Signal dom (BitVec 32))
    (dstIp    : Signal dom (BitVec 32))
    (start    : Signal dom Bool) :
    Ipv4TxOut dom :=
  circuit do
    let cnt        ← Signal.reg (0#5)
    let totLenReg  ← Signal.reg (0#16)
    let protoReg   ← Signal.reg (0#8)
    let srcIpReg   ← Signal.reg (0#32)
    let dstIpReg   ← Signal.reg (0#32)

    let cntSig := (cnt : Signal dom (BitVec 5))
    let pZero   := (Signal.pure 0#5  : Signal dom (BitVec 5))
    let p1      := (Signal.pure 1#5  : Signal dom (BitVec 5))
    let p20     := (Signal.pure 20#5 : Signal dom (BitVec 5))
    let isIdle  := (· == ·) <$> cntSig <*> pZero
    let isLast  := (· == ·) <$> cntSig <*> p20
    let isEmitting := (fun b => !b) <$> isIdle

    -- Latch on start.  During the burst we read from the
    -- registers; on the start cycle itself we bypass to the
    -- live input wires so byte 0 (Ver/IHL) gets the right
    -- *length* value when the checksum is computed.
    let tlSig := (totLenReg : Signal dom (BitVec 16))
    let prSig := (protoReg  : Signal dom (BitVec 8))
    let siSig := (srcIpReg  : Signal dom (BitVec 32))
    let diSig := (dstIpReg  : Signal dom (BitVec 32))
    let tlNow := Signal.mux start totalLen tlSig
    let prNow := Signal.mux start proto    prSig
    let siNow := Signal.mux start srcIp    siSig
    let diNow := Signal.mux start dstIp    diSig

    -- Compute checksum once per cycle from the live (or
    -- latched) fields, then feed it into the byte mux.  Same
    -- mux for both start and burst cycles since tlNow / prNow
    -- etc. handle the bypass.
    let chksum := ipv4HeaderChecksumSig tlNow prNow siNow diNow
    let byteOut := ipv4HeaderByte tlNow prNow siNow diNow chksum cntSig

    let cntInc := (· + ·) <$> cntSig <*> p1
    cnt <~ Signal.mux start p1
            (Signal.mux isLast pZero
              (Signal.mux isEmitting cntInc cntSig))
    totLenReg <~ Signal.mux start totalLen tlSig
    protoReg  <~ Signal.mux start proto    prSig
    srcIpReg  <~ Signal.mux start srcIp    siSig
    dstIpReg  <~ Signal.mux start dstIp    diSig

    return ({ headerByte  := byteOut
            , headerValid := isEmitting
            , headerLast  := isLast
            } : Ipv4TxOut dom)

/-! ### IPv4 RX parser. -/

structure Ipv4RxOut (dom : DomainConfig) where
  srcIp     : Signal dom (BitVec 32)
  dstIp     : Signal dom (BitVec 32)
  proto     : Signal dom (BitVec 8)
  totalLen  : Signal dom (BitVec 16)
  /-- High for one cycle after the 20th header byte is
      latched. -/
  done      : Signal dom Bool
  /-- True iff checksum verifies AND Ver/IHL == 0x45.  Sampled
      together with `done`. -/
  headerOk  : Signal dom Bool

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (Ipv4RxOut dom) dom := ⟨⟩

@[inline] private def shiftIn32 {dom : DomainConfig}
    (acc : Signal dom (BitVec 32)) (b : Signal dom (BitVec 8)) :
    Signal dom (BitVec 32) :=
  (acc <<< (8#32 : BitVec 32)) ||| ((0#24 : BitVec 24) ++ b)

@[inline] private def shiftIn16 {dom : DomainConfig}
    (acc : Signal dom (BitVec 16)) (b : Signal dom (BitVec 8)) :
    Signal dom (BitVec 16) :=
  (acc <<< (8#16 : BitVec 16)) ||| ((0#8 : BitVec 8) ++ b)

def ipv4RxParser {dom : DomainConfig}
    (byte   : Signal dom (BitVec 8))
    (valid  : Signal dom Bool)
    (sopIp  : Signal dom Bool) :
    Ipv4RxOut dom :=
  circuit do
    let cnt      ← Signal.reg (0#5)
    let verIhlR  ← Signal.reg (0#8)
    let totLenR  ← Signal.reg (0#16)
    let protoR   ← Signal.reg (0#8)
    let chkR     ← Signal.reg (0#16)
    let srcR     ← Signal.reg (0#32)
    let dstR     ← Signal.reg (0#32)
    let doneR    ← Signal.reg false
    let okR      ← Signal.reg false

    let cntSig := (cnt : Signal dom (BitVec 5))
    -- Per-offset selectors (offset = cntSig; sopIp = offset 0).
    let p1  := (Signal.pure 1#5  : Signal dom (BitVec 5))
    let p2  := (Signal.pure 2#5  : Signal dom (BitVec 5))
    let p3  := (Signal.pure 3#5  : Signal dom (BitVec 5))
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
    -- offset 0 is the version/IHL byte (sopIp pulses high)
    let inVerIhl := sopIp
    let inTotLen := (((· == ·) <$> cntSig <*> p2) |||
                     ((· == ·) <$> cntSig <*> p3))
    let inProto  := (· == ·) <$> cntSig <*> p9
    let inChk    := (((· == ·) <$> cntSig <*> p10) |||
                     ((· == ·) <$> cntSig <*> p11))
    let inSrc    := (((· == ·) <$> cntSig <*> p12) |||
                     ((· == ·) <$> cntSig <*> p13) |||
                     ((· == ·) <$> cntSig <*> p14) |||
                     ((· == ·) <$> cntSig <*> p15))
    let inDst    := (((· == ·) <$> cntSig <*> p16) |||
                     ((· == ·) <$> cntSig <*> p17) |||
                     ((· == ·) <$> cntSig <*> p18) |||
                     ((· == ·) <$> cntSig <*> p19))
    let isLast   := (· == ·) <$> cntSig <*> p19

    let verIhlSig := (verIhlR : Signal dom (BitVec 8))
    let totLenSig := (totLenR : Signal dom (BitVec 16))
    let protoSig  := (protoR  : Signal dom (BitVec 8))
    let chkSig    := (chkR    : Signal dom (BitVec 16))
    let srcSig    := (srcR    : Signal dom (BitVec 32))
    let dstSig    := (dstR    : Signal dom (BitVec 32))
    let doneSig   := (doneR   : Signal dom Bool)
    let okSig     := (okR     : Signal dom Bool)

    let tlNext  := shiftIn16 totLenSig byte
    let chkNext := shiftIn16 chkSig    byte
    let srcNext := shiftIn32 srcSig    byte
    let dstNext := shiftIn32 dstSig    byte

    -- Counter: on sopIp set to 1; while valid increment; else hold.
    let cntInc := (· + ·) <$> cntSig <*> p1
    cnt <~ Signal.mux sopIp p1
            (Signal.mux valid cntInc cntSig)
    verIhlR <~ Signal.mux (valid &&& inVerIhl) byte verIhlSig
    totLenR <~ Signal.mux (valid &&& inTotLen) tlNext totLenSig
    protoR  <~ Signal.mux (valid &&& inProto)  byte protoSig
    chkR    <~ Signal.mux (valid &&& inChk)    chkNext chkSig
    srcR    <~ Signal.mux (valid &&& inSrc)    srcNext srcSig
    dstR    <~ Signal.mux (valid &&& inDst)    dstNext dstSig
    doneR   <~ valid &&& isLast

    -- Header verify: re-compute checksum and compare with the
    -- captured one.  Also check Ver/IHL == 0x45.  Sampled on
    -- the doneR-pulse cycle, NOT the isLast cycle — by then
    -- all field registers (chkR, totLenR, srcR, dstR, etc.)
    -- have latched the last byte and hold their final values.
    let pVerIhl := (Signal.pure 0x45#8 : Signal dom (BitVec 8))
    let verIhlOk := (· == ·) <$> verIhlSig <*> pVerIhl
    let computed := ipv4HeaderChecksumSig totLenSig protoSig srcSig dstSig
    -- The transmitted checksum was computed with the
    -- HeaderChecksum field = 0; the receiver's `chkSig` holds
    -- the value the sender put on the wire.  Recompute over
    -- the same inputs and compare against the captured chkSig.
    let chkOk := (· == ·) <$> computed <*> chkSig
    okR     <~ Signal.mux doneSig (verIhlOk &&& chkOk) okSig

    return ({ srcIp    := srcSig
            , dstIp    := dstSig
            , proto    := protoSig
            , totalLen := totLenSig
            , done     := doneSig
            , headerOk := okSig
            } : Ipv4RxOut dom)

end Sparkle.IP.Net.IPv4
