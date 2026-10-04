/-
  Sim test for IP.Net.IPv4.{ipv4TxBuilder, ipv4RxParser}.

  Two scenarios:
    * TX: drive a builder with srcIp=10.0.0.10, dstIp=10.0.0.20,
      proto=ICMP, totalLen=84 (20 header + 64 payload).  Capture
      20 emitted header bytes; verify they match the hand-built
      reference, including the computed checksum at offsets 10-11.

    * RX: feed the same 20 header bytes into the parser.  After
      the run, srcIp / dstIp / proto / totalLen should match,
      done should pulse, and headerOk should be true.
-/

import IP.Net.IPv4
import Sparkle

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Net.IPv4

namespace Sparkle.Tests.IP.Net.IPv4Test

private def srcIp : BitVec 32 := 0x0A00000A#32   -- 10.0.0.10
private def dstIp : BitVec 32 := 0x0A000014#32   -- 10.0.0.20
private def proto : BitVec 8  := 0x01#8          -- ICMP
private def totLen : BitVec 16 := 84#16          -- 20 + 64 payload

/-! ### Reference: build the 20 header bytes the spec says. -/

private def headerBytesNoChksum : List (BitVec 8) :=
  [ 0x45#8, 0x00#8                              -- Ver/IHL, DSCP
  , BitVec.extractLsb' 8 8 totLen, BitVec.extractLsb' 0 8 totLen
  , 0x00#8, 0x00#8                              -- Identification
  , 0x40#8, 0x00#8                              -- Flags=DF, FragOffset
  , 0x40#8                                       -- TTL=64
  , proto                                        -- Protocol
  , 0x00#8, 0x00#8                              -- HeaderChecksum (placeholder)
  -- SrcIP (4) + DstIP (4)
  , BitVec.extractLsb' 24 8 srcIp, BitVec.extractLsb' 16 8 srcIp
  , BitVec.extractLsb'  8 8 srcIp, BitVec.extractLsb'  0 8 srcIp
  , BitVec.extractLsb' 24 8 dstIp, BitVec.extractLsb' 16 8 dstIp
  , BitVec.extractLsb'  8 8 dstIp, BitVec.extractLsb'  0 8 dstIp ]

private def chksum : BitVec 16 :=
  ipv4HeaderChecksum totLen 0#16 0x4000#16
    (0x4000#16 ||| (BitVec.zeroExtend 16 proto))
    -- The Sig form uses 0x4000 | proto rather than (TTL<<8|proto);
    -- normalise here.  Actually: the pure-data API takes ttlProto
    -- already-OR'd.  Use TTL=0x40 explicitly:
    -- Note: the Sig form passes the same combined value as
    -- `0x4000 ||| zext proto`, but the wire-correct combination is
    -- (TTL<<8) | Proto = 0x4001 for ICMP TTL=64.  We match the Sig
    -- form's behaviour.
    srcIp dstIp

/-- Reference header with chksum inserted at offsets 10..11. -/
private def expectedHeader : List (BitVec 8) :=
  let hi := BitVec.extractLsb' 8 8 chksum
  let lo := BitVec.extractLsb' 0 8 chksum
  let head := headerBytesNoChksum.take 10
  let tail := headerBytesNoChksum.drop 12
  head ++ [hi, lo] ++ tail

/-! ### TX stimulus. -/

private def srcIpSig : Signal defaultDomain (BitVec 32) := ⟨fun _ => srcIp⟩
private def dstIpSig : Signal defaultDomain (BitVec 32) := ⟨fun _ => dstIp⟩
private def protoSig : Signal defaultDomain (BitVec 8)  := ⟨fun _ => proto⟩
private def totLenSig : Signal defaultDomain (BitVec 16) := ⟨fun _ => totLen⟩
private def startSig : Signal defaultDomain Bool := ⟨fun t => decide (t = 0)⟩

private def txOut : Ipv4TxOut defaultDomain :=
  ipv4TxBuilder totLenSig protoSig srcIpSig dstIpSig startSig

/-! ### RX stimulus: feed the expectedHeader bytes back in. -/

private def rxByte : Signal defaultDomain (BitVec 8) :=
  ⟨fun t =>
    if t < 20 then (expectedHeader[t]?).getD 0#8 else 0#8⟩
private def rxValid : Signal defaultDomain Bool :=
  ⟨fun t => decide (t < 20)⟩
private def sopIp : Signal defaultDomain Bool :=
  ⟨fun t => decide (t = 0)⟩

private def rxOut : Ipv4RxOut defaultDomain :=
  ipv4RxParser rxByte rxValid sopIp

def main : IO Unit := do
  IO.println "=== IPv4 TX builder + RX parser sim ==="

  -- TX: capture emitted bytes during cycles 0..19 (headerValid).
  let mut txBytes : List (BitVec 8) := []
  for h : t in [:25] do
    let v := txOut.headerValid.val t
    let b := txOut.headerByte.val t
    if v then txBytes := txBytes ++ [b]
  IO.println s!"  TX: emitted {txBytes.length} bytes (expected 20)"
  let txOk := txBytes = expectedHeader
  if txOk then
    IO.println "    TX bytes ✓ match expected header (incl. checksum)"
  else
    IO.println "    TX bytes ✗ mismatch"
    IO.println s!"      got: {txBytes.map BitVec.toNat}"
    IO.println s!"      exp: {expectedHeader.map BitVec.toNat}"

  -- RX: after the 20 input bytes plus the 1-cycle done latency,
  -- check parsed fields.
  let sampleAt : Nat := 22
  let parsedSrc := rxOut.srcIp.val sampleAt
  let parsedDst := rxOut.dstIp.val sampleAt
  let parsedProto := rxOut.proto.val sampleAt
  let parsedTotLen := rxOut.totalLen.val sampleAt
  let parsedOk := rxOut.headerOk.val sampleAt
  IO.println s!"  RX@cycle{sampleAt}: srcIp=0x{Nat.toDigits 16 parsedSrc.toNat |> String.ofList} (expected 0x0a00000a)"
  IO.println s!"           dstIp=0x{Nat.toDigits 16 parsedDst.toNat |> String.ofList} (expected 0x0a000014)"
  IO.println s!"           proto={parsedProto.toNat} (expected 1)"
  IO.println s!"           totalLen={parsedTotLen.toNat} (expected 84)"
  IO.println s!"           headerOk={parsedOk} (expected true)"
  let rxOk := parsedSrc = srcIp ∧ parsedDst = dstIp
            ∧ parsedProto = proto ∧ parsedTotLen = totLen ∧ parsedOk = true

  if txOk ∧ rxOk then
    IO.println "\nALL PASS"
  else
    IO.println "\nFAIL"
    IO.Process.exit 1

end Sparkle.Tests.IP.Net.IPv4Test

section SynthesisChecks
-- Build-time synth checks for the IPv4 TX builder and RX
-- parser.  Both depend on `ipv4HeaderChecksumSig` which used
-- to fail to synthesize through a user-defined-binary-op
-- Applicative lift.  Re-expressing the checksum compute in
-- terms of Signal-native primitives (concat, +, slice) and
-- chaining the per-add steps as plain function calls (no
-- `<$> <*>` over a non-primitive function head) unblocks the
-- elaborator — see `onesAdd16Sig`.

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Net.IPv4

private def synth_ipv4TxByte
    (totalLen : Signal defaultDomain (BitVec 16))
    (proto    : Signal defaultDomain (BitVec 8))
    (srcIp dstIp : Signal defaultDomain (BitVec 32))
    (start    : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 8) :=
  (ipv4TxBuilder totalLen proto srcIp dstIp start).headerByte

#synthesizeVerilog synth_ipv4TxByte

private def synth_ipv4RxSrcIp
    (byte  : Signal defaultDomain (BitVec 8))
    (valid sopIp : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 32) :=
  (ipv4RxParser byte valid sopIp).srcIp

#synthesizeVerilog synth_ipv4RxSrcIp

private def synth_ipv4RxHeaderOk
    (byte  : Signal defaultDomain (BitVec 8))
    (valid sopIp : Signal defaultDomain Bool) :
    Signal defaultDomain Bool :=
  (ipv4RxParser byte valid sopIp).headerOk

#synthesizeVerilog synth_ipv4RxHeaderOk

end SynthesisChecks
