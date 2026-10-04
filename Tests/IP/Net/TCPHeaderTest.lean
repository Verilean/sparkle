/-
  Sim test for IP.Net.TCP header parser + checksum.

  Build a hand-rolled 20-byte TCP header (SYN packet style),
  compute its pseudo-header-inclusive checksum at the
  pure-data layer, feed the 20 bytes through `tcpRxParser`,
  and assert every parsed field round-trips.
-/

import IP.Net.TCP
import Sparkle

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Net.TCP

namespace Sparkle.Tests.IP.Net.TCPHeaderTest

private def srcIP : BitVec 32 := 0x0A00000A#32   -- 10.0.0.10
private def dstIP : BitVec 32 := 0x0A000014#32   -- 10.0.0.20

private def srcPort : BitVec 16 := 0xC000#16     -- ephemeral client
private def dstPort : BitVec 16 := 0x0050#16     -- HTTP (80)
private def seqNum  : BitVec 32 := 0xDEADBEEF#32
private def ackNum  : BitVec 32 := 0#32          -- SYN: no ack yet
private def dataOffFlags : BitVec 16 :=
  -- DataOffset = 5 (5 dwords), Flags = SYN (0x02)
  (5#4 ++ (0#3 : BitVec 3) ++ (0#1 : BitVec 1) ++ (0#8 : BitVec 8)) ||| 0x0002#16
private def window  : BitVec 16 := 0x4000#16
private def urgent  : BitVec 16 := 0#16
private def tcpLen  : BitVec 16 := 20#16         -- header only, no payload

private def chksum : BitVec 16 :=
  tcpHeaderChecksum srcIP dstIP tcpLen
    srcPort dstPort seqNum ackNum
    dataOffFlags window urgent

/-! ### Reference 20-byte header bytes. -/

private def headerBytes : List (BitVec 8) :=
  [ BitVec.extractLsb' 8 8 srcPort, BitVec.extractLsb' 0 8 srcPort
  , BitVec.extractLsb' 8 8 dstPort, BitVec.extractLsb' 0 8 dstPort
  , BitVec.extractLsb' 24 8 seqNum, BitVec.extractLsb' 16 8 seqNum
  , BitVec.extractLsb'  8 8 seqNum, BitVec.extractLsb'  0 8 seqNum
  , BitVec.extractLsb' 24 8 ackNum, BitVec.extractLsb' 16 8 ackNum
  , BitVec.extractLsb'  8 8 ackNum, BitVec.extractLsb'  0 8 ackNum
  , BitVec.extractLsb'  8 8 dataOffFlags, BitVec.extractLsb' 0 8 dataOffFlags
  , BitVec.extractLsb'  8 8 window, BitVec.extractLsb' 0 8 window
  , BitVec.extractLsb'  8 8 chksum, BitVec.extractLsb' 0 8 chksum
  , BitVec.extractLsb'  8 8 urgent, BitVec.extractLsb' 0 8 urgent ]

/-! ### Parser stimulus. -/
private def rxByte : Signal defaultDomain (BitVec 8) :=
  ⟨fun t => if t < 20 then (headerBytes[t]?).getD 0#8 else 0#8⟩
private def rxValid : Signal defaultDomain Bool :=
  ⟨fun t => decide (t < 20)⟩
private def sopTcp : Signal defaultDomain Bool :=
  ⟨fun t => decide (t = 0)⟩

private def rxOut : TcpRxOut defaultDomain :=
  tcpRxParser rxByte rxValid sopTcp

def main : IO Unit := do
  IO.println "=== TCP header parser sim ==="
  let sampleAt : Nat := 22
  let psrc := rxOut.srcPort.val sampleAt
  let pdst := rxOut.dstPort.val sampleAt
  let pseq := rxOut.seqNum.val sampleAt
  let pack := rxOut.ackNum.val sampleAt
  let pdf  := rxOut.dataOffFlags.val sampleAt
  let pwnd := rxOut.window.val sampleAt
  let pchk := rxOut.chksum.val sampleAt
  let purg := rxOut.urgent.val sampleAt

  IO.println s!"  srcPort = 0x{Nat.toDigits 16 psrc.toNat |> String.ofList} (expected 0xc000)"
  IO.println s!"  dstPort = 0x{Nat.toDigits 16 pdst.toNat |> String.ofList} (expected 0x0050)"
  IO.println s!"  seqNum  = 0x{Nat.toDigits 16 pseq.toNat |> String.ofList} (expected 0xdeadbeef)"
  IO.println s!"  ackNum  = 0x{Nat.toDigits 16 pack.toNat |> String.ofList} (expected 0x00000000)"
  IO.println s!"  flags   = 0x{Nat.toDigits 16 pdf.toNat |> String.ofList} (SYN bit should be set)"
  IO.println s!"  window  = 0x{Nat.toDigits 16 pwnd.toNat |> String.ofList} (expected 0x4000)"
  IO.println s!"  chksum  = 0x{Nat.toDigits 16 pchk.toNat |> String.ofList} (reference 0x{Nat.toDigits 16 chksum.toNat |> String.ofList})"
  IO.println s!"  urgent  = 0x{Nat.toDigits 16 purg.toNat |> String.ofList} (expected 0x0000)"

  let ok := psrc = srcPort ∧ pdst = dstPort ∧ pseq = seqNum
          ∧ pack = ackNum ∧ pdf = dataOffFlags ∧ pwnd = window
          ∧ pchk = chksum ∧ purg = urgent

  -- Also check SYN flag bit specifically.
  let synBit := (BitVec.extractLsb' 0 8 pdf) &&& flagSyn
  let synOk := synBit = flagSyn
  IO.println s!"  SYN bit  = {synBit.toNat} (expected 2)"

  if ok ∧ synOk then
    IO.println "\nALL PASS"
  else
    IO.println "\nFAIL"
    IO.Process.exit 1

end Sparkle.Tests.IP.Net.TCPHeaderTest

section SynthesisChecks

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Net.TCP

-- 20-byte byte mux: 10 inputs + 1 cnt → 1 byte.
private def synth_tcpHeaderByte
    (srcPort dstPort : Signal defaultDomain (BitVec 16))
    (seqNum ackNum : Signal defaultDomain (BitVec 32))
    (dataOffFlags window chksum urgent : Signal defaultDomain (BitVec 16))
    (cntSig : Signal defaultDomain (BitVec 5)) :
    Signal defaultDomain (BitVec 8) :=
  tcpHeaderByte srcPort dstPort seqNum ackNum
    dataOffFlags window chksum urgent cntSig

#synthesizeVerilog synth_tcpHeaderByte

-- Pseudo-header checksum sub-module.
private def synth_tcpChecksum
    (srcIP dstIP : Signal defaultDomain (BitVec 32))
    (tcpLen : Signal defaultDomain (BitVec 16))
    (srcPort dstPort : Signal defaultDomain (BitVec 16))
    (seqNum ackNum : Signal defaultDomain (BitVec 32))
    (dataOffFlags window urgent : Signal defaultDomain (BitVec 16)) :
    Signal defaultDomain (BitVec 16) :=
  tcpHeaderChecksumSig srcIP dstIP tcpLen
    srcPort dstPort seqNum ackNum
    dataOffFlags window urgent

#synthesizeVerilog synth_tcpChecksum

-- RX parser: project the seqNum / dataOffFlags outputs.
private def synth_tcpRxSeq
    (byte : Signal defaultDomain (BitVec 8))
    (valid sopTcp : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 32) :=
  (tcpRxParser byte valid sopTcp).seqNum

#synthesizeVerilog synth_tcpRxSeq

private def synth_tcpRxFlags
    (byte : Signal defaultDomain (BitVec 8))
    (valid sopTcp : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 16) :=
  (tcpRxParser byte valid sopTcp).dataOffFlags

#synthesizeVerilog synth_tcpRxFlags

end SynthesisChecks
