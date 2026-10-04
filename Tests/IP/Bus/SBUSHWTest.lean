/-
  Sim test for IP.Bus.SBUSHW.frameAccumulatorHW.

  Feed a hand-built 25-byte S.BUS frame one byte per cycle
  and check:
    * headerOk latches on cycle 2 (register lag on hdr detected in cycle 1).
    * footerOk fires when we sample cycle after byte 24 arrived.
    * ch0 equals the pure-data unpackChannels[0] once byte1 and byte2 are latched.

  Synth via #synthesizeVerilog (single-scalar wrappers).
-/

import IP.Bus.SBUS
import IP.Bus.SBUSHW

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Bus.SBUSHW
open Sparkle.IP.Bus.SBUS (packChannels unpackChannels headerByte footerByte encodeFlags)

namespace Sparkle.Tests.IP.Bus.SBUSHWTest

abbrev D := defaultDomain

def main : IO Unit := do
  IO.println "=== SBUS HW frame accumulator vs pure-data ==="

  let mut ok := true

  -- Build a 25-byte frame with 16 channel values.  Only
  -- channel 0 is checked in HW (11-bit).
  let channels : Array Nat := (Array.range 16).map (fun i => 500 + i * 10)
  let chBytes := packChannels channels
  let frameBytes : Array UInt8 :=
    #[headerByte] ++ chBytes ++ #[encodeFlags false false false false, footerByte]

  IO.println s!"  frame size = {frameBytes.size}"

  -- Cycle 0 = start pulse (idx reset to 0).
  -- Cycles 1..25 = feed the 25 bytes.
  let startSig : Signal D Bool := ⟨fun t => decide (t = 0)⟩
  let byteInSig : Signal D (BitVec 8) := ⟨fun t =>
    if t = 0 then 0#8
    else if h : t - 1 < frameBytes.size then BitVec.ofNat 8 frameBytes[t - 1]!.toNat
    else 0#8⟩
  let validSig : Signal D Bool := ⟨fun t => decide (t ≥ 1 ∧ t ≤ frameBytes.size)⟩

  let engine := frameAccumulatorHW startSig byteInSig validSig

  -- headerOk should be true starting cycle 2 (after byte 0 latched at cycle 1's edge)
  let hdrAt2 := engine.headerOk.val 2
  IO.println s!"  headerOk at cycle 2 = {hdrAt2}"
  if !hdrAt2 then
    IO.println "  UNEXPECTED: header should have been detected"
    ok := false
  else
    IO.println "  ok header detected"

  -- footerOk should pulse on cycle 25 (footer arrives with idx=24 and hdr latched)
  let ftrAt25 := engine.footerOk.val 25
  IO.println s!"  footerOk at cycle 25 = {ftrAt25}"
  if !ftrAt25 then
    IO.println "  UNEXPECTED: footer OK should have fired"
    ok := false
  else
    IO.println "  ok footer detected"

  -- ch0 after cycle 3 (byte1 latched at cycle 2, byte2 at cycle 3)
  -- so at cycle 4 both are visible in the registers.
  let expectedCh0 := (unpackChannels chBytes)[0]!
  let ch0Hw := engine.ch0.val 4
  IO.println s!"  ch0 pure = {expectedCh0}, HW = {ch0Hw.toNat}"
  if ch0Hw.toNat ≠ expectedCh0 then
    IO.println "  MISMATCH ch0"
    ok := false
  else
    IO.println "  ok ch0 matches"

  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

end Sparkle.Tests.IP.Bus.SBUSHWTest

section SynthesisChecks
open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Bus.SBUSHW

private def synth_sbusIdx
    (start : Signal defaultDomain Bool)
    (byteIn : Signal defaultDomain (BitVec 8))
    (valid : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 5) :=
  (frameAccumulatorHW start byteIn valid).idxOut

#synthesizeVerilog synth_sbusIdx

private def synth_sbusCh0
    (start : Signal defaultDomain Bool)
    (byteIn : Signal defaultDomain (BitVec 8))
    (valid : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 11) :=
  (frameAccumulatorHW start byteIn valid).ch0

#synthesizeVerilog synth_sbusCh0

end SynthesisChecks
