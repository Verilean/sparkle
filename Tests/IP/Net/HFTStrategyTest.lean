/-
  Sim test for IP.Net.HFTStrategy.hftStrategy.

  Scenario:
    * Feed an 18-byte HTTP GET request on the inbound stream
      starting at cycle 0.
    * Assert that the strategy's outbound emitter pulses
      `outValid` and produces the same 18 bytes
      "GET / HTTP/1.0\r\n\r\n" — but DELAYED by exactly 5
      cycles (parser + register pipeline).
    * Assert `emitCount` increments to 1.
    * Latency budget: first inbound byte at cycle 0,
      first outbound byte at cycle 5 → 5-cycle reaction.
-/

import IP.Net.HFTStrategy
import IP.Net.HTTP
import Sparkle

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Net.HFTStrategy
open Sparkle.IP.Net.HTTP

namespace Sparkle.Tests.IP.Net.HFTStrategyTest

private def inboundBytes : List (BitVec 8) :=
  -- "GET / HTTP/1.0\r\n\r\n" — 18 bytes
  [ 0x47#8, 0x45#8, 0x54#8, 0x20#8
  , 0x2F#8, 0x20#8
  , 0x48#8, 0x54#8, 0x54#8, 0x50#8, 0x2F#8
  , 0x31#8, 0x2E#8, 0x30#8
  , 0x0D#8, 0x0A#8, 0x0D#8, 0x0A#8 ]

private def inByte : Signal defaultDomain (BitVec 8) :=
  ⟨fun t => if t < 18 then (inboundBytes[t]?).getD 0#8 else 0#8⟩
private def inValid : Signal defaultDomain Bool :=
  ⟨fun t => decide (t < 18)⟩

private def out : HFTOut defaultDomain := hftStrategy inByte inValid

def main : IO Unit := do
  IO.println "=== HFT NIC-side strategy sim ==="

  -- Inspect each cycle and find when the FIRST outbound
  -- byte appears (txValid rises).
  let mut firstOutCycle : Option Nat := none
  let mut outBytes : List (BitVec 8) := []
  for h : t in [:40] do
    let v := out.outValid.val t
    let b := out.outByte.val t
    if v then
      outBytes := outBytes ++ [b]
      if firstOutCycle.isNone then firstOutCycle := some t
  let firstCycle := firstOutCycle.getD 0
  IO.println s!"  first outbound byte at cycle {firstCycle} (expected 5)"
  IO.println s!"  outbound bytes captured: {outBytes.length} (expected 18)"
  let bytesOk := outBytes = inboundBytes
  if bytesOk then
    IO.println "    ✓ outbound bytes match inbound (echoes \"GET / HTTP/1.0\\r\\n\\r\\n\")"
  else
    IO.println s!"    ✗ outbound mismatch: got {outBytes.map BitVec.toNat}"

  -- emitCount should be 1 after the trigger fired.
  let cntAt30 := out.emitCount.val 30
  IO.println s!"  emitCount at cycle 30 = {cntAt30.toNat} (expected 1)"

  -- The latency budget check: parser + register pipeline =
  -- 5 cycles.  Verify firstOutCycle is exactly 5.
  let latencyOk := firstCycle = 5
  if latencyOk then
    IO.println "    ✓ 5-cycle inbound→outbound reaction latency"
  else
    IO.println s!"    ✗ expected 5-cycle latency, got {firstCycle}"

  if bytesOk ∧ cntAt30 = 1#8 ∧ latencyOk then
    IO.println "\nALL PASS"
  else
    IO.println "\nFAIL"
    IO.Process.exit 1

end Sparkle.Tests.IP.Net.HFTStrategyTest

section SynthesisChecks

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Net.HFTStrategy

private def synth_hftOutByte
    (inByte : Signal defaultDomain (BitVec 8))
    (inValid : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 8) :=
  (hftStrategy inByte inValid).outByte

#synthesizeVerilog synth_hftOutByte

private def synth_hftEmitCount
    (inByte : Signal defaultDomain (BitVec 8))
    (inValid : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 8) :=
  (hftStrategy inByte inValid).emitCount

#synthesizeVerilog synth_hftEmitCount

private def synth_hftTriggerSeen
    (inByte : Signal defaultDomain (BitVec 8))
    (inValid : Signal defaultDomain Bool) :
    Signal defaultDomain Bool :=
  (hftStrategy inByte inValid).triggerSeen

#synthesizeVerilog synth_hftTriggerSeen

end SynthesisChecks
