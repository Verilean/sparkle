/-
  Sim test for IP.Bus.SPIHW.spiMasterHW.

  Behavioural: kick off a single-byte SPI transfer at mode 0
  (CPOL=0, CPHA=0), walk the FSM, and check that:
    * SCLK toggles multiple times.
    * CS drops on start and rises on completion.
    * `done` pulses once.

  Synth via #synthesizeVerilog on the SCLK output.
-/

import IP.Bus.SPI
import IP.Bus.SPIHW

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Bus.SPIHW

namespace Sparkle.Tests.IP.Bus.SPIHWTest

abbrev D := defaultDomain

def main : IO Unit := do
  IO.println "=== SPI HW master (single-byte, mode 0) ==="

  let mut ok := true

  let startSig : Signal D Bool := ⟨fun t => decide (t = 0)⟩
  let cpolSig : Signal D Bool := Signal.pure false
  let cphaSig : Signal D Bool := Signal.pure false
  -- bitDiv = 0 → tick every cycle for fast walk.
  let bitDivSig : Signal D (BitVec 16) := Signal.pure 0#16
  let mosiSig : Signal D (BitVec 8) := Signal.pure 0xA5#8
  -- Slave returns 0x5A pattern (per-cycle).
  let misoBitSig : Signal D Bool := ⟨fun t => t % 2 == 0⟩

  let master := spiMasterHW startSig cpolSig cphaSig bitDivSig mosiSig misoBitSig

  -- Walk 40 cycles.
  let mut sclkToggles := 0
  let mut prev := false
  let mut sawCsLow := false
  let mut sawCsHigh := false
  let mut sawDone := false
  for t in [:40] do
    let s := master.sclk.val t
    if t > 0 && s ≠ prev then sclkToggles := sclkToggles + 1
    prev := s
    if !(master.cs.val t) then sawCsLow := true
    if t > 5 && (master.cs.val t) then sawCsHigh := true
    if master.done.val t then sawDone := true

  IO.println s!"  SCLK toggles: {sclkToggles}"
  IO.println s!"  CS drop seen: {sawCsLow}"
  IO.println s!"  CS restore seen: {sawCsHigh}"
  IO.println s!"  done pulse seen: {sawDone}"

  if sclkToggles < 4 then IO.println "  UNEXPECTED: SCLK didn't toggle enough"; ok := false
  if !sawCsLow then IO.println "  UNEXPECTED: CS never asserted"; ok := false
  if !sawCsHigh then IO.println "  UNEXPECTED: CS never restored"; ok := false
  if !sawDone then IO.println "  UNEXPECTED: done never pulsed"; ok := false

  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

end Sparkle.Tests.IP.Bus.SPIHWTest

section SynthesisChecks
open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Bus.SPIHW

private def synth_spiSclk
    (start : Signal defaultDomain Bool)
    (cpol : Signal defaultDomain Bool)
    (cpha : Signal defaultDomain Bool)
    (bitDiv : Signal defaultDomain (BitVec 16))
    (mosiByte : Signal defaultDomain (BitVec 8))
    (misoBit : Signal defaultDomain Bool) :
    Signal defaultDomain Bool :=
  (spiMasterHW start cpol cpha bitDiv mosiByte misoBit).sclk

#synthesizeVerilog synth_spiSclk

private def synth_spiMisoByte
    (start : Signal defaultDomain Bool)
    (cpol : Signal defaultDomain Bool)
    (cpha : Signal defaultDomain Bool)
    (bitDiv : Signal defaultDomain (BitVec 16))
    (mosiByte : Signal defaultDomain (BitVec 8))
    (misoBit : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 8) :=
  (spiMasterHW start cpol cpha bitDiv mosiByte misoBit).misoByte

#synthesizeVerilog synth_spiMisoByte

end SynthesisChecks
