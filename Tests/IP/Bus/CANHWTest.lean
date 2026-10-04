/-
  Sim test for IP.Bus.CANHW.crc15HW.

  Feed a known bit list into the HW LFSR one bit per cycle
  (start pulse cycle 0, valid = 1 for cycles 1..N).  The
  register at cycle N+1 should equal `IP.Bus.CAN.crc15` on
  the same list.

  Synth check via #synthesizeVerilog at the bottom.
-/

import IP.Bus.CAN
import IP.Bus.CANHW

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Bus.CANHW
open Sparkle.IP.Bus.CAN (crc15)

namespace Sparkle.Tests.IP.Bus.CANHWTest

abbrev D := defaultDomain

/-- Build a Signal that emits the k-th element of `xs`
    starting at cycle 1, default at cycle 0 / past end. -/
private def listSig {α : Type} [Inhabited α] (xs : List α) (default0 : α) : Signal D α := Id.run do
  let arr := xs.toArray
  return ⟨fun t =>
    if t = 0 then default0
    else if h : t - 1 < arr.size then arr[t - 1]!
    else default0⟩

/-- Feed bits one per cycle (offset by 1, since cycle 0 is
    the start pulse).  The HW samples on cycle k+1 the value
    of bitIn we put at cycle k+1; with valid=true the LFSR
    register at cycle k+2 has consumed it. -/
def main : IO Unit := do
  IO.println "=== CAN CRC-15 HW vs pure-data ==="

  let mut ok := true

  -- A representative bit sequence: the CRC-covered region of
  -- a known CAN frame (1 byte payload).  Hand-picked to test
  -- a non-trivial run with both 0s and 1s.
  let bits : List Bool :=
    [false,                                 -- SOF
     true, true, false, true, false, false, true, false, true, false, false, -- ID 0x7C5 (11 bits, MSB-first; spaced for clarity)
     false,                                 -- RTR = 0
     false,                                 -- IDE = 0
     false,                                 -- r0
     false, false, false, true,             -- DLC = 1
     true, false, true, false, true, false, true, false]  -- 1-byte payload 0xAA

  let expected := crc15 bits
  IO.println s!"  pure-data crc15 = 0x{Nat.toDigits 16 expected |> String.ofList} ({bits.length} input bits)"

  -- Build start/valid/bitIn signals.  Cycle 0: start pulse.
  -- Cycles 1..bits.length: valid + bitIn from the list.
  let startSig : Signal D Bool := ⟨fun t => decide (t = 0)⟩
  let bitInSig := listSig bits false
  let validSig : Signal D Bool :=
    ⟨fun t => decide (t ≥ 1 ∧ t ≤ bits.length)⟩

  let engine := crc15HW startSig bitInSig validSig

  -- The LFSR at cycle (bits.length + 1) should hold the final CRC.
  let sampleAt := bits.length + 1
  IO.println s!"  sampling crc.val {sampleAt}..."
  let crcHw := engine.crc.val sampleAt
  IO.println s!"  HW crc           = 0x{Nat.toDigits 16 crcHw.toNat |> String.ofList}"

  if crcHw.toNat = expected then
    IO.println "  ✓ HW CRC-15 matches pure-data implementation"
  else
    IO.println "  ✗ mismatch"
    ok := false

  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

end Sparkle.Tests.IP.Bus.CANHWTest

section SynthesisChecks
open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Bus.CANHW

private def synth_canCrc15
    (start : Signal defaultDomain Bool)
    (bitIn : Signal defaultDomain Bool)
    (valid : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 15) :=
  (crc15HW start bitIn valid).crc

#synthesizeVerilog synth_canCrc15

end SynthesisChecks
