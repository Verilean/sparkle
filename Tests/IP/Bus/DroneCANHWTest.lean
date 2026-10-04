/-
  Sim test for IP.Bus.DroneCANHW.crc16CcittHW +
  transferIdTrackerHW.

  Behavioural: feed a known byte list into the HW LFSR and
  compare against `IP.Bus.DroneCAN.crc16Ccitt`.  Also
  exercises the transfer-ID / toggle-bit tracker.

  Synth check via #synthesizeVerilog at the bottom (single-
  output scalar wrappers).
-/

import IP.Bus.DroneCAN
import IP.Bus.DroneCANHW

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Bus.DroneCANHW
open Sparkle.IP.Bus.DroneCAN (crc16Ccitt)

namespace Sparkle.Tests.IP.Bus.DroneCANHWTest

abbrev D := defaultDomain

def main : IO Unit := do
  IO.println "=== DroneCAN CRC-16-CCITT HW vs pure-data ==="

  let mut ok := true

  -- 7-byte NodeStatus payload (uptime=1, health=ok=0, mode=operational=0,
  --   subMode=0, vendorCode=0).
  let bytes : Array UInt8 := #[0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]

  let expected := crc16Ccitt bytes
  IO.println s!"  pure-data crc16 = 0x{Nat.toDigits 16 expected |> String.ofList} ({bytes.size} bytes)"

  let startSig : Signal D Bool := ⟨fun t => decide (t = 0)⟩
  let byteInSig : Signal D (BitVec 8) :=
    ⟨fun t =>
      if t = 0 then 0#8
      else if h : t - 1 < bytes.size then BitVec.ofNat 8 bytes[t - 1]!.toNat
      else 0#8⟩
  let validSig : Signal D Bool :=
    ⟨fun t => decide (t ≥ 1 ∧ t ≤ bytes.size)⟩

  let engine := crc16CcittHW startSig byteInSig validSig
  let sampleAt := bytes.size + 1
  let crcHw := engine.crc.val sampleAt
  IO.println s!"  HW crc          = 0x{Nat.toDigits 16 crcHw.toNat |> String.ofList}"

  if crcHw.toNat = expected then
    IO.println "  ok HW CRC-16-CCITT matches pure-data implementation"
  else
    IO.println "  MISMATCH"
    ok := false

  -- Transfer-ID tracker: single-frame transfer (SOT+EOT on
  -- cycle 1) then a two-frame transfer starting on cycle 3
  -- (SOT, valid, toggle=false) with a mid-frame on cycle 4
  -- (toggle=true).  No error expected.
  IO.println ""
  IO.println "-- transfer-id tracker --"
  let tidSig : Signal D (BitVec 5) := ⟨fun t =>
    if t = 1 then 5#5
    else if t = 3 then 9#5
    else if t = 4 then 9#5
    else 0#5⟩
  let togSig : Signal D Bool := ⟨fun t =>
    -- SOT frames must present toggle=false to satisfy
    -- tracker semantics (expected starts at false on SOT).
    if t = 4 then true else false⟩
  let sotSig : Signal D Bool := ⟨fun t => decide (t = 1 ∨ t = 3)⟩
  let eotSig : Signal D Bool := ⟨fun t => decide (t = 1 ∨ t = 4)⟩
  let vSig   : Signal D Bool := ⟨fun t => decide (t ≥ 1 ∧ t ≤ 4)⟩

  let tracker := transferIdTrackerHW tidSig togSig sotSig eotSig vSig
  -- After cycle 4 (the mid-frame with toggle=true, tid=9), the
  -- tracker's error signal should still be false.
  let errCycle5 := tracker.error.val 5
  IO.println s!"  error at cycle 5 = {errCycle5}"
  if errCycle5 then
    IO.println "  UNEXPECTED: error should be clear on a valid mid-frame"
    ok := false
  else
    IO.println "  ok tracker sees no error on well-formed transfer"

  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

end Sparkle.Tests.IP.Bus.DroneCANHWTest

section SynthesisChecks
open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Bus.DroneCANHW

private def synth_droneCanCrc16
    (start : Signal defaultDomain Bool)
    (byteIn : Signal defaultDomain (BitVec 8))
    (valid : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 16) :=
  (crc16CcittHW start byteIn valid).crc

#synthesizeVerilog synth_droneCanCrc16

private def synth_droneCanNodeFilter
    (srcNode selfNode : Signal defaultDomain (BitVec 7)) :
    Signal defaultDomain Bool :=
  (nodeFilterHW srcNode selfNode).accept

#synthesizeVerilog synth_droneCanNodeFilter

private def synth_droneCanTidError
    (tid : Signal defaultDomain (BitVec 5))
    (tog sot eot valid : Signal defaultDomain Bool) :
    Signal defaultDomain Bool :=
  (transferIdTrackerHW tid tog sot eot valid).error

#synthesizeVerilog synth_droneCanTidError

end SynthesisChecks
