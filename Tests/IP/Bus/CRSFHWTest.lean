/-
  Sim test for IP.Bus.CRSFHW.crc8HW.

  Feed a known byte list into the HW LFSR one byte per cycle
  (start pulse cycle 0, valid = 1 for cycles 1..N).  The
  register at cycle N+1 should equal `IP.Bus.CRSF.crc8` on
  the same list.

  Synth check via #synthesizeVerilog at the bottom.
-/

import IP.Bus.CRSF
import IP.Bus.CRSFHW

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Bus.CRSFHW
open Sparkle.IP.Bus.CRSF (crc8)

namespace Sparkle.Tests.IP.Bus.CRSFHWTest

abbrev D := defaultDomain

/-- Build a Signal that emits the k-th element of `xs`
    starting at cycle 1, default at cycle 0 / past end. -/
private def listSig {α : Type} [Inhabited α] (xs : List α) (default0 : α) : Signal D α := Id.run do
  let arr := xs.toArray
  return ⟨fun t =>
    if t = 0 then default0
    else if h : t - 1 < arr.size then arr[t - 1]!
    else default0⟩

def main : IO Unit := do
  IO.println "=== CRSF CRC-8 HW vs pure-data ==="

  let mut ok := true

  -- Representative bytes: a short CRSF Link Statistics payload
  -- (type + 10 data bytes) — CRC is computed over these bytes.
  let bytes : List UInt8 :=
    [ 0x14                                    -- type = Link Stats
    , 0x60, 0x60, 0x64, 0x00                  -- up RSSI ×2, LQ, SNR
    , 0x00, 0x02, 0x02                        -- ant, mode, tx pwr
    , 0x60, 0x64, 0x00 ]                      -- dn RSSI, LQ, SNR

  let expected := crc8 bytes.toArray
  IO.println s!"  pure-data crc8 = 0x{Nat.toDigits 16 expected.toNat |> String.ofList} ({bytes.length} bytes)"

  -- Build start / valid / byteIn signals.  Cycle 0: start pulse.
  -- Cycles 1..bytes.length: valid + byteIn from the list.
  let startSig : Signal D Bool := ⟨fun t => decide (t = 0)⟩
  let byteInSig : Signal D (BitVec 8) :=
    let arr := bytes.toArray
    ⟨fun t =>
      if t = 0 then 0#8
      else if h : t - 1 < arr.size then BitVec.ofNat 8 arr[t - 1]!.toNat
      else 0#8⟩
  let validSig : Signal D Bool :=
    ⟨fun t => decide (t ≥ 1 ∧ t ≤ bytes.length)⟩

  let engine := crc8HW startSig byteInSig validSig

  let sampleAt := bytes.length + 1
  IO.println s!"  sampling crc.val {sampleAt}..."
  let crcHw := engine.crc.val sampleAt
  IO.println s!"  HW crc          = 0x{Nat.toDigits 16 crcHw.toNat |> String.ofList}"

  if crcHw.toNat = expected.toNat then
    IO.println "  ok HW CRC-8 matches pure-data implementation"
  else
    IO.println "  MISMATCH"
    ok := false

  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

end Sparkle.Tests.IP.Bus.CRSFHWTest

section SynthesisChecks
open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Bus.CRSFHW

private def synth_crsfCrc8
    (start : Signal defaultDomain Bool)
    (byteIn : Signal defaultDomain (BitVec 8))
    (valid : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 8) :=
  (crc8HW start byteIn valid).crc

#synthesizeVerilog synth_crsfCrc8

end SynthesisChecks
