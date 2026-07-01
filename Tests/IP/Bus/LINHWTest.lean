/-
  Sim test for IP.Bus.LINHW.{pidParityHW, checksumHW}.

  Behavioural check:
    * PID parity: sweep all 6-bit IDs and compare each cycle's
      combinational output against `IP.Bus.LIN.pidParity`.
    * Checksum: feed a short byte sequence and compare the
      final accumulator's inverse against
      `IP.Bus.LIN.computeChecksum`.

  Synth check via #synthesizeVerilog at the bottom.
-/

import IP.Bus.LIN
import IP.Bus.LINHW

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Bus.LINHW
open Sparkle.IP.Bus.LIN (pidParity computeChecksum)

namespace Sparkle.Tests.IP.Bus.LINHWTest

abbrev D := defaultDomain

def main : IO Unit := do
  IO.println "=== LIN HW (PID parity + checksum) vs pure-data ==="

  let mut ok := true

  -- PID parity: at cycle t the input is (t & 0x3F).
  IO.println "-- PID parity --"
  let idSig : Signal D (BitVec 6) := ⟨fun t => BitVec.ofNat 6 t⟩
  let pidOut := pidParityHW idSig
  for id in [:64] do
    let expected := pidParity id
    let hw := (pidOut.parity.val id).toNat
    if hw ≠ expected then
      IO.println s!"  MISMATCH id={id}: expected {expected}, hw {hw}"
      ok := false
  if ok then
    IO.println "  ok all 64 PIDs match"

  -- Checksum: bytes 0x01..0x08 (small sample).
  IO.println "-- checksum --"
  let bytes : Array UInt8 := #[0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08]
  let expectedChk := computeChecksum bytes
  IO.println s!"  pure-data chk = 0x{Nat.toDigits 16 expectedChk.toNat |> String.ofList}"

  let startSig : Signal D Bool := ⟨fun t => decide (t = 0)⟩
  let byteInSig : Signal D (BitVec 8) :=
    ⟨fun t =>
      if t = 0 then 0#8
      else if h : t - 1 < bytes.size then BitVec.ofNat 8 bytes[t - 1]!.toNat
      else 0#8⟩
  let validSig : Signal D Bool :=
    ⟨fun t => decide (t ≥ 1 ∧ t ≤ bytes.size)⟩

  let engine := checksumHW startSig byteInSig validSig
  let sampleAt := bytes.size + 1
  let chkHw := engine.chk.val sampleAt
  IO.println s!"  HW chk        = 0x{Nat.toDigits 16 chkHw.toNat |> String.ofList}"
  if chkHw.toNat = expectedChk.toNat then
    IO.println "  ok HW checksum matches pure-data implementation"
  else
    IO.println "  MISMATCH"
    ok := false

  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

end Sparkle.Tests.IP.Bus.LINHWTest

section SynthesisChecks
open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Bus.LINHW

private def synth_linPidParity
    (idIn : Signal defaultDomain (BitVec 6)) :
    Signal defaultDomain (BitVec 2) :=
  (pidParityHW idIn).parity

#synthesizeVerilog synth_linPidParity

private def synth_linChecksum
    (start : Signal defaultDomain Bool)
    (byteIn : Signal defaultDomain (BitVec 8))
    (valid : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 8) :=
  (checksumHW start byteIn valid).chk

#synthesizeVerilog synth_linChecksum

end SynthesisChecks
