/-
  Sim test for IP.Net.UART.

  Two cross-checks:
  1. Pure-data round-trip: uartBytesToBits → uartBitsToBytes
     reconstructs the original byte list.
  2. HW loopback: feed `uartTxHW`'s output directly into
     `uartRxHW`'s input over many cycles and assert the RX
     engine eventually emits the same bytes (with the right
     valid pulses).

  We use bitDiv = 9 (i.e. 10 cycles per bit) to keep the
  simulation horizon short — the actual Tang Nano 50K design
  will use 99 (= 100MHz / 1Mbps).
-/

import IP.Net.UART

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Net.UART

namespace Sparkle.Tests.IP.Net.UARTTest

abbrev D := defaultDomain

def testPureData : IO Bool := do
  IO.println "=== UART pure-data ==="
  let mut ok := true
  let bytes : List UInt8 := [0x48, 0x69, 0x21]  -- "Hi!"
  let bits := uartBytesToBits bytes
  let expectedLen := bytes.length * 10
  if bits.length = expectedLen then
    IO.println s!"  ✓ encoded {bytes.length} bytes → {bits.length} bits (10 each)"
  else
    IO.println s!"  ✗ length = {bits.length} vs {expectedLen}"
    ok := false

  let decoded := uartBitsToBytes bits
  if decoded = bytes then
    IO.println s!"  ✓ pure round-trip: {bytes} = {decoded}"
  else
    IO.println s!"  ✗ round-trip mismatch: got {decoded}"
    ok := false

  -- Robustness: prepending idle-high bits doesn't break decoding.
  let withIdle := List.replicate 7 true ++ bits
  let decoded2 := uartBitsToBytes withIdle
  if decoded2 = bytes then
    IO.println "  ✓ leading idle bits ignored"
  else
    IO.println s!"  ✗ leading-idle decode wrong: {decoded2}"
    ok := false

  return ok

/-- Build a Signal that pulses `tx_valid` exactly once at cycle 1
    carrying the given byte.  After cycle 1 it goes low and the
    byte stream is irrelevant. -/
private def singleByteStimulus (b : UInt8) : Signal D Bool × Signal D (BitVec 8) :=
  let validS : Signal D Bool := ⟨fun t => decide (t = 1)⟩
  let byteS : Signal D (BitVec 8) := Signal.pure (BitVec.ofNat 8 b.toNat)
  (validS, byteS)

def testHwLoopback : IO Bool := do
  IO.println "\n=== UART HW loopback (TX → RX) ==="
  let mut ok := true

  -- Use a small divider so a byte takes 100 cycles instead of 1000.
  let bitDivS : Signal D (BitVec 16) := Signal.pure 9#16   -- 10 cycles per bit
  -- 10 bits/byte × 10 cycles = 100 cycles per byte; need a couple
  -- extra for the start-edge half-divider on RX and the emit
  -- pulse on RX (= ≈ 110 cycles total margin).
  let horizon := 200

  let (txValid, txByte) := singleByteStimulus 0x5A  -- 'Z'
  let tx := uartTxHW txByte txValid bitDivS
  let rx := uartRxHW tx.txLine bitDivS

  -- Sample rx_valid + rx_byte across the horizon.
  let mut firstValidCycle : Option Nat := none
  let mut decodedByte : Option (BitVec 8) := none
  for t in [0:horizon] do
    if rx.rxValid.val t then
      firstValidCycle := some t
      decodedByte := some (rx.rxByte.val t)
      break

  match firstValidCycle, decodedByte with
  | some c, some b =>
    IO.println s!"  RX emitted byte 0x{Nat.toDigits 16 b.toNat |> String.ofList} at cycle {c}"
    if b.toNat = 0x5A then
      IO.println "  ✓ HW loopback round-trips byte 0x5A"
    else
      IO.println s!"  ✗ mismatch: expected 0x5A, got 0x{Nat.toDigits 16 b.toNat |> String.ofList}"
      ok := false
  | _, _ =>
    IO.println s!"  ✗ no rx_valid pulse within {horizon} cycles"
    ok := false

  return ok

def main : IO Unit := do
  IO.println "╔════════════════════════════════════════╗"
  IO.println "║  IP.Net.UART — bit-level RX/TX        ║"
  IO.println "╚════════════════════════════════════════╝"
  let a ← testPureData
  let b ← testHwLoopback
  if a && b then
    IO.println "\nALL PASS"
  else
    IO.println "\nFAIL"
    IO.Process.exit 1

end Sparkle.Tests.IP.Net.UARTTest

section SynthesisChecks
open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Net.UART

private def synth_uartTx
    (txByte : Signal defaultDomain (BitVec 8))
    (txValid : Signal defaultDomain Bool)
    (bitDiv : Signal defaultDomain (BitVec 16)) :
    Signal defaultDomain Bool :=
  (uartTxHW txByte txValid bitDiv).txLine

private def synth_uartRx
    (rxLine : Signal defaultDomain Bool)
    (bitDiv : Signal defaultDomain (BitVec 16)) :
    Signal defaultDomain (BitVec 8) :=
  (uartRxHW rxLine bitDiv).rxByte

#synthesizeVerilog synth_uartTx
#synthesizeVerilog synth_uartRx

end SynthesisChecks
