/-
  Sim test for IP.Net.SLIP.

  1. Pure-data: encodeFrame / decodeStream round-trip with edge
     cases (END/ESC bytes inside payload, back-to-back frames,
     empty payload).
  2. HW round-trip: slipFramerHW → byte stream → slipDeframerHW,
     assert the deframer's outByte stream + frameDone pulse
     reconstruct the original IP packet bytes.
  3. Synth: #synthesizeVerilog on both engines.
-/

import IP.Net.SLIP

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Net.SLIP

namespace Sparkle.Tests.IP.Net.SLIPTest

abbrev D := defaultDomain

def testPureData : IO Bool := do
  IO.println "=== SLIP pure-data ==="
  let mut ok := true

  -- A trivial 3-byte packet, no escaping.
  let p1 : List UInt8 := [0x48, 0x69, 0x21]   -- "Hi!"
  let f1 := encodeFrame p1
  let expected1 : List UInt8 := [0xC0, 0x48, 0x69, 0x21, 0xC0]
  if f1 = expected1 then
    IO.println s!"  ✓ simple frame: {f1}"
  else
    IO.println s!"  ✗ simple frame: got {f1}, expected {expected1}"
    ok := false

  -- Payload containing END (0xC0) and ESC (0xDB).
  let p2 : List UInt8 := [0x01, 0xC0, 0x02, 0xDB, 0x03]
  let f2 := encodeFrame p2
  let expected2 : List UInt8 := [0xC0, 0x01, 0xDB, 0xDC, 0x02, 0xDB, 0xDD, 0x03, 0xC0]
  if f2 = expected2 then
    IO.println s!"  ✓ escape encoding: {f2}"
  else
    IO.println s!"  ✗ escape encoding: got {f2}, expected {expected2}"
    ok := false

  -- Round-trip: encode then decode gives the same payload.
  let dec1 := decodeStream f1
  if dec1 = [p1] then
    IO.println "  ✓ round-trip simple"
  else
    IO.println s!"  ✗ round-trip simple: {dec1}"
    ok := false
  let dec2 := decodeStream f2
  if dec2 = [p2] then
    IO.println "  ✓ round-trip with escaping"
  else
    IO.println s!"  ✗ round-trip with escaping: {dec2}"
    ok := false

  -- Two back-to-back frames, no inter-frame filler.
  let combined := f1 ++ f2
  let dec3 := decodeStream combined
  if dec3 = [p1, p2] then
    IO.println "  ✓ back-to-back frames decoded as 2 packets"
  else
    IO.println s!"  ✗ back-to-back: {dec3}"
    ok := false

  -- Leading filler ENDs should be ignored.
  let withFiller := [0xC0, 0xC0, 0xC0] ++ f1
  let dec4 := decodeStream withFiller
  if dec4 = [p1] then
    IO.println "  ✓ leading END filler ignored"
  else
    IO.println s!"  ✗ leading END filler: {dec4}"
    ok := false

  return ok

/-- A test signal that drives a sequence of bytes one per cycle,
    with `valid` pulsed when each byte is present.  After the
    list is exhausted the byte is whatever default & valid=false. -/
private def byteStreamSig (bs : List UInt8) :
    Signal D (BitVec 8) × Signal D Bool :=
  let arr := bs.toArray
  let byteS : Signal D (BitVec 8) :=
    ⟨fun t =>
      if h : t < arr.size then BitVec.ofNat 8 arr[t]!.toNat else 0#8⟩
  let validS : Signal D Bool :=
    ⟨fun t => decide (t < arr.size)⟩
  (byteS, validS)

def testHwLoopback : IO Bool := do
  IO.println "\n=== SLIP HW framer → deframer loopback ==="
  let mut ok := true

  -- Send a small payload through framer, capture wire bytes,
  -- feed them through deframer, assert reconstructed bytes
  -- match.  Use payload containing both END and ESC so the
  -- escaping path is exercised.
  let payload : List UInt8 := [0x10, 0xC0, 0x20, 0xDB, 0x30]
  IO.println s!"  payload bytes: {payload}"

  -- Stimulus: present each payload byte for several cycles to
  -- give the framer time to emit + escape (framer takes 1 or 2
  -- cycles per byte; we use 4 cycles per byte as slack).
  let stretchFactor := 4
  let stretched := payload.flatMap (fun b => List.replicate stretchFactor b)
  -- payloadValid is high only on the FIRST cycle of each
  -- 4-cycle slot — simpler stim to drive the framer's pulse-edge
  -- behaviour while keeping the byte stable.
  let payloadByteS : Signal D (BitVec 8) :=
    let arr := stretched.toArray
    ⟨fun t =>
      if h : t < arr.size then BitVec.ofNat 8 arr[t]!.toNat else 0#8⟩
  let payloadValidS : Signal D Bool :=
    ⟨fun t =>
      -- Pulse valid for one cycle at the start of each slot,
      -- but only inside the payload window.  Also need a small
      -- delay (cycle 1+) so the framer's idle→body transition
      -- has settled.
      let inWindow := t ≥ 2 ∧ t < 2 + payload.length * stretchFactor
      let slotStart := (t - 2) % stretchFactor = 0
      decide (inWindow ∧ slotStart)⟩
  let frameEndS : Signal D Bool :=
    ⟨fun t => decide (t = 2 + payload.length * stretchFactor + 2)⟩

  let framer := slipFramerHW payloadByteS payloadValidS frameEndS

  -- Loopback: pipe framer.txByte / txValid directly into deframer.
  let deframer := slipDeframerHW framer.txByte framer.txValid

  -- Sample the deframer over a long enough horizon.
  let horizon := 2 + payload.length * stretchFactor + 20
  let mut decoded : List Nat := []
  let mut sawFrameDone := false
  for t in [0:horizon] do
    if deframer.outValid.val t then
      decoded := decoded ++ [(deframer.outByte.val t).toNat]
    if deframer.frameDone.val t then
      sawFrameDone := true

  let expected := payload.map UInt8.toNat
  if decoded = expected then
    IO.println s!"  ✓ HW loopback reconstructs payload: {decoded}"
  else
    IO.println s!"  ✗ HW decoded {decoded} ≠ expected {expected}"
    ok := false

  if sawFrameDone then
    IO.println "  ✓ frameDone pulsed"
  else
    IO.println "  ✗ frameDone never pulsed within horizon"
    ok := false

  return ok

def main : IO Unit := do
  IO.println "╔════════════════════════════════════════╗"
  IO.println "║  IP.Net.SLIP — RFC 1055 framer/deframer ║"
  IO.println "╚════════════════════════════════════════╝"
  let a ← testPureData
  let b ← testHwLoopback
  if a && b then
    IO.println "\nALL PASS"
  else
    IO.println "\nFAIL"
    IO.Process.exit 1

end Sparkle.Tests.IP.Net.SLIPTest

section SynthesisChecks
open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Net.SLIP

private def synth_slipFramerByte
    (pb : Signal defaultDomain (BitVec 8))
    (pv : Signal defaultDomain Bool)
    (fe : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 8) :=
  (slipFramerHW pb pv fe).txByte

private def synth_slipDeframerByte
    (rb : Signal defaultDomain (BitVec 8))
    (rv : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 8) :=
  (slipDeframerHW rb rv).outByte

#synthesizeVerilog synth_slipFramerByte
#synthesizeVerilog synth_slipDeframerByte

end SynthesisChecks
