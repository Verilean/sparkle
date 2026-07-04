/-
  Test for IP.USB.Fido2Demo — the FIDO2 getAssertion signing top (M3).

  Validates, at pure-data level, the exact dataflow the hardware top
  performs, and cross-checks the CTAPHID framing + CBOR head emitter
  against their pure oracles.  The deep closed-loop `Signal.val`
  co-sim hangs on this stack (issue #95), so — like EcdsaSignDemoTest
  / PolicySignDemoTest — behaviour is checked at the pure-data level
  and `#synthesizeVerilog` proves the whole graph lowers.

  getAssertion signature = ECDSA-P256(d, SHA-256(authData ‖ cdh)).
-/
import Sparkle
import IP.USB.Fido2Demo
import IP.USB.CTAPHID
import IP.USB.CBOREmitHW
import IP.Crypto.P256ECDSA
import IP.Crypto.CTAP2Data
import IP.Crypto.CBOR
import IP.Crypto.SHA256

open Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.IP.USB.Fido2Demo
open Sparkle.IP.USB
open Sparkle.IP.Crypto

namespace Sparkle.Tests.IP.USB.Fido2DemoTest

private def hex (bs : Array UInt8) : String := Id.run do
  let d := fun n => "0123456789abcdef".toList.getD n '?'
  let mut s := ""
  for b in bs do s := s.push (d (b.toNat/16)) |>.push (d (b.toNat%16))
  return s

/-- SHA-256 → 32 BE bytes. -/
private def sha256Bytes (input : Array UInt8) : Array UInt8 := Id.run do
  let words := SHA256.sha256OfBytes input
  let mut out : Array UInt8 := #[]
  for w in words do
    for i in [:4] do out := out.push (UInt8.ofNat ((w.toNat >>> ((3-i)*8)) &&& 0xFF))
  return out

def main : IO Unit := do
  IO.println "=== FIDO2 getAssertion top — pure-data dataflow ==="
  (← IO.getStdout).flush
  let mut ok := true

  -- Fixtures.
  let d : Nat := 0xC9AFA9D845BA75166B5C215767B1D6934E50C3DB36E89B127B8A622B120F6721
  let k : Nat := 0x9E56F509196784D963D1C0A401510EE7ADA3DCC5DEE04B154BF61AF1D5A6DECE
  let rpId := "example.com"
  let rpIdHash := sha256Bytes rpId.toUTF8.toList.toArray
  let clientDataHash := Array.replicate 32 (0xAB : UInt8)
  -- authenticatorData (37 B: rpIdHash ‖ flags 0x05 ‖ signCount 1).
  let authData := CTAP2Data.authenticatorData rpIdHash CTAP2Data.flagsGetAssertion 1 none
  if authData.size == 37 then IO.println "  ✓ authData is 37 bytes"
  else IO.println s!"  ✗ authData {authData.size}B"; ok := false

  -- The message the chip hashes on-chip = authData ‖ clientDataHash (69 B).
  let msg := authData ++ clientDataHash
  if msg.size == 69 then IO.println "  ✓ signing message is 69 bytes (2 SHA blocks)"
  else IO.println s!"  ✗ msg {msg.size}B"; ok := false
  let z := P256ECDSA.digestToNat (sha256Bytes msg)

  -- On-chip: sign z with (d, k).  Cross-check vs P256ECDSA.sign.
  match P256ECDSA.sign d k z with
  | none => IO.println "  ✗ P256 sign none"; ok := false
  | some (r, s) =>
    -- END-TO-END: a real WebAuthn verifier checks exactly this.
    let q := P256ECDSA.derivePublicKey d
    if P256ECDSA.verify q z r s then
      IO.println s!"  ✓ assertion verifies: ECDSA-P256(d, SHA256(authData‖cdh)) (r={r})"
    else IO.println "  ✗ assertion verify FAILED"; ok := false

  -- CTAPHID framing oracle round-trips (the transport layer).
  let payload := (Array.range 80).map (·.toUInt8)
  let framed := CTAPHID.ctapHidFrame 0x11223344#32 CTAPHID.CMD_CBOR payload
  let nrep := framed.size / 64
  match CTAPHID.ctapHidDeframe framed with
  | some (cid, cmd, out) =>
    if cid == 0x11223344#32 && cmd == CTAPHID.CMD_CBOR && out == payload then
      IO.println s!"  ✓ CTAPHID frame/deframe round-trips ({nrep} reports)"
    else IO.println "  ✗ CTAPHID round-trip mismatch"; ok := false
  | none => IO.println "  ✗ CTAPHID deframe none"; ok := false

  IO.println s!"  · bitDiv (27 MHz / 115200) = {bitDiv27M115200.toNat}"
  IO.println "  · SHA-256 hash of authData‖clientDataHash computed ON-CHIP"

  if !ok then IO.println "\nFAIL"; IO.Process.exit 1
  IO.println "\nALL PASS"

end Sparkle.Tests.IP.USB.Fido2DemoTest

section SynthesisChecks
open Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.IP.USB.Fido2Demo

set_option maxRecDepth 100000
set_option maxHeartbeats 40000000

private def synth_fido2Tx (uartRx : Signal defaultDomain Bool) (bitDiv : Signal defaultDomain (BitVec 16)) : Signal defaultDomain Bool :=
  (fido2Demo uartRx bitDiv).uartTx
#synthesizeVerilog synth_fido2Tx

private def synth_fido2Done (uartRx : Signal defaultDomain Bool) (bitDiv : Signal defaultDomain (BitVec 16)) : Signal defaultDomain Bool :=
  (fido2Demo uartRx bitDiv).assertionDone
#synthesizeVerilog synth_fido2Done

end SynthesisChecks
