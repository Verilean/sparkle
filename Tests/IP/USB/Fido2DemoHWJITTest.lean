/-
  JIT co-sim of the generated hardware for the UART top `Fido2Demo.fido2Demo`
  (FIDO2 getAssertion): send the 133-byte frame d ‖ authenticatorData(37) ‖
  clientDataHash(32) ‖ k over `uartRx`, watch `uartTx` / `assertionDone`, and
  compare with the pure-data reference
    (r,s) = P256ECDSA.sign d k (SHA-256 (authData ‖ cdh)).

  There is no refusal path in this design (it signs every frame it receives);
  the second request uses different authenticatorData / clientDataHash / d / k to
  show the result follows the frame, not a constant.  Interface driven: the
  UART bridge only (not CTAPHID/USB reports, not CBOR).

  Checked by `UartHWJITHarness.runSteps` (in CI, group crypto-hw): every bit
  slot of every frame held for all its cycles, the exact reply per request with
  no extra frame and no frame in the idle tail, and per request window the
  named strobe exactly once and every other watched strobe not at all.  This
  test found the extra 0x00 frame after every reply (`txMore` in
  IP/USB/Fido2Demo.lean tested the count before the decrement) and the 1-cycle low glitch after
  each stop bit (`uartTxHW` shifted in 0); both are fixed in the design.

  Ports after `#sim` lowering: inputs uartRx = 0, bitDiv = 1;
  outputs uartTx = 0, assertionDone = 1.
-/
import IP.Crypto.Proof.P256ECDSA
import IP.Crypto.Codec.CTAP2Data
import IP.Crypto.SHA256
import IP.USB.Fido2Demo
import Sparkle.Compiler.Elab
import Tests.IP.Crypto.UartHWJITHarness

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Core.JIT
open Sparkle.IP.USB.Fido2Demo
open Sparkle.IP.Crypto
open Sparkle.Tests.IP.Crypto.UartHWJIT

namespace Sparkle.Tests.IP.USB.Fido2DemoHWJITTest

set_option maxRecDepth 100000
set_option maxHeartbeats 40000000

/-- `#sim`-able top: the real FIDO2 getAssertion UART demo. -/
def fido2DemoTop
    (uartRx : Signal defaultDomain Bool)
    (bitDiv : Signal defaultDomain (BitVec 16)) : Fido2DemoOut defaultDomain :=
  fido2Demo uartRx bitDiv

#sim fido2DemoTop

open fido2DemoTop.Sim

def bitDiv : Nat := 15
/-- strobe watch: assertionDone = output 1 (index 0) -/
def watch : Array Nat := #[1]
def cap : Nat := 3000000
def tail : Nat := 10000

private def sha256Bytes (input : Array UInt8) : Array UInt8 := Id.run do
  let mut out : Array UInt8 := #[]
  for w in SHA256.sha256OfBytes input do
    for i in [:4] do out := out.push (UInt8.ofNat ((w.toNat >>> ((3-i)*8)) &&& 0xFF))
  return out

/-- One getAssertion request: frame and the expected r‖s. -/
def request (label : String) (d k : Nat) (rpId : String) (signCount : Nat)
    (cdhByte : UInt8) : Step :=
  let rpIdHash := sha256Bytes rpId.toUTF8.toList.toArray
  let authData := CTAP2Data.authenticatorData rpIdHash CTAP2Data.flagsGetAssertion signCount none
  let cdh := Array.replicate 32 cdhByte
  let z := P256ECDSA.digestToNat (sha256Bytes (authData ++ cdh))
  let frame := beBytes d 32 ++ (authData.map UInt8.toNat) ++ (cdh.map UInt8.toNat) ++ beBytes k 32
  match P256ECDSA.sign d k z with
  | some (r, s) => { label, frame, strobe := 0, reply := beBytes r 32 ++ beBytes s 32 }
  | none => { label := label ++ " (reference sign = none)", frame, strobe := 0, reply := #[] }

def main : IO Unit := do
  IO.println "=== fido2Demo (UART top) — JIT co-sim vs P256ECDSA.sign (SHA-256 authData‖cdh) ==="
  (← IO.getStdout).flush
  let sim ← load
  let h := sim.handle
  let d1 : Nat := 0xC9AFA9D845BA75166B5C215767B1D6934E50C3DB36E89B127B8A622B120F6721
  let k1 : Nat := 0x9E56F509196784D963D1C0A401510EE7ADA3DCC5DEE04B154BF61AF1D5A6DECE
  let d2 : Nat := 0x1234567890ABCDEF1234567890ABCDEF1234567890ABCDEF1234567890ABCDEF
  let k2 : Nat := 0xA6E3C57DD01ABE90086538398355DD4C3B17AA873382B0F24D6129493D8AAD60
  let b ← Bench.create h bitDiv watch
  IO.println "-- two getAssertion requests back to back (second after the first reply drained)"
  (← IO.getStdout).flush
  let ok ← runSteps b #[
      request "assertion 1 (example.com, signCount 1)" d1 k1 "example.com" 1 0xAB
    , request "assertion 2 (other.org, signCount 7, other d/k/cdh)" d2 k2 "other.org" 7 0x5C] cap tail
  JIT.destroy h
  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

end Sparkle.Tests.IP.USB.Fido2DemoHWJITTest
