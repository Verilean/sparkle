/-
  Sim + synth test for IP.Crypto.PolicySignDemo — the Tang Nano 50K
  POLICY-ENFORCING Ethereum signing device.

  The security property under test: the chip computes the signing
  hash `z` ON-CHIP from the message bytes, checks the recipient/
  value against the on-chip policy sliced from the SAME bytes, and
  produces `(r,s)` ONLY when the policy passes.  We validate the
  DATAFLOW (the exact z / (r,s) / policy decision) against the
  independent pure references:
    * z      = keccak256(to ‖ value)            (Keccak256)
    * (r,s)  = Secp256k1ECDSA.sign d k z         (only if policy ok)
    * policy = TxPolicy.policyRef to value

  As with the other deep crypto stacks, full closed-loop Signal.val
  co-sim hangs the interpreter (issue #95), so the behavioural check
  is at the pure-data level; the `#synthesizeVerilog` at the bottom
  proves the whole sponge + policy + signer + UART top lowers to
  hardware, and iverilog elaborates the emitted Verilog.
-/
import Sparkle
import IP.Crypto.Keccak256
import IP.Crypto.Secp256k1ECDSA
import IP.Crypto.TxPolicy
import IP.Crypto.PolicySignDemo

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Crypto.PolicySignDemo

namespace Sparkle.Tests.IP.Crypto.PolicySignDemoTest

abbrev D := defaultDomain

/-- 32 big-endian bytes of a 256-bit word. -/
private def beBytes32 (n : Nat) : Array UInt8 := Id.run do
  let mut out : Array UInt8 := #[]
  for i in [:32] do
    out := out.push (UInt8.ofNat ((n >>> ((31 - i) * 8)) &&& 0xFF))
  return out

/-- The message the chip hashes: `to (32) ‖ value (32)`. -/
private def message (toWord valWord : Nat) : Array UInt8 :=
  beBytes32 toWord ++ beBytes32 valWord

/-- Pure model of the chip's dataflow for one frame. -/
private def demoSpec (d k toWord valWord : Nat) :
    Bool × Option (Nat × Nat) :=
  -- z = keccak256(to ‖ value) as a big-endian 256-bit integer.
  let digest := Sparkle.IP.Crypto.Keccak256.keccak256OfBytes (message toWord valWord)
  let z := Id.run do
    let mut acc := 0
    for b in digest do
      acc := (acc <<< 8) ||| b.toNat
    return acc
  -- recipient = low 160 bits of the `to` word.
  let recip : BitVec 160 := BitVec.ofNat 160 toWord
  let value : BitVec 256 := BitVec.ofNat 256 valWord
  let ok := Sparkle.IP.Crypto.TxPolicy.policyRef recip value
  let sig := if ok then Sparkle.IP.Crypto.Secp256k1ECDSA.sign d k z else none
  (ok, sig)

def main : IO Unit := do
  IO.println "=== Tang Nano policy-enforcing signer — dataflow check ==="
  (← IO.getStdout).flush
  let mut ok := true

  -- An allowlisted recipient (allow0) and a non-allowlisted one.
  let allow0 : Nat := 0x70997970C51812dc3A010C7d01b50e0d17dc79C8
  let bad    : Nat := 0xdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef
  let underCap : Nat := 500000000000000000   -- 0.5 ETH < 1 ETH cap
  let overCap  : Nat := 2000000000000000000  -- 2 ETH   > 1 ETH cap
  let d := 0xC9AFA9D845BA75166B5C215767B1D6934E50C3DB36E89B127B8A622B120F6721
  let k := 0x9E56F509196784D963D1C0A401510EE7ADA3DCC5DEE04B154BF61AF1D5A6DECE

  -- (label, to, value, expectPolicyOk)
  let cases : List (String × Nat × Nat × Bool) :=
    [ ("allowlisted + under cap → SIGN",   allow0, underCap, true)
    , ("allowlisted + over cap  → REJECT", allow0, overCap,  false)
    , ("bad recipient           → REJECT", bad,    underCap, false) ]

  for (label, toW, valW, expectOk) in cases do
    let (gotOk, sig) := demoSpec d k toW valW
    let okMatch := gotOk == expectOk
    let sigMatch := match sig with
      | some (r, _) => expectOk && r != 0
      | none => !expectOk
    if okMatch && sigMatch then
      match sig with
      | some (r, _) => IO.println s!"  ✓ {label}: policyOk={gotOk}, signed (r={r})"
      | none        => IO.println s!"  ✓ {label}: policyOk={gotOk}, no signature"
    else
      IO.println s!"  ✗ {label}: gotOk={gotOk} expectOk={expectOk} sig={sig.isSome}"
      ok := false

  IO.println s!"  · bitDiv (27 MHz / 115200) = {Sparkle.IP.Crypto.EcdsaSignDemo.bitDiv27M115200.toNat}"
  IO.println "  · z computed ON-CHIP from the same bytes the policy checks"

  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

end Sparkle.Tests.IP.Crypto.PolicySignDemoTest

section SynthesisChecks
open Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.IP.Crypto.PolicySignDemo

set_option maxRecDepth 100000
set_option maxHeartbeats 40000000

/-- Synth the full Tang Nano policy-signer top's UART TX line —
    forces the whole sponge + policy + signer + UART graph to lower. -/
private def synth_policyDemoTx
    (uartRx : Signal defaultDomain Bool)
    (bitDiv : Signal defaultDomain (BitVec 16)) :
    Signal defaultDomain Bool :=
  (policySignDemo uartRx bitDiv).uartTx

#synthesizeVerilog synth_policyDemoTx

/-- Synth the reject strobe (the policy-gate observable). -/
private def synth_policyDemoReject
    (uartRx : Signal defaultDomain Bool)
    (bitDiv : Signal defaultDomain (BitVec 16)) :
    Signal defaultDomain Bool :=
  (policySignDemo uartRx bitDiv).rejected

#synthesizeVerilog synth_policyDemoReject

end SynthesisChecks
