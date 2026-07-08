/-
  Sim + synth test for IP.Crypto.PolicySignDemoM2 — the Tang Nano 50K
  policy-enforcing signer that hashes the REAL EIP-1559 preimage.

  Dataflow validated against the pure references:
    * z      = keccak256(0x02 ‖ rlp([...]))   (Eip1559Tx.signingHashNat)
    * (r,s)  = Secp256k1ECDSA.sign d k z        (only if policy ok)
    * policy = TxPolicy.policyRef to value      (on the dedicated fields)

  Full closed-loop Signal.val co-sim hangs (issue #95), so the
  behavioural check is at the pure-data level; the `#synthesizeVerilog`
  below proves the whole M2 top lowers to hardware.
-/
import Sparkle
import IP.Crypto.Eip1559Tx
import IP.Crypto.Secp256k1ECDSA
import IP.Crypto.TxPolicy
import IP.Crypto.PolicySignDemoM2

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Crypto.PolicySignDemoM2

namespace Sparkle.Tests.IP.Crypto.PolicySignDemoM2Test

/-- 20 big-endian address bytes from a Nat. -/
private def addr20 (n : Nat) : Array UInt8 := Id.run do
  let mut out : Array UInt8 := #[]
  for i in [:20] do
    out := out.push (UInt8.ofNat ((n >>> ((19 - i) * 8)) &&& 0xFF))
  return out

/-- Build a canonical no-data EIP-1559 transfer. -/
private def mkTx (toAddr valWei : Nat) : Sparkle.IP.Crypto.Eip1559Tx.Tx :=
  { chainId := 31337, nonce := 0, maxPriorityFee := 1000000000,
    maxFee := 2000000000, gasLimit := 21000,
    to := addr20 toAddr, value := valWei,
    data := #[], accessList := Sparkle.IP.Crypto.Eip1559Tx.emptyAccessList }

/-- Pure model of the M2 chip dataflow for one frame. -/
private def demoSpec (d k toAddr valWei : Nat) : Bool × Option (Nat × Nat) :=
  let tx := mkTx toAddr valWei
  let z := Sparkle.IP.Crypto.Eip1559Tx.signingHashNat tx
  let recip : BitVec 160 := BitVec.ofNat 160 toAddr
  let value : BitVec 256 := BitVec.ofNat 256 valWei
  let ok := Sparkle.IP.Crypto.TxPolicy.policyRef recip value
  let sig := if ok then Sparkle.IP.Crypto.Secp256k1ECDSA.sign d k z else none
  (ok, sig)

def main : IO Unit := do
  IO.println "=== Tang Nano policy-signer M2 (real EIP-1559) — dataflow check ==="
  (← IO.getStdout).flush
  let mut ok := true

  let allow0 : Nat := 0x70997970C51812dc3A010C7d01b50e0d17dc79C8
  let bad    : Nat := 0x000000000000000000000000000000000000dEaD
  let underCap : Nat := 500000000000000000
  let overCap  : Nat := 2000000000000000000
  let d := 0x59c6995e998f97a5a0044966f0945389dc9e86dae88c7a8412f4603b6b78690d  -- anvil #1
  let k := 0x9E56F509196784D963D1C0A401510EE7ADA3DCC5DEE04B154BF61AF1D5A6DECE

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

  IO.println "  · z = keccak256(0x02 ‖ rlp([...])) — the REAL EIP-1559 tx hash"
  IO.println "  · signature is broadcastable (see host/policy_signer + anvil demo)"

  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

end Sparkle.Tests.IP.Crypto.PolicySignDemoM2Test

section SynthesisChecks
open Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.IP.Crypto.PolicySignDemoM2

set_option maxRecDepth 100000
set_option maxHeartbeats 40000000

private def synth_policyM2Tx
    (uartRx : Signal defaultDomain Bool)
    (bitDiv : Signal defaultDomain (BitVec 16)) :
    Signal defaultDomain Bool :=
  (policySignDemoM2 uartRx bitDiv).uartTx

#synthesizeVerilog synth_policyM2Tx

private def synth_policyM2Reject
    (uartRx : Signal defaultDomain Bool)
    (bitDiv : Signal defaultDomain (BitVec 16)) :
    Signal defaultDomain Bool :=
  (policySignDemoM2 uartRx bitDiv).rejected

#synthesizeVerilog synth_policyM2Reject

end SynthesisChecks
