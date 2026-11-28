/-
  JIT co-sim of the generated hardware for the UART top
  `PolicySignDemoM2.policySignDemoM2` (real EIP-1559 preimage): send the
  264-byte frame d ‖ k ‖ to ‖ value ‖ keccak-padded preimage (136 B) over
  `uartRx`, watch `uartTx` / `signDone` / `rejected`, and compare with the
  pure-data references
    z = Eip1559Tx.signingHashNat tx, policy = TxPolicy.policyRef (on the
    dedicated to/value fields), (r,s) = Secp256k1ECDSA.sign d k z.

  Accept path: reply is r ‖ s (64 bytes).  Refusal path: reply is the single
  byte 0xEE and `rejected` pulses (no signature, `signDone` stays low).

  KNOWN FAILURE — NOT IN CI.  The reply values are correct, but the design's TX
  streamer sends ONE EXTRA 0x00 frame after every reply and then a 1-cycle low
  glitch on `uartTx` (`txMore` in IP/Crypto/PolicySignDemoM2.lean tests the
  count before it is decremented, so `txBusy` stays up for one more byte).
  This test fails on that until the design is fixed; the design was
  deliberately not touched here.

  Ports after `#sim` lowering: inputs uartRx = 0, bitDiv = 1;
  outputs uartTx = 0, signDone = 1, rejected = 2.
-/
import IP.Crypto.Codec.Eip1559Tx
import IP.Crypto.Proof.Secp256k1ECDSA
import IP.Crypto.TxPolicy
import IP.Crypto.PolicySignDemoM2
import Sparkle.Compiler.Elab
import Tests.IP.Crypto.UartHWJITHarness

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Core.JIT
open Sparkle.IP.Crypto.PolicySignDemoM2
open Sparkle.Tests.IP.Crypto.UartHWJIT

namespace Sparkle.Tests.IP.Crypto.PolicySignDemoM2HWJITTest

set_option maxRecDepth 100000
set_option maxHeartbeats 40000000

/-- `#sim`-able top: the real M2 policy-signing UART demo. -/
def policySignDemoM2Top
    (uartRx : Signal defaultDomain Bool)
    (bitDiv : Signal defaultDomain (BitVec 16)) : PolicyDemoM2Out defaultDomain :=
  policySignDemoM2 uartRx bitDiv

#sim policySignDemoM2Top

open policySignDemoM2Top.Sim

def bitDiv : Nat := 15
/-- strobe watch: signDone = output 1 (index 0), rejected = output 2 (index 1) -/
def watch : Array Nat := #[1, 2]
def cap : Nat := 3000000
def tail : Nat := 10000

def d : Nat := 0x59c6995e998f97a5a0044966f0945389dc9e86dae88c7a8412f4603b6b78690d
def k : Nat := 0x9E56F509196784D963D1C0A401510EE7ADA3DCC5DEE04B154BF61AF1D5A6DECE

/-- Keccak pad10*1 of a ≤135-byte message to one 136-byte rate block (the host's job). -/
def keccakPad136 (m : Array UInt8) : Array UInt8 := Id.run do
  let mut b := m.push 0x01
  while b.size < 136 do b := b.push 0
  b.set! 135 (b[135]! ||| 0x80)

open Sparkle.IP.Crypto.TxPolicy in
/-- Reference for one request: the 264-byte frame and the expected (strobe index, reply). -/
def request (label : String) (nonce toAddr valWei : Nat) : Step :=
  let tx : Sparkle.IP.Crypto.Eip1559Tx.Tx :=
    { chainId := 31337, nonce, maxPriorityFee := 1000000000,
      maxFee := 2000000000, gasLimit := 21000,
      to := (beBytes toAddr 20).map UInt8.ofNat, value := valWei,
      data := #[], accessList := Sparkle.IP.Crypto.Eip1559Tx.emptyAccessList }
  let pre := keccakPad136 (Sparkle.IP.Crypto.Eip1559Tx.signingPayload tx)
  let frame := beBytes d 32 ++ beBytes k 32 ++ beBytes toAddr 32 ++ beBytes valWei 32
                 ++ pre.map UInt8.toNat
  let z := Sparkle.IP.Crypto.Eip1559Tx.signingHashNat tx
  let ok := policyRef (BitVec.ofNat 160 toAddr) (BitVec.ofNat 256 valWei)
  if ok then
    match Sparkle.IP.Crypto.Secp256k1ECDSA.sign d k z with
    | some (r, s) => { label, frame, strobe := 0, reply := beBytes r 32 ++ beBytes s 32 }
    | none => { label := label ++ " (reference sign = none)", frame, strobe := 0, reply := #[] }
  else
    { label, frame, strobe := 1, reply := #[0xEE] }

def main : IO Unit := do
  IO.println "=== policySignDemoM2 (UART top) — JIT co-sim vs Eip1559Tx hash / policyRef / Secp256k1ECDSA.sign ==="
  (← IO.getStdout).flush
  let sim ← load
  let h := sim.handle
  let allow0 : Nat := 0x70997970C51812dc3A010C7d01b50e0d17dc79C8
  let allow3 : Nat := 0x15d34AAf54267DB7D7c367839AAf71A00a2C6A65
  let bad    : Nat := 0x000000000000000000000000000000000000dEaD
  let underCap : Nat := 500000000000000000
  let maxV     : Nat := 1000000000000000000
  let mut ok := true
  IO.println "-- run A: allowlisted recipient, under cap → r‖s"
  (← IO.getStdout).flush
  let bA ← Bench.create h bitDiv watch
  ok := (← runSteps bA #[request "accept allow0 / 0.5 ETH" 0 allow0 underCap] cap tail) && ok
  IO.println "-- run B: 3 refusals then the boundary accept (value == cap), no reset between"
  (← IO.getStdout).flush
  let bB ← Bench.create h bitDiv watch
  ok := (← runSteps bB #[
      request "refuse: allowlisted, 2 ETH over cap" 1 allow0 (2 * maxV)
    , request "refuse: bad recipient, under cap" 2 bad underCap
    , request "refuse: allowlisted, cap+1 wei" 3 allow3 (maxV + 1)
    , request "accept: allowlisted, value == cap" 4 allow3 maxV] cap tail) && ok
  JIT.destroy h
  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

end Sparkle.Tests.IP.Crypto.PolicySignDemoM2HWJITTest
