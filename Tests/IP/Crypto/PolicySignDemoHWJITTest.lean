/-
  JIT co-sim of the generated hardware for the UART top
  `PolicySignDemo.policySignDemo` (milestone 1): send the 128-byte frame
  d ‖ k ‖ to ‖ value over `uartRx`, watch `uartTx` / `signDone` / `rejected`,
  and compare with the pure-data references
    z = keccak256(to ‖ value), policy = TxPolicy.policyRef, (r,s) = Secp256k1ECDSA.sign d k z.

  Accept path: reply is r ‖ s (64 bytes).  Refusal path: reply is the single
  byte 0xEE and `rejected` pulses (no signature, `signDone` stays low).

  KNOWN FAILURE — NOT IN CI.  The reply values are correct (r ‖ s and 0xEE match
  the references), but the design's TX streamer sends ONE EXTRA 0x00 frame after
  every reply and then a 1-cycle low glitch on `uartTx` (`txMore` in
  IP/Crypto/PolicySignDemo.lean tests the count before it is decremented, so
  `txBusy` stays up for one more byte).  This test fails on that until the
  design is fixed; the design was deliberately not touched here.

  Ports after `#sim` lowering: inputs uartRx = 0, bitDiv = 1;
  outputs uartTx = 0, signDone = 1, rejected = 2.
-/
import IP.Crypto.Proof.Keccak256
import IP.Crypto.Proof.Secp256k1ECDSA
import IP.Crypto.TxPolicy
import IP.Crypto.PolicySignDemo
import Sparkle.Compiler.Elab
import Tests.IP.Crypto.UartHWJITHarness

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Core.JIT
open Sparkle.IP.Crypto.PolicySignDemo
open Sparkle.Tests.IP.Crypto.UartHWJIT

namespace Sparkle.Tests.IP.Crypto.PolicySignDemoHWJITTest

set_option maxRecDepth 100000
set_option maxHeartbeats 40000000

/-- `#sim`-able top: the real policy-signing UART demo. -/
def policySignDemoTop
    (uartRx : Signal defaultDomain Bool)
    (bitDiv : Signal defaultDomain (BitVec 16)) : PolicyDemoOut defaultDomain :=
  policySignDemo uartRx bitDiv

#sim policySignDemoTop

open policySignDemoTop.Sim

def bitDiv : Nat := 15
/-- strobe watch: signDone = output 1 (index 0), rejected = output 2 (index 1) -/
def watch : Array Nat := #[1, 2]
/-- cycle cap per request (one signature ≈ 1.8 M cycles) -/
def cap : Nat := 3000000
/-- idle cycles after the last reply (≈ 62 byte times): any extra byte would show up -/
def tail : Nat := 10000

def d : Nat := 0xC9AFA9D845BA75166B5C215767B1D6934E50C3DB36E89B127B8A622B120F6721
def k : Nat := 0x9E56F509196784D963D1C0A401510EE7ADA3DCC5DEE04B154BF61AF1D5A6DECE

open Sparkle.IP.Crypto.TxPolicy in
/-- Reference for one request: the 128-byte frame and the expected (strobe index, reply). -/
def request (label : String) (toW valW : Nat) : Step :=
  let frame := beBytes d 32 ++ beBytes k 32 ++ beBytes toW 32 ++ beBytes valW 32
  let digest := Sparkle.IP.Crypto.Keccak256.keccak256OfBytes
    ((beBytes toW 32 ++ beBytes valW 32).map UInt8.ofNat)
  let z := digest.foldl (fun a b => (a <<< 8) ||| b.toNat) 0
  let ok := policyRef (BitVec.ofNat 160 toW) (BitVec.ofNat 256 valW)
  if ok then
    match Sparkle.IP.Crypto.Secp256k1ECDSA.sign d k z with
    | some (r, s) => { label, frame, strobe := 0, reply := beBytes r 32 ++ beBytes s 32 }
    | none => { label := label ++ " (reference sign = none)", frame, strobe := 0, reply := #[] }
  else
    { label, frame, strobe := 1, reply := #[0xEE] }

def main : IO Unit := do
  IO.println "=== policySignDemo (M1 UART top) — JIT co-sim vs keccak256 / policyRef / Secp256k1ECDSA.sign ==="
  (← IO.getStdout).flush
  let sim ← load
  let h := sim.handle
  let allow0 : Nat := 0x70997970C51812dc3A010C7d01b50e0d17dc79C8
  let allow3 : Nat := 0x15d34AAf54267DB7D7c367839AAf71A00a2C6A65
  let bad    : Nat := 0xdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef
  let underCap : Nat := 500000000000000000
  let maxV     : Nat := 1000000000000000000
  let mut ok := true
  -- Run A: accept path only (fresh reset).
  IO.println "-- run A: allowlisted recipient, under cap → r‖s"
  (← IO.getStdout).flush
  let bA ← Bench.create h bitDiv watch
  ok := (← runSteps bA #[request "accept allow0 / 0.5 ETH" allow0 underCap] cap tail) && ok
  -- Run B: refusals and a boundary accept, back to back on one reset.
  IO.println "-- run B: 3 refusals then the boundary accept (value == cap), no reset between"
  (← IO.getStdout).flush
  let bB ← Bench.create h bitDiv watch
  ok := (← runSteps bB #[
      request "refuse: allowlisted, 2 ETH over cap" allow0 (2 * maxV)
    , request "refuse: bad recipient, under cap" bad underCap
    , request "refuse: allowlisted, cap+1 wei" allow3 (maxV + 1)
    , request "accept: allowlisted, value == cap" allow3 maxV] cap tail) && ok
  JIT.destroy h
  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

end Sparkle.Tests.IP.Crypto.PolicySignDemoHWJITTest
