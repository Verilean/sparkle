/-
  JIT co-sim of the generated hardware for the UART top
  `EcdsaSignDemo.ecdsaSignDemo`: send d ‖ k ‖ z (96 bytes, big-endian)
  over `uartRx`, record the whole `uartTx` line, decode it like a receiver
  (`UartHWJITHarness.runSteps`: every cycle of every bit slot, glitches,
  exactly 64 reply bytes and no extra frame for 10000 idle cycles after the
  reply, `signDone` exactly once per request window) and compare r ‖ s with the pure-data
  `Secp256k1ECDSA.sign d k z`.  Two requests back to back.

  Ports after `#sim` lowering: inputs uartRx = 0, bitDiv = 1;
  outputs uartTx = 0, signDone = 1.  bitDiv = 15 → 16 cycles per bit.
-/
import IP.Crypto.Proof.Secp256k1ECDSA
import IP.Crypto.EcdsaSignDemo
import Sparkle.Compiler.Elab
import Tests.IP.Crypto.UartHWJITHarness

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Core.JIT
open Sparkle.IP.Crypto.EcdsaSignDemo
open Sparkle.Tests.IP.Crypto.UartHWJIT

namespace Sparkle.Tests.IP.Crypto.EcdsaSignDemoHWJITTest

set_option maxRecDepth 100000
set_option maxHeartbeats 40000000

/-- `#sim`-able top: the real UART demo, outputs uartTx / signDone. -/
def ecdsaSignDemoTop
    (uartRx : Signal defaultDomain Bool)
    (bitDiv : Signal defaultDomain (BitVec 16)) : DemoOut defaultDomain :=
  ecdsaSignDemo uartRx bitDiv

#sim ecdsaSignDemoTop

open ecdsaSignDemoTop.Sim

def bitDiv : Nat := 15
/-- strobe watch: signDone = output 1 (index 0) -/
def watch : Array Nat := #[1]
/-- cycles allowed per request after its last byte: one signature (≈ 1.8 M) +
    64 reply bytes (10 bits each) with margin. -/
def cap : Nat := 3000000
def tail : Nat := 10000

/-- One request d ‖ k ‖ z and the expected r ‖ s. -/
def request (label : String) (d k z : Nat) : Step :=
  let frame := beBytes d 32 ++ beBytes k 32 ++ beBytes z 32
  match Sparkle.IP.Crypto.Secp256k1ECDSA.sign d k z with
  | some (r, s) => { label, frame, strobe := 0, reply := beBytes r 32 ++ beBytes s 32 }
  | none => { label := label ++ " (reference sign = none)", frame, strobe := 0, reply := #[] }

def main : IO Unit := do
  IO.println "=== secp256k1 ecdsaSignDemo (UART top) — JIT co-sim vs Secp256k1ECDSA.sign ==="
  (← IO.getStdout).flush
  let sim ← load
  let h := sim.handle
  let b ← Bench.create h bitDiv watch
  let ok ← runSteps b #[
      request "sign 1" 0xC9AFA9D845BA75166B5C215767B1D6934E50C3DB36E89B127B8A622B120F6721
        0x9E56F509196784D963D1C0A401510EE7ADA3DCC5DEE04B154BF61AF1D5A6DECE
        0xAF2BDBE1AA9B6EC1E2ADE1D694F41FC71A831D0268E9891562113D8A62ADD1BF
    , request "sign 2 (other d/k/z)" 0x1234567890ABCDEF1234567890ABCDEF1234567890ABCDEF1234567890ABCDEF
        0xA6E3C57DD01ABE90086538398355DD4C3B17AA873382B0F24D6129493D8AAD60
        0x4B688DF40BCEDBE641DDB16FF0A1842D9C67EA1C3BF63F3E0471BAA664531D1A] cap tail
  JIT.destroy h
  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

end Sparkle.Tests.IP.Crypto.EcdsaSignDemoHWJITTest
