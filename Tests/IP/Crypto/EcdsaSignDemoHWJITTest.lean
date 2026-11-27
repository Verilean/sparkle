/-
  JIT co-sim of the generated hardware for the UART top
  `EcdsaSignDemo.ecdsaSignDemo`: send d ‖ k ‖ z (96 bytes, big-endian)
  over `uartRx`, record the `uartTx` line, decode the 64 reply bytes
  r ‖ s, and compare with the pure-data `Secp256k1ECDSA.sign d k z`.

  Ports after `#sim` lowering: inputs uartRx = 0, bitDiv = 1;
  outputs uartTx = 0, signDone = 1.  bitDiv = 15 → 16 cycles per bit.
-/
import IP.Crypto.Proof.Secp256k1ECDSA
import IP.Crypto.EcdsaSignDemo
import Sparkle.Compiler.Elab
import Tests.IP.Crypto.SignHWJITHarness

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Core.JIT
open Sparkle.IP.Crypto.EcdsaSignDemo
open Sparkle.Tests.IP.Crypto.SignHWJIT

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
def cpb : Nat := bitDiv + 1
/-- cycles recorded after the last request byte: one signature (≈ 1.8 M) +
    64 reply bytes (10 bits each) with margin. -/
def cap : Nat := 4000000

def main : IO Unit := do
  IO.println "=== secp256k1 ecdsaSignDemo (UART top) — JIT co-sim vs Secp256k1ECDSA.sign ==="
  (← IO.getStdout).flush
  let sim ← load
  let h := sim.handle
  let d := 0xC9AFA9D845BA75166B5C215767B1D6934E50C3DB36E89B127B8A622B120F6721
  let k := 0x9E56F509196784D963D1C0A401510EE7ADA3DCC5DEE04B154BF61AF1D5A6DECE
  let z := 0xAF2BDBE1AA9B6EC1E2ADE1D694F41FC71A831D0268E9891562113D8A62ADD1BF
  JIT.reset h
  JIT.setInput h 1 (UInt64.ofNat bitDiv)
  -- one cycle with the given RX level; returns (uartTx, signDone) sampled before the edge
  let step (rx : Bool) : IO (Bool × Bool) := do
    JIT.setInput h 0 (if rx then 1 else 0)
    JIT.eval h
    let t ← JIT.getOutput h 0
    let sd ← JIT.getOutput h 1
    JIT.tick h
    pure (t != 0, sd != 0)
  for _ in [0:20] do let _ ← step true
  let sendByte (b : Nat) : IO Unit := do
    for _ in [0:cpb] do let _ ← step false
    for i in [0:8] do
      for _ in [0:cpb] do let _ ← step (((b >>> i) &&& 1) == 1)
    for _ in [0:cpb] do let _ ← step true
  for v in [d, k, z] do
    for i in [0:32] do sendByte ((v >>> (8 * (31 - i))) &&& 0xFF)
  let mut samples : Array Bool := Array.mkEmpty cap
  let mut doneAt : Option Nat := none
  for c in [0:cap] do
    let (t, sd) ← step true
    samples := samples.push t
    if sd && doneAt.isNone then doneAt := some c
  JIT.destroy h
  let bytes := Uart.decode samples cpb 64
  IO.println s!"  signDone after {doneAt} cycles from the last request byte; {bytes.size} reply bytes"
  let mut ok := true
  if bytes.size != 64 then
    IO.println s!"  ✗ expected 64 reply bytes within {cap} cycles"
    ok := false
  else
    let r := Uart.beNat bytes 0 32
    let s := Uart.beNat bytes 32 32
    match Sparkle.IP.Crypto.Secp256k1ECDSA.sign d k z with
    | some (er, es) =>
      if r == er && s == es then IO.println "  ✓ UART reply r‖s = reference"
      else
        IO.println s!"  ✗ got r={r}\n        s={s}\n    exp r={er}\n        s={es}"
        ok := false
    | none => IO.println "  ✗ reference none"; ok := false
  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

end Sparkle.Tests.IP.Crypto.EcdsaSignDemoHWJITTest
