/-
  Done-once-per-request JIT co-sim of `rfc6979HW` (generic harness
  `DoneHWJITHarness`) for the constant key d = 1.  Ports after `#sim`: inputs
  start = 0, z = 1..8; outputs k = 0..7, done = 8.

  Requests: hashes z (two message hashes, 0, 2^256 - 1, n + 5, 1) whose nonce is
  the pure-data `Rfc6979.rfc6979 1 z`.  z is held while busy; garbage drives it
  during idle cycles and gaps.  Checked per request: `done` exactly once (1 cycle
  wide), k at `done` = reference and unchanged until the next start, no `done`
  in the prologue or after the last request; latency window [1, 6000].  NOT
  checked: nonce retry (k ≥ n or k = 0), other keys.
-/
import IP.Crypto.SHA256
import IP.Crypto.Rfc6979
import IP.Crypto.Rfc6979HW
import Tests.IP.Crypto.DoneHWJITHarness
import Sparkle.Compiler.Elab

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Core.JIT
open Sparkle.IP.Crypto.Rfc6979HW
open Sparkle.Tests.IP.Crypto.DoneHW

namespace Sparkle.Tests.IP.Crypto.Rfc6979DoneHWJITTest

set_option maxRecDepth 100000
set_option maxHeartbeats 40000000

def nonceTop (start : Signal defaultDomain Bool) (z : Signal defaultDomain (BitVec 256)) :
    NonceOut defaultDomain :=
  rfc6979HW (BitVec.ofNat 256 1) start z

#sim nonceTop

def mkDut (h : JITHandle) : Dut where
  handle := h
  hold := true
  set := fun ins st => do
    JIT.setInput h 0 (if st then 1 else 0)
    setWords h 1 8 ins[0]!
  junk := fun seed => do
    JIT.setInput h 0 0
    setWords h 1 8 (garbage seed 1 256)
  read := do
    let k ← getWords h 0 8
    let done := (← JIT.getOutput h 8) != 0
    pure { done, outs := #[k] }

def spec : Spec := { name := "rfc6979HW(d=1)", minLat := 1, maxLat := 6000 }

def zOf (msg : String) : Nat := Id.run do
  let mut v : Nat := 0
  for w in Sparkle.IP.Crypto.SHA256.sha256OfBytes (bytesOf msg) do v := (v <<< 32) ||| w.toNat
  return v

def n : Nat := 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141

def request (z : Nat) : Req := { inputs := #[z], expect := some #[Sparkle.IP.Crypto.Rfc6979.rfc6979 1 z] }

def requests : Array Req := #[request (zOf "Satoshi Nakamoto"), request 0, request (2 ^ 256 - 1),
  request (zOf "All those moments will be lost in time, like tears in rain. Time to die..."),
  request (n + 5), request 1, request (zOf "Satoshi Nakamoto")]

def main : IO Unit := do
  IO.println "=== rfc6979HW — done-once-per-request JIT co-sim ==="
  (← IO.getStdout).flush
  let sim ← nonceTop.Sim.load
  let h := sim.handle
  let mut ok := true
  for gaps in [#[0], #[1, 4, 0, 7]] do
    ok := (← runCase (mkDut h) spec requests gaps) && ok
  IO.println "-- negative controls on the live design"
  ok := (← liveControls (mkDut h) spec requests) && ok
  JIT.destroy h
  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

end Sparkle.Tests.IP.Crypto.Rfc6979DoneHWJITTest
