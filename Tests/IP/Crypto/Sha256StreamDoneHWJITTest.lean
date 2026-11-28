/-
  Done-once-per-request JIT co-sim of `sha256StreamHW` (generic harness
  `DoneHWJITHarness`).  Ports after `#sim`: inputs start = 0, nBlocks = 1,
  blk0 = 2..17, blk1 = 18..33; outputs hash = 0..7, done = 8.

  Requests: messages of 0..119 bytes (1 or 2 padded blocks) whose digest is
  `sha256OfBytes`.  The operands are held while busy (the documented protocol);
  garbage drives every input during idle cycles and between requests.  Checked
  per request: `done` exactly once (1 cycle wide), hash at `done` = reference and
  unchanged until the next start, no `done` in the prologue or after the last
  request; latency window [1, 400], per message length identical latency (not
  required across lengths).  NOT checked: operands changing while busy.
-/
import IP.Crypto.SHA256
import IP.Crypto.SHA256Stream
import Tests.IP.Crypto.DoneHWJITHarness
import Sparkle.Compiler.Elab

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Core.JIT
open Sparkle.IP.Crypto.SHA256
open Sparkle.IP.Crypto.SHA256Stream
open Sparkle.Tests.IP.Crypto.DoneHW

namespace Sparkle.Tests.IP.Crypto.Sha256StreamDoneHWJITTest

set_option maxRecDepth 100000
set_option maxHeartbeats 40000000

def streamTop (start : Signal defaultDomain Bool) (nBlocks : Signal defaultDomain (BitVec 2))
    (blk0 blk1 : Signal defaultDomain (BitVec 512)) : StreamOut defaultDomain :=
  sha256StreamHW start nBlocks blk0 blk1

#sim streamTop

def refDigest (msg : Array UInt8) : Nat := Id.run do
  let mut v : Nat := 0
  for w in sha256OfBytes msg do v := (v <<< 32) ||| w.toNat
  return v

def mkDut (h : JITHandle) : Dut where
  handle := h
  hold := true
  set := fun ins st => do
    JIT.setInput h 0 (if st then 1 else 0)
    JIT.setInput h 1 (UInt64.ofNat ins[0]!)
    setWords h 2 16 ins[1]!
    setWords h 18 16 ins[2]!
  junk := fun seed => do
    JIT.setInput h 0 0
    JIT.setInput h 1 (UInt64.ofNat (garbage seed 1 2))
    setWords h 2 16 (garbage seed 2 512)
    setWords h 18 16 (garbage seed 3 512)
  read := do
    let hash ← getWords h 0 8
    let done := (← JIT.getOutput h 8) != 0
    pure { done, outs := #[hash] }

def spec : Spec := { name := "sha256StreamHW", minLat := 1, maxLat := 400 }

def requests (msgs : Array (Array UInt8)) : Array Req :=
  msgs.map fun m =>
    let b := padBlocks m
    { inputs := #[b.length, b.getD 0 0, b.getD 1 0], expect := some #[refDigest m] }

def msgs : Array (Array UInt8) := #[
  #[], bytesOf "abc", Array.replicate 55 0x61, Array.replicate 56 0x62, Array.replicate 64 0x63,
  bytesOf "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq", Array.replicate 119 0x64,
  Array.replicate 1 0xFF, bytesOf "abc", Array.replicate 100 0x65]

def main : IO Unit := do
  IO.println "=== sha256StreamHW — done-once-per-request JIT co-sim ==="
  (← IO.getStdout).flush
  let sim ← streamTop.Sim.load
  let h := sim.handle
  let mut ok := true
  let reqs := requests msgs
  for gaps in [#[0], #[1, 4, 0, 7], #[20]] do
    ok := (← runCase (mkDut h) spec reqs gaps) && ok
  IO.println "-- negative controls on the live design"
  ok := (← liveControls (mkDut h) spec reqs) && ok
  JIT.destroy h
  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

end Sparkle.Tests.IP.Crypto.Sha256StreamDoneHWJITTest
