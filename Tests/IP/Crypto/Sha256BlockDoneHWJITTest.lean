/-
  Done-once-per-request JIT co-sim of `sha256Block` (generic harness
  `DoneHWJITHarness`).  Ports after `#sim`: inputs start = 0, blockIn = 1..16,
  first = 17; outputs hash = 0..7, done = 8.

  Requests: single-block messages (0..55 bytes, `first` = 1) whose digest is
  `sha256OfBytes`; and 2- and 3-block messages whose last block is compared with
  `sha256OfBytes` (the intermediate blocks are only checked for the handshake).
  The block is held while busy (`hold`) or replaced by garbage (second pass);
  garbage also drives every input during idle cycles and gaps.  Checked per
  request: `done` exactly once (1 cycle wide) at the same latency every time,
  hash at `done` = reference and unchanged until the next start, no `done` in
  the prologue or after the last request.  Latency window [1, 80].

  NOT checked: the block-chained intermediate hash values, `first` = 0 on a
  fresh core.
-/
import IP.Crypto.SHA256
import Tests.IP.Crypto.DoneHWJITHarness
import Sparkle.Compiler.Elab

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Core.JIT
open Sparkle.IP.Crypto.SHA256
open Sparkle.Tests.IP.Crypto.DoneHW

namespace Sparkle.Tests.IP.Crypto.Sha256BlockDoneHWJITTest

set_option maxRecDepth 100000
set_option maxHeartbeats 40000000

def shaTop (start : Signal defaultDomain Bool) (blockIn : Signal defaultDomain (BitVec 512))
    (first : Signal defaultDomain Bool) : SHA256Out defaultDomain :=
  sha256Block start blockIn first

#sim shaTop

def refDigest (msg : Array UInt8) : Nat := Id.run do
  let mut v : Nat := 0
  for w in sha256OfBytes msg do v := (v <<< 32) ||| w.toNat
  return v

def mkDut (h : JITHandle) (hold : Bool) : Dut where
  handle := h
  hold := hold
  set := fun ins st => do
    JIT.setInput h 0 (if st then 1 else 0)
    setWords h 1 16 ins[0]!
    JIT.setInput h 17 (UInt64.ofNat ins[1]!)
  junk := fun seed => do
    JIT.setInput h 0 0
    setWords h 1 16 (garbage seed 1 512)
    JIT.setInput h 17 (UInt64.ofNat (seed / 4096 % 2))
  read := do
    let hash ← getWords h 0 8
    let done := (← JIT.getOutput h 8) != 0
    pure { done, outs := #[hash] }

def spec : Spec := { name := "sha256Block", minLat := 1, maxLat := 80, fixedLatency := true }

/-- Requests of a list of messages: every block is a request with `first` on the
    first one; only the last block's digest is compared. -/
def requests (msgs : Array (Array UInt8)) : Array Req := Id.run do
  let mut out := #[]
  for m in msgs do
    let blks := padBlocks m
    for i in [0:blks.length] do
      out := out.push { inputs := #[blks[i]!, if i == 0 then 1 else 0],
                        expect := if i + 1 == blks.length then some #[refDigest m] else none }
  return out

def msgs : Array (Array UInt8) := #[
  #[], bytesOf "abc", Array.replicate 55 0x61, Array.replicate 56 0x62, Array.replicate 100 0x63,
  bytesOf "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq", Array.replicate 150 0x64,
  Array.replicate 1 0xFF, bytesOf "abc"]

def main : IO Unit := do
  IO.println "=== sha256Block — done-once-per-request JIT co-sim ==="
  (← IO.getStdout).flush
  let sim ← shaTop.Sim.load
  let h := sim.handle
  let mut ok := true
  let reqs := requests msgs
  for hold in [true, false] do
    IO.println s!"-- block inputs {if hold then "held while busy" else "garbage after the start pulse"}"
    -- (without hold the block is only valid on the start cycle: the core must latch it)
    for gaps in [#[0], #[1, 4, 0, 7], #[20]] do
      ok := (← runCase (mkDut h hold) spec reqs gaps) && ok
  IO.println "-- negative controls on the live design"
  ok := (← liveControls (mkDut h true) spec reqs) && ok
  JIT.destroy h
  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

end Sparkle.Tests.IP.Crypto.Sha256BlockDoneHWJITTest
