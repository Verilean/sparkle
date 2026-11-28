/-
  Done-once-per-request JIT co-sim of `hmacSha256` (generic harness
  `DoneHWJITHarness`).  Ports after `#sim`: inputs start = 0, key = 1..8,
  blk1 = 9..24, blk2 = 25..40, threeBlk = 41; outputs hmac = 0..7, done = 8.

  Requests: keys of 1..32 bytes (left-aligned, zero padded) with messages of
  0..119 bytes padded as SHA-256 messages of length 64 + len; reference is the
  pure-data `Rfc6979.hmacSha256`.  Operands held while busy; garbage on every
  input during idle cycles and gaps.  Checked per request: `done` exactly once
  (1 cycle wide), mac at `done` = reference and unchanged until the next start,
  no `done` in the prologue or after the last request; latency window [1, 2000].
  NOT checked: keys longer than the operand (hashed by the caller), 3-block
  messages (outside the design's range).
-/
import IP.Crypto.SHA256
import IP.Crypto.HMACSHA256HW
import IP.Crypto.Rfc6979
import Tests.IP.Crypto.DoneHWJITHarness
import Sparkle.Compiler.Elab

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Core.JIT
open Sparkle.IP.Crypto.HMACSHA256HW
open Sparkle.Tests.IP.Crypto.DoneHW

namespace Sparkle.Tests.IP.Crypto.HmacSha256DoneHWJITTest

set_option maxRecDepth 100000
set_option maxHeartbeats 40000000

def hmacTop (start : Signal defaultDomain Bool) (key : Signal defaultDomain (BitVec 256))
    (blk1 blk2 : Signal defaultDomain (BitVec 512)) (threeBlk : Signal defaultDomain Bool) :
    HmacOut defaultDomain :=
  hmacSha256 start key blk1 blk2 threeBlk

#sim hmacTop

def bytesToNat (a : Array UInt8) : Nat := a.foldl (fun v b => (v <<< 8) ||| b.toNat) 0

def mkDut (h : JITHandle) : Dut where
  handle := h
  hold := true
  set := fun ins st => do
    JIT.setInput h 0 (if st then 1 else 0)
    setWords h 1 8 ins[0]!
    setWords h 9 16 ins[1]!
    setWords h 25 16 ins[2]!
    JIT.setInput h 41 (UInt64.ofNat ins[3]!)
  junk := fun seed => do
    JIT.setInput h 0 0
    setWords h 1 8 (garbage seed 1 256)
    setWords h 9 16 (garbage seed 2 512)
    setWords h 25 16 (garbage seed 3 512)
    JIT.setInput h 41 (UInt64.ofNat (seed / 64 % 2))
  read := do
    let mac ← getWords h 0 8
    let done := (← JIT.getOutput h 8) != 0
    pure { done, outs := #[mac] }

def spec : Spec := { name := "hmacSha256", minLat := 1, maxLat := 2000 }

def request (key msg : Array UInt8) : Req :=
  let b := padBlocks msg 64
  { inputs := #[bytesToNat key <<< (8 * (32 - key.size)), b.getD 0 0, b.getD 1 0, if b.length == 2 then 1 else 0],
    expect := some #[bytesToNat (Sparkle.IP.Crypto.Rfc6979.hmacSha256 key msg)] }

def requests : Array Req := #[
  request (Array.replicate 20 0x0b) (bytesOf "Hi There"),
  request (bytesOf "Jefe") (bytesOf "what do ya want for nothing?"),
  request (Array.replicate 20 0xaa) (Array.replicate 50 0xdd),
  request (Array.replicate 32 0x5a) (Array.replicate 119 0x61),
  request (Array.replicate 32 0xc3) (Array.replicate 56 0x62),
  request (Array.replicate 1 0x01) #[],
  request (Array.replicate 32 0xff) (Array.replicate 55 0x00),
  request (Array.replicate 20 0x0b) (bytesOf "Hi There")]

def main : IO Unit := do
  IO.println "=== hmacSha256 — done-once-per-request JIT co-sim ==="
  (← IO.getStdout).flush
  let sim ← hmacTop.Sim.load
  let h := sim.handle
  let mut ok := true
  for gaps in [#[0], #[1, 4, 0, 7], #[20]] do
    ok := (← runCase (mkDut h) spec requests gaps) && ok
  IO.println "-- negative controls on the live design"
  ok := (← liveControls (mkDut h) spec requests) && ok
  JIT.destroy h
  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

end Sparkle.Tests.IP.Crypto.HmacSha256DoneHWJITTest
