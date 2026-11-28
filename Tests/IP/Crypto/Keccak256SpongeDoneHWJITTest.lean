/-
  Done-once-per-request JIT co-sim of `keccak256SpongeHW` (generic harness
  `DoneHWJITHarness`).  Ports after `#sim`: inputs start = 0, nBlocks = 1,
  m0..m33 = 2..35 (64-bit lanes); outputs d0..d3 = 0..3, done = 4.

  Requests: 0..200-byte messages (Ethereum padding, 1 or 2 blocks of 17 LE
  lanes) whose digest, as 4 LE lanes, is `keccak256OfBytes`.  The lanes are held
  while busy (the second block is absorbed ~28 cycles after start); garbage
  drives every input during idle cycles and gaps.  Checked per request: `done`
  exactly once, hash at `done` = reference and (per the module doc "held after")
  unchanged until the next start, no `done` in the prologue; the `done` width is
  reported and allowed up to 1 cycle; latency window [1, 400].  NOT checked: more
  than 2 blocks (outside `maxBlocks`).
-/
import IP.Crypto.Proof.Keccak256
import IP.Crypto.Keccak256Sponge
import Tests.IP.Crypto.DoneHWJITHarness
import Sparkle.Compiler.Elab

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Core.JIT
open Sparkle.IP.Crypto.Keccak256
open Sparkle.IP.Crypto.Keccak256Sponge
open Sparkle.Tests.IP.Crypto.DoneHW

namespace Sparkle.Tests.IP.Crypto.Keccak256SpongeDoneHWJITTest

set_option maxRecDepth 100000
set_option maxHeartbeats 40000000

def spongeTop
    (start : Signal defaultDomain Bool) (nBlocks : Signal defaultDomain (BitVec 2))
    (m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16
     m17 m18 m19 m20 m21 m22 m23 m24 m25 m26 m27 m28 m29 m30 m31 m32 m33
     : Signal defaultDomain (BitVec 64)) : SpongeOut defaultDomain :=
  keccak256SpongeHW start nBlocks
    m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16
    m17 m18 m19 m20 m21 m22 m23 m24 m25 m26 m27 m28 m29 m30 m31 m32 m33

#sim spongeTop

def mkDut (h : JITHandle) : Dut where
  handle := h
  hold := true
  set := fun ins st => do
    JIT.setInput h 0 (if st then 1 else 0)
    JIT.setInput h 1 (UInt64.ofNat ins[0]!)
    for i in [0:34] do JIT.setInput h (2 + i).toUInt32 (UInt64.ofNat ins[1 + i]!)
  junk := fun seed => do
    JIT.setInput h 0 0
    JIT.setInput h 1 (UInt64.ofNat (garbage seed 1 2))
    for i in [0:34] do JIT.setInput h (2 + i).toUInt32 (UInt64.ofNat (garbage seed (10 + i) 64))
  read := do
    let mut outs := #[]
    for i in [0:4] do outs := outs.push (← JIT.getOutput h i.toUInt32).toNat
    let done := (← JIT.getOutput h 4) != 0
    pure { done, outs }

def spec : Spec := { name := "keccak256SpongeHW", minLat := 1, maxLat := 400 }

def request (msg : Array UInt8) : Req :=
  let padded := padEthereum msg
  let nBlocks := padded.size / rateBytes
  let lanes := (List.range (rateLanes * maxBlocks)).toArray.map fun i =>
    if i < nBlocks * rateLanes then (bytesToLane padded (i * 8)).toNat else 0
  let dig := keccak256OfBytes msg
  let lane := fun (k : Nat) => (List.range 8).foldl (fun v j => v ||| (dig[8 * k + j]!.toNat <<< (8 * j))) 0
  { inputs := #[nBlocks] ++ lanes, expect := some #[lane 0, lane 1, lane 2, lane 3] }

def msgs : Array (Array UInt8) := #[
  #[], #[0x61, 0x62, 0x63], Array.replicate 135 0x61, Array.replicate 136 0x62,
  Array.replicate 200 0x63, Array.replicate 1 0xFF, Array.replicate 100 0x64, #[0x61, 0x62, 0x63]]

def main : IO Unit := do
  IO.println "=== keccak256SpongeHW — done-once-per-request JIT co-sim ==="
  (← IO.getStdout).flush
  let sim ← spongeTop.Sim.load
  let h := sim.handle
  let mut ok := true
  let reqs := msgs.map request
  for gaps in [#[0], #[1, 4, 0, 7], #[20]] do
    ok := (← runCase (mkDut h) spec reqs gaps) && ok
  IO.println "-- negative controls on the live design"
  ok := (← liveControls (mkDut h) spec reqs) && ok
  JIT.destroy h
  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

end Sparkle.Tests.IP.Crypto.Keccak256SpongeDoneHWJITTest
