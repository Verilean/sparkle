/-
  JIT co-sim test for IP.Crypto.Keccak256Sponge — REAL-CYCLE validation.

  The pure-Lean `Signal.val` interpreter cannot co-sim the 25-lane
  Keccak state (it times out — see issue #95 and Keccak256HWTest).
  This test instead lowers the sponge through the `#sim` elaborator
  (`synthesizeHierarchical` → `CSim.toCJIT` → native C → `.so`) and
  runs it as compiled machine code, so we can drive the actual FSM
  cycle-by-cycle and read the digest OUT OF THE HARDWARE.

  This is the only path that exercises the sponge's real handshake
  timing — the block-loop "+1 cycle after keccak-f done" latch that
  the pure-data reconstruction (Keccak256SpongeTest) cannot check.

  Drive protocol (matches `keccak256SpongeHW`):
    * pack the padded message into 34 LE lanes (block-major),
    * cycle 0: start=1 with the lanes + nBlocks,
    * cycle 1..: start=0, tick until `done`=1,
    * read d0..d3, assemble the 32-byte digest, compare to
      `keccak256OfBytes input`.
-/
import IP.Crypto.Proof.Keccak256
import IP.Crypto.Keccak256Sponge
import Sparkle.Compiler.Elab

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Crypto.Keccak256
open Sparkle.IP.Crypto.Keccak256Sponge

namespace Sparkle.Tests.IP.Crypto.Keccak256SpongeJITTest

set_option maxRecDepth 100000
set_option maxHeartbeats 40000000

/-- The `#sim`-able top: returns the full `SpongeOut` record so the
    generated `SimOutput` exposes d0..d3 + done. -/
def spongeSimTop
    (start : Signal defaultDomain Bool) (nBlocks : Signal defaultDomain (BitVec 2))
    (m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16
     m17 m18 m19 m20 m21 m22 m23 m24 m25 m26 m27 m28 m29 m30 m31 m32 m33
     : Signal defaultDomain (BitVec 64)) : SpongeOut defaultDomain :=
  keccak256SpongeHW start nBlocks
    m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16
    m17 m18 m19 m20 m21 m22 m23 m24 m25 m26 m27 m28 m29 m30 m31 m32 m33

#sim spongeSimTop

open spongeSimTop.Sim

/-- Pack a padded byte array into 34 LE lanes (block-major), zero-
    filling unused lanes.  Mirrors `Keccak256SpongeTest.packLanes`. -/
private def packLanes34 (padded : Array UInt8) : Array (BitVec 64) × Nat := Id.run do
  let nBlocks := padded.size / rateBytes
  let mut lanes : Array (BitVec 64) := Array.replicate (rateLanes * maxBlocks) 0#64
  for blk in [:nBlocks] do
    for i in [:rateLanes] do
      lanes := lanes.set! (blk * rateLanes + i)
        (bytesToLane padded (blk * rateBytes + i * 8))
  return (lanes, nBlocks)

/-- Build a `SimInput` for a given start bit + packed lanes + nBlocks. -/
private def mkInput (start : Bool) (nBlocks : Nat) (L : Array (BitVec 64)) : SimInput :=
  let g := fun i => L.getD i 0#64
  { start := if start then 1#1 else 0#1
  , nBlocks := BitVec.ofNat 2 nBlocks
  , m0 := g 0,   m1 := g 1,   m2 := g 2,   m3 := g 3
  , m4 := g 4,   m5 := g 5,   m6 := g 6,   m7 := g 7
  , m8 := g 8,   m9 := g 9,   m10 := g 10, m11 := g 11
  , m12 := g 12, m13 := g 13, m14 := g 14, m15 := g 15
  , m16 := g 16, m17 := g 17, m18 := g 18, m19 := g 19
  , m20 := g 20, m21 := g 21, m22 := g 22, m23 := g 23
  , m24 := g 24, m25 := g 25, m26 := g 26, m27 := g 27
  , m28 := g 28, m29 := g 29, m30 := g 30, m31 := g 31
  , m32 := g 32, m33 := g 33 }

/-- 4 LE lanes → 32-byte digest. -/
private def lanesToDigest (o : SimOutput) : Array UInt8 :=
  laneToBytes o.d0 ++ laneToBytes o.d1 ++ laneToBytes o.d2 ++ laneToBytes o.d3

private def hexOfBytes (bs : Array UInt8) : String := Id.run do
  let digit := fun (n : Nat) => "0123456789abcdef".toList.getD n '?'
  let mut s := ""
  for b in bs do
    s := s.push (digit (b.toNat / 16)) |>.push (digit (b.toNat % 16))
  return s

/-- Run one message through the JIT sponge and return the digest. -/
private def runSponge (sim : Simulator) (input : Array UInt8) : IO (Array UInt8) := do
  let padded := padEthereum input
  let (lanes, nBlocks) := packLanes34 padded
  sim.reset
  -- Cycle 0: start pulse with lanes + nBlocks.
  sim.step (mkInput true nBlocks lanes)
  -- Hold start low; tick until done, cap at a generous bound
  -- (2 blocks × ~30 cyc ≪ 200).
  let zeroLanes : Array (BitVec 64) := Array.replicate (rateLanes * maxBlocks) 0#64
  let mut out ← sim.read
  let mut cyc := 0
  while out.done == 0#1 && cyc < 200 do
    sim.step (mkInput false nBlocks zeroLanes)
    out ← sim.read
    cyc := cyc + 1
  return lanesToDigest out

def main : IO Unit := do
  IO.println "=== Keccak-256 sponge — JIT real-cycle co-sim vs keccak256OfBytes ==="
  (← IO.getStdout).flush
  let sim ← load
  let mut ok := true

  let mk := fun (n : Nat) => Array.replicate n (0x61 : UInt8)
  let fixtures : List (String × Array UInt8) :=
    [ ("empty", #[])
    , ("abc",   #[0x61, 0x62, 0x63])
    , ("136B",  mk 136)   -- 2-block: exercises the block-loop continuation
    , ("200B",  mk 200) ]

  for (label, input) in fixtures do
    let got ← runSponge sim input
    let ref := keccak256OfBytes input
    if got == ref then
      IO.println s!"  ✓ {label}: HW digest {hexOfBytes got}"
    else
      IO.println s!"  ✗ {label}: HW {hexOfBytes got} ≠ ref {hexOfBytes ref}"
      ok := false

  sim.destroy
  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

end Sparkle.Tests.IP.Crypto.Keccak256SpongeJITTest
