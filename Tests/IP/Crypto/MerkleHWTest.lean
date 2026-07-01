/-
  Sim test for IP.Crypto.MerkleHW.merkleRootHW.

  Streams 4 leaf hashes into the accumulator (levels 0..2)
  and confirms slot 2 holds the 4-leaf root at the end,
  matching `IP.Crypto.Merkle.commit`.

  The HW takes an external SHA-256 combiner via `combineOut` /
  `combineDone`.  We pre-compute the 3 combines the FSM will
  request (leaves 0↔1, then leaves 2↔3, then those two pairs)
  and feed them on a fixed schedule that matches the FSM's
  request/ack cycles.  This decouples the Merkle FSM's
  correctness from SHA-256 HW timing.

  Synth via #synthesizeVerilog at the bottom.
-/

import IP.Crypto.Merkle
import IP.Crypto.MerkleHW

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Crypto.MerkleHW
open Sparkle.IP.Crypto.Merkle (hashLeaf hashInternal commit Digest)

namespace Sparkle.Tests.IP.Crypto.MerkleHWTest

abbrev D := defaultDomain

/-- Convert a 32-byte digest to a `BitVec 256`, big-endian
    (byte 0 = MSB), matching `hashInternal (l ++ r)` byte order. -/
private def digestToBv (d : Digest) : BitVec 256 := Id.run do
  let mut acc : Nat := 0
  for b in d do
    acc := (acc <<< 8) ||| b.toNat
  return BitVec.ofNat 256 acc

/-- Inverse: 32 bytes from a BitVec 256 in the same order. -/
private def bvToDigest (v : BitVec 256) : Digest := Id.run do
  let mut out : Digest := #[]
  let n := v.toNat
  for i in [:32] do
    let shift := (31 - i) * 8
    out := out.push (UInt8.ofNat ((n >>> shift) &&& 0xFF))
  return out

/-- A Signal that fires exactly at the listed cycles. -/
private def pulses (ts : List Nat) : Signal D Bool :=
  ⟨fun t => decide (t ∈ ts)⟩

/-- A Signal that returns different BitVec 256 values at the
    listed cycles; default everywhere else. -/
private def bvSchedule (sched : List (Nat × BitVec 256)) (default : BitVec 256) :
    Signal D (BitVec 256) :=
  ⟨fun t =>
    match sched.find? (fun (u, _) => u = t) with
    | some (_, v) => v
    | none => default⟩

def main : IO Unit := do
  IO.println "=== Merkle-tree streaming accumulator HW vs pure-data ==="
  let mut ok := true

  -- 4 leaves.  Values are the Goldilocks field elements
  -- 42, 43, 44, 45 hashed as SHA-256(le8bytes(x)).
  let leafVals : List Nat := [42, 43, 44, 45]
  let leaves : List Digest := leafVals.map hashLeaf
  let leafBvs : List (BitVec 256) := leaves.map digestToBv

  -- Expected root via the pure-data reference.
  let expectedRoot := commit leafVals.toArray
  IO.println s!"  pure-data root = {digestToBv expectedRoot |>.toNat |> fun n => Nat.toDigits 16 n |> String.ofList}"

  -- Pre-compute the combine operations the FSM will request.
  --   Leaf 0 push  : slot 0 empty → place, no combine.
  --   Leaf 1 push  : slot 0 full → combine(hashLeaf 42, hashLeaf 43) = c01.
  --                  Result → level 1, slot 1 empty → place.
  --   Leaf 2 push  : slot 0 empty → place.
  --   Leaf 3 push  : slot 0 full → combine(hashLeaf 44, hashLeaf 45) = c23.
  --                  Result → level 1, slot 1 full → combine(c01, c23) = root.
  --                  Result → level 2, slot 2 empty → place.
  let d0 := leaves[0]!
  let d1 := leaves[1]!
  let d2 := leaves[2]!
  let d3 := leaves[3]!
  let c01 := hashInternal d0 d1
  let c23 := hashInternal d2 d3
  let root := hashInternal c01 c23
  if root ≠ expectedRoot then
    IO.println "  ✗ pure-data reference disagrees with itself (bug in test wiring)"
    IO.Process.exit 1
  IO.println s!"  hand-computed root matches commit()"

  -- Push schedule.  Between pushes, allow the FSM to complete
  -- its walk (up to 3 combines + placements ⇒ ~6 cycles budget).
  --
  -- cycle 0 : start
  -- cycle 1 : push leaf 0     — ready→busy for 1 tick, then ready
  -- cycle 3 : push leaf 1     — 1 combine, requires combineDone
  -- cycle 8 : push leaf 2
  -- cycle 10: push leaf 3     — 2 combines
  let pushCycles : List Nat := [1, 3, 8, 10]
  -- Leaf value fed on the push cycle.
  let leafSched : List (Nat × BitVec 256) :=
    List.zip pushCycles leafBvs

  -- Combine acks.  The FSM sets combineReq at some cycle after a
  -- push where the target slot was occupied.  We ack on the *next*
  -- cycle (single-cycle combiner).  Schedule expected acks:
  --   after push@3: combine(d0,d1) → ack at cycle 5 with c01.
  --   after push@10: combine(d2,d3) → ack at cycle 12 with c23.
  --                   then combine(c01,c23) → ack at cycle 14 with root.
  let combSched : List (Nat × BitVec 256) :=
    [ (5, digestToBv c01), (12, digestToBv c23), (14, digestToBv root) ]

  let startSig := pulses [0]
  let pushSig  := pulses pushCycles
  let leafSig  := bvSchedule leafSched 0#256
  let combSig  := bvSchedule combSched 0#256
  let doneSig  := pulses (combSched.map (·.fst))

  let engine := merkleRootHW startSig pushSig leafSig combSig doneSig

  -- Print the FSM state around each event for debugging.
  for t in [:18] do
    let occ := (engine.occ.val t).toNat
    let req := engine.combineReq.val t
    let rdy := engine.ready.val t
    IO.println s!"  t={t}: occ=0b{Nat.toDigits 2 occ |> String.ofList} combineReq={req} ready={rdy}"

  -- The root should be in slot 2 after cycle 15 (one cycle after
  -- the final placeNow following the combine at t=14).
  let s2At15 := engine.slot2.val 15
  let s2At16 := engine.slot2.val 16
  let expectBv := digestToBv root
  IO.println s!"  slot2@15 = {s2At15.toNat |> Nat.toDigits 16 |> String.ofList}"
  IO.println s!"  slot2@16 = {s2At16.toNat |> Nat.toDigits 16 |> String.ofList}"
  IO.println s!"  expected = {expectBv.toNat |> Nat.toDigits 16 |> String.ofList}"

  -- Verify at the cycle where slot 2 latches (the final placeNow).
  let found := s2At15 = expectBv ∨ s2At16 = expectBv
  if found then
    IO.println "  ✓ HW slot 2 holds the 4-leaf Merkle root"
  else
    IO.println "  ✗ HW slot 2 mismatch"
    ok := false

  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

end Sparkle.Tests.IP.Crypto.MerkleHWTest

section SynthesisChecks
open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Crypto.MerkleHW

private def synth_merkleSlot0
    (start push : Signal defaultDomain Bool)
    (leafIn combineOut : Signal defaultDomain (BitVec 256))
    (combineDone : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 256) :=
  (merkleRootHW start push leafIn combineOut combineDone).slot0

#synthesizeVerilog synth_merkleSlot0

private def synth_merkleOcc
    (start push : Signal defaultDomain Bool)
    (leafIn combineOut : Signal defaultDomain (BitVec 256))
    (combineDone : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 4) :=
  (merkleRootHW start push leafIn combineOut combineDone).occ

#synthesizeVerilog synth_merkleOcc

private def synth_merkleCombineReq
    (start push : Signal defaultDomain Bool)
    (leafIn combineOut : Signal defaultDomain (BitVec 256))
    (combineDone : Signal defaultDomain Bool) :
    Signal defaultDomain Bool :=
  (merkleRootHW start push leafIn combineOut combineDone).combineReq

#synthesizeVerilog synth_merkleCombineReq

end SynthesisChecks
