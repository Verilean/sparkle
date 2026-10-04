/-
  Sim + synth test for IP.Crypto.Keccak256Sponge.

  The sponge's deep 25-lane × 64-bit state makes full `Signal.val`
  co-sim time out the pure-Lean simulator (same limitation the
  `keccakF1600HW` permutation test documents).  So the behavioural
  validation is done at the PURE-DATA level, on the exact
  pad + lane-pack + block-loop the HW consumes:

    1. `padEthereum input`               (caller-side padding)
    2. pack padded bytes → 64-bit LE lanes, block-major
       (lane b*17+i = bytesToLane block-b at 8*i)              ← the
       exact `msgLanes` layout `keccak256SpongeHW` expects
    3. run the block loop (XOR 17 lanes / block, keccakF each)
    4. squeeze lanes 0..3 → 32-byte digest

  If this reconstruction equals `keccak256OfBytes input` for a set
  of fixtures — including the 1-block and 2-block cases and the
  `zerosNeeded == 0` padding boundary — then the byte→lane→block
  contract the top will drive the sponge with is correct.  The HW
  itself is validated by instantiation + `#synthesizeVerilog`.
-/
import IP.Crypto.Proof.Keccak256
import IP.Crypto.Keccak256Sponge

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Crypto.Keccak256
open Sparkle.IP.Crypto.Keccak256Sponge

namespace Sparkle.Tests.IP.Crypto.Keccak256SpongeTest

abbrev D := defaultDomain

private def constSig {α : Type} (v : α) : Signal D α := ⟨fun _ => v⟩

/-- Hex string of a byte array. -/
private def hexOfBytes (bs : Array UInt8) : String := Id.run do
  let digit := fun (n : Nat) => "0123456789abcdef".toList.getD n '?'
  let mut s := ""
  for b in bs do
    s := s.push (digit (b.toNat / 16)) |>.push (digit (b.toNat % 16))
  return s

/-- Pack a padded byte array into 64-bit LE lanes, block-major —
    EXACTLY the `msgLanes` layout `keccak256SpongeHW` indexes as
    `msgLanes[blk*17 + i]`.  Returns (lanes, nBlocks). -/
private def packLanes (padded : Array UInt8) : Array (BitVec 64) × Nat := Id.run do
  let nBlocks := padded.size / rateBytes
  let mut lanes : Array (BitVec 64) := #[]
  for blk in [:nBlocks] do
    for i in [:rateLanes] do
      lanes := lanes.push (bytesToLane padded (blk * rateBytes + i * 8))
  return (lanes, nBlocks)

/-- Reference sponge computed from the *lane* representation the HW
    consumes: run the same absorb/permute loop over `packLanes`
    output.  Must equal `keccak256OfBytes`. -/
private def spongeFromLanes (input : Array UInt8) : Array UInt8 := Id.run do
  let padded := padEthereum input
  let (lanes, nBlocks) := packLanes padded
  let mut state : State := State.empty
  for blk in [:nBlocks] do
    for i in [:rateLanes] do
      let cur := state.getD i 0#64
      state := state.set! i (cur ^^^ lanes.getD (blk * rateLanes + i) 0#64)
    state := keccakF state
  let mut out : Array UInt8 := #[]
  for laneIdx in [:4] do
    out := out ++ laneToBytes (state.getD laneIdx 0#64)
  return out

def main : IO Unit := do
  IO.println "=== Keccak-256 sponge (lane-domain) vs keccak256OfBytes ==="
  (← IO.getStdout).flush
  let mut ok := true

  -- Fixtures spanning the block/padding boundaries:
  --   empty          → 1 block
  --   "abc" (3 B)    → 1 block
  --   135 B          → zerosNeeded == 0 (0x81 collision), 1 block
  --   136 B          → exactly one full block + a pad-only 2nd block
  --   200 B          → 2 blocks
  let mk := fun (n : Nat) => Array.replicate n (0x61 : UInt8)  -- 'a'*n
  let fixtures : List (String × Array UInt8) :=
    [ ("empty",  #[])
    , ("abc",    #[0x61, 0x62, 0x63])
    , ("135B",   mk 135)
    , ("136B",   mk 136)
    , ("200B",   mk 200) ]

  for (label, input) in fixtures do
    let ref := keccak256OfBytes input
    let got := spongeFromLanes input
    let padded := padEthereum input
    let nB := padded.size / rateBytes
    if got == ref then
      IO.println s!"  ✓ {label} ({input.size}B → {nB} block(s)): {hexOfBytes got}"
    else
      IO.println s!"  ✗ {label}: lane-sponge {hexOfBytes got} ≠ ref {hexOfBytes ref}"
      ok := false

  -- Sanity: our fixtures exercise nBlocks ∈ {1, 2}, the HW's range.
  let maxNb := (fixtures.map (fun (_, i) => (padEthereum i).size / rateBytes)).foldl Nat.max 0
  if maxNb > maxBlocks then
    IO.println s!"  ✗ a fixture needs {maxNb} blocks > HW maxBlocks={maxBlocks}"
    ok := false
  else
    IO.println s!"  · max blocks across fixtures = {maxNb} (HW supports {maxBlocks})"

  -- HW instantiation smoke-check (forces the FSM to elaborate; no
  -- Signal.val sampling — the 25-lane recursion times out the sim).
  -- `keccak256SpongeHW` now takes the 34 message lanes as separate
  -- scalar args (m0..m33), not an array.
  let z : Signal D (BitVec 64) := constSig 0#64
  let _engine := keccak256SpongeHW (constSig true) (constSig 1#2)
    z z z z z z z z z z  z z z z z z z z z z
    z z z z z z z z z z  z z z z
  IO.println "  ok keccak256SpongeHW instantiates cleanly on constant lanes"

  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

end Sparkle.Tests.IP.Crypto.Keccak256SpongeTest

section SynthesisChecks
open Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.IP.Crypto.Keccak256Sponge

set_option maxRecDepth 8000
set_option maxHeartbeats 8000000

/-- A constant zero lane at the default domain. -/
private def z64 : Signal defaultDomain (BitVec 64) := ⟨fun _ => 0#64⟩

/-- Synth the sponge's digest lane 0.  The 34 message lanes are passed
    as separate scalar args (all zero here) — a hardware-module input
    must be flat scalars for the synth pass to lower it. -/
private def synth_spongeD0
    (start : Signal defaultDomain Bool)
    (nBlocks : Signal defaultDomain (BitVec 2))
    (m0  m1  m2  m3  m4  m5  m6  m7  m8  m9
     m10 m11 m12 m13 m14 m15 m16 m17 m18 m19
     m20 m21 m22 m23 m24 m25 m26 m27 m28 m29
     m30 m31 m32 m33 : Signal defaultDomain (BitVec 64)) :
    Signal defaultDomain (BitVec 64) :=
  (keccak256SpongeHW start nBlocks
    m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 m19 m20 m21 m22 m23 m24 m25 m26 m27 m28 m29 m30 m31 m32 m33).d0

#synthesizeVerilog synth_spongeD0

/-- Synth the sponge's `done`. -/
private def synth_spongeDone
    (start : Signal defaultDomain Bool)
    (nBlocks : Signal defaultDomain (BitVec 2))
    (m0  m1  m2  m3  m4  m5  m6  m7  m8  m9
     m10 m11 m12 m13 m14 m15 m16 m17 m18 m19
     m20 m21 m22 m23 m24 m25 m26 m27 m28 m29
     m30 m31 m32 m33 : Signal defaultDomain (BitVec 64)) :
    Signal defaultDomain Bool :=
  (keccak256SpongeHW start nBlocks
    m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 m19 m20 m21 m22 m23 m24 m25 m26 m27 m28 m29 m30 m31 m32 m33).done

#synthesizeVerilog synth_spongeDone

end SynthesisChecks
