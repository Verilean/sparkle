/-
  Sim + synth test for IP.Crypto.AESGCMHW.

  NIST SP 800-38D §Appendix B Test Case 2:
    K   = 00000000000000000000000000000000
    IV  = 000000000000000000000000
    P   = 00000000000000000000000000000000  (16 zero bytes)
    A   = (empty)
    C   = 0388dace60b6a392f328c2b971b2fe78
    T   = ab6e47d42cec13bdf53a67b21257bddf

  Behavioural checks:
    * gcmCounterHW: initial counter J_0 latches, then increments
      per `step` cycle.
    * gcmTagAccumulatorHW: single-block feed, verify `mulX` =
      Y XOR block and Y latches on mulDone.
    * Pure-data cross-check that `encryptAead` on Test Case 2
      matches the expected ciphertext + tag.
-/

import IP.Crypto.Codec.AESGCM
import IP.Crypto.AESGCMHW

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Crypto.AESGCMHW
open Sparkle.IP.Crypto.AESGCM (encryptAead GcmCiphertext)

namespace Sparkle.Tests.IP.Crypto.AESGCMHWTest

abbrev D := defaultDomain

private def bytesToBv128 (bs : Array UInt8) : BitVec 128 := Id.run do
  let mut acc : Nat := 0
  for b in bs do
    acc := (acc <<< 8) ||| b.toNat
  return BitVec.ofNat 128 acc

private def hexOfBytes (bs : Array UInt8) : String := Id.run do
  let digit (d : Nat) : Char :=
    if d < 10 then Char.ofNat (d + 0x30) else Char.ofNat (d - 10 + 0x61)
  let mut out := ""
  for b in bs do
    let n := b.toNat
    out := out.push (digit ((n >>> 4) &&& 0xF))
    out := out.push (digit (n &&& 0xF))
  return out

private def constSig {α : Type} (v : α) : Signal D α := ⟨fun _ => v⟩
private def pulses (ts : List Nat) : Signal D Bool := ⟨fun t => decide (t ∈ ts)⟩
private def bvSchedule (sched : List (Nat × BitVec 128)) (default : BitVec 128) :
    Signal D (BitVec 128) :=
  ⟨fun t =>
    match sched.find? (fun (u, _) => u = t) with
    | some (_, v) => v
    | none => default⟩

def main : IO Unit := do
  IO.println "=== AES-GCM HW pieces + NIST SP 800-38D Test Case 2 ==="
  let mut ok := true

  -- Pure-data NIST GCM Test Case 2.
  let key : Array UInt8 := Array.replicate 16 0
  let iv  : Array UInt8 := Array.replicate 12 0
  let pt  : Array UInt8 := Array.replicate 16 0
  let aad : Array UInt8 := #[]
  let expectedCt : Array UInt8 :=
    #[0x03, 0x88, 0xda, 0xce, 0x60, 0xb6, 0xa3, 0x92,
      0xf3, 0x28, 0xc2, 0xb9, 0x71, 0xb2, 0xfe, 0x78]
  let expectedTag : Array UInt8 :=
    #[0xab, 0x6e, 0x47, 0xd4, 0x2c, 0xec, 0x13, 0xbd,
      0xf5, 0x3a, 0x67, 0xb2, 0x12, 0x57, 0xbd, 0xdf]
  let result := encryptAead key iv pt aad
  IO.println s!"  pure-data C = {hexOfBytes result.ciphertext}"
  IO.println s!"  pure-data T = {hexOfBytes result.tag}"
  if result.ciphertext = expectedCt then
    IO.println "  ok C matches NIST TC 2"
  else
    IO.println s!"  MISMATCH C: expected {hexOfBytes expectedCt}"
    ok := false
  if result.tag = expectedTag then
    IO.println "  ok T matches NIST TC 2"
  else
    IO.println s!"  MISMATCH T: expected {hexOfBytes expectedTag}"
    ok := false

  -- gcmCounterHW: J_0 = IV || 0x00000001 = 12 IV bytes + [0,0,0,1].
  IO.println "-- gcmCounterHW --"
  let j0 : BitVec 128 := bytesToBv128 (iv ++ #[0, 0, 0, 1])
  -- Step schedule: step on t=1, 3, 5.  Counter should be j0
  -- at t=0..1, j0+1 at t=2..3, j0+2 at t=4..5, j0+3 at t=6..
  let engine := gcmCounterHW (pulses [0]) (pulses [1, 3, 5]) (constSig j0)
  for t in [0, 1, 2, 3, 4, 5, 6] do
    let c := engine.counter.val t
    IO.println s!"  t={t}: counter=0x{Nat.toDigits 16 c.toNat |> String.ofList}"

  let expectC := fun (n : Nat) => (j0.toNat + n) &&& ((1 <<< 128) - 1)
  let ctrAt6 := (engine.counter.val 6).toNat
  if ctrAt6 = expectC 3 then
    IO.println "  ok counter after 3 steps = J_0 + 3"
  else
    IO.println s!"  MISMATCH counter@6 = {ctrAt6}, expected {expectC 3}"
    ok := false

  -- gcmTagAccumulatorHW: single block feed.  Feed blockValid at t=1 with a
  -- known block, ack mulDone at t=3 with a known mulResult.  Verify:
  --   fire pulses at t=1
  --   mulX@1 = 0 XOR block = block
  --   ready goes low at t=2, high again at t=4
  --   y@4 = mulResult
  IO.println "-- gcmTagAccumulatorHW --"
  let block : BitVec 128 := 0x0102030405060708090a0b0c0d0e0f10#128
  let mulR  : BitVec 128 := 0xdeadbeef00000000cafef00d00000000#128
  let tagEng := gcmTagAccumulatorHW
                  (pulses [0])
                  (pulses [1])
                  (pulses [3])
                  (constSig block)
                  (constSig mulR)
  for t in [0, 1, 2, 3, 4] do
    let y := tagEng.y.val t
    let mx := tagEng.mulX.val t
    let fr := tagEng.fire.val t
    let rd := tagEng.ready.val t
    IO.println s!"  t={t}: y=0x{Nat.toDigits 16 y.toNat |> String.ofList} mulX=0x{Nat.toDigits 16 mx.toNat |> String.ofList} fire={fr} ready={rd}"
  -- Checks.
  if tagEng.fire.val 1 then
    IO.println "  ok fire pulses at t=1"
  else
    IO.println "  MISMATCH fire@1 = false"
    ok := false
  if tagEng.mulX.val 1 = block then
    IO.println "  ok mulX@1 = block (initial y = 0)"
  else
    IO.println "  MISMATCH mulX@1"
    ok := false
  if tagEng.y.val 4 = mulR then
    IO.println "  ok y@4 = mulResult (latched on mulDone)"
  else
    IO.println s!"  MISMATCH y@4"
    ok := false

  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

end Sparkle.Tests.IP.Crypto.AESGCMHWTest

section SynthesisChecks
open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Crypto.AESGCMHW

private def synth_gcmCounter
    (start step : Signal defaultDomain Bool)
    (j0In : Signal defaultDomain (BitVec 128)) :
    Signal defaultDomain (BitVec 128) :=
  (gcmCounterHW start step j0In).counter

#synthesizeVerilog synth_gcmCounter

private def synth_gcmTagY
    (start blockValid mulDone : Signal defaultDomain Bool)
    (blockIn mulResult : Signal defaultDomain (BitVec 128)) :
    Signal defaultDomain (BitVec 128) :=
  (gcmTagAccumulatorHW start blockValid mulDone blockIn mulResult).y

#synthesizeVerilog synth_gcmTagY

private def synth_gcmTagFire
    (start blockValid mulDone : Signal defaultDomain Bool)
    (blockIn mulResult : Signal defaultDomain (BitVec 128)) :
    Signal defaultDomain Bool :=
  (gcmTagAccumulatorHW start blockValid mulDone blockIn mulResult).fire

#synthesizeVerilog synth_gcmTagFire

end SynthesisChecks
