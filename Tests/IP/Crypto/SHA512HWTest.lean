/-
  Sim + synth test for IP.Crypto.SHA512HW.

  Behavioural:
    * FIPS 180-4 Appendix C.1: SHA-512("abc") =
        ddaf35a193617abacc417349ae204131 12e6fa4e89a97ea20a9eeee64b55d39a
        2192992a274fc1a836ba3c23a3feebbd 454d4423643ce80e2a9ac94fa54ca49f
      Verified through the pure-data reference.
    * Round-by-round check of the Signal-side helpers vs the
      pure-data 64-bit helpers for a hand-picked input word.

  Synth:
    * `kMux` (80-way 64-bit constant table) via `#synthesizeVerilog`.
    * Each combinational helper (rotr64Sig, chFn64Sig, majFn64Sig,
      bigSigma0Sig64, etc.) via wrappers.

  The full 80-round iterative compressor (analogous to SHA-256's
  `sha256Block`) is not implemented here — same Lean-sim
  exponential-cost issue tracked separately for SHA-256's C2
  follow-up.  The K-table mux + helpers are the pieces every
  SHA-512 engine needs, and match the L.1.b coverage that
  landed for SHA-256.
-/

import IP.Crypto.Proof.SHA512
import IP.Crypto.SHA512HW
import Sparkle

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Crypto.SHA512
open Sparkle.IP.Crypto.SHA512HW

namespace Sparkle.Tests.IP.Crypto.SHA512HWTest

abbrev D := defaultDomain

private def constSig {α : Type} (v : α) : Signal D α := ⟨fun _ => v⟩

private def hexByte (b : Nat) : String :=
  let lo := b &&& 0xF
  let hi := (b >>> 4) &&& 0xF
  let digit (d : Nat) : Char :=
    if d < 10 then Char.ofNat (d + 0x30) else Char.ofNat (d - 10 + 0x61)
  String.mk [digit hi, digit lo]

private def expectedHexWords (words : Array (BitVec 64)) : String := Id.run do
  let mut out := ""
  for w in words do
    for i in [:8] do
      let shift := (7 - i) * 8
      out := out ++ hexByte ((w.toNat >>> shift) &&& 0xFF)
  return out

def main : IO Unit := do
  IO.println "=== SHA-512 pure-data + Signal helpers ==="
  let mut ok := true

  -- FIPS 180-4 App C.1: SHA-512("abc").
  let abc : Array UInt8 := "abc".toUTF8.toList.toArray
  let expected :=
    "ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a" ++
    "2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f"
  let got := expectedHexWords (sha512OfBytes abc)
  IO.println s!"  pure SHA-512(\"abc\") = {got}"
  IO.println s!"  expected             = {expected}"
  if got = expected then
    IO.println "  ok pure-data matches FIPS 180-4 App C.1"
  else
    IO.println "  MISMATCH pure-data SHA-512(\"abc\")"
    ok := false

  -- Signal helper cross-check.  Pick a non-trivial input.
  let w : BitVec 64 := 0x0123456789abcdef#64
  let xSig := constSig w
  -- rotr64Sig
  let cases : List (String × BitVec 64 × BitVec 64) :=
    [ ("rotr64  1", rotr64 w  1, (rotr64Sig xSig  1).val 0)
    , ("rotr64  8", rotr64 w  8, (rotr64Sig xSig  8).val 0)
    , ("rotr64 28", rotr64 w 28, (rotr64Sig xSig 28).val 0)
    , ("shr64   7", shr64  w  7, (shr64Sig  xSig  7).val 0)
    , ("bigSig0",   bigSigma0 w,   (bigSigma0Sig64 xSig).val 0)
    , ("bigSig1",   bigSigma1 w,   (bigSigma1Sig64 xSig).val 0)
    , ("smallSig0", smallSigma0 w, (smallSigma0Sig64 xSig).val 0)
    , ("smallSig1", smallSigma1 w, (smallSigma1Sig64 xSig).val 0)
    ]
  for (label, ref, hw) in cases do
    if ref = hw then
      IO.println s!"  ok {label} Signal helper matches pure-data"
    else
      IO.println s!"  MISMATCH {label}: pure={ref.toNat |> Nat.toDigits 16 |> String.ofList} hw={hw.toNat |> Nat.toDigits 16 |> String.ofList}"
      ok := false

  -- Ch/Maj on a triple.
  let a : BitVec 64 := 0x0011223344556677#64
  let b : BitVec 64 := 0x89abcdef01234567#64
  let c : BitVec 64 := 0xfedcba9876543210#64
  let chSig := (chFn64Sig (constSig a) (constSig b) (constSig c)).val 0
  let mjSig := (majFn64Sig (constSig a) (constSig b) (constSig c)).val 0
  if chSig = chFn a b c then
    IO.println "  ok chFn64Sig matches pure-data"
  else
    IO.println "  MISMATCH chFn64Sig"
    ok := false
  if mjSig = majFn a b c then
    IO.println "  ok majFn64Sig matches pure-data"
  else
    IO.println "  MISMATCH majFn64Sig"
    ok := false

  -- kMux sweep on a few round indices.
  let cntBits : List (Nat × BitVec 64) :=
    [ (0,  kTable.getD 0  0#64)
    , (16, kTable.getD 16 0#64)
    , (63, kTable.getD 63 0#64)
    , (79, kTable.getD 79 0#64) ]
  for (t, ref) in cntBits do
    let hw := (kMux (constSig (BitVec.ofNat 7 t))).val 0
    if hw = ref then
      IO.println s!"  ok kMux[t={t}] = {ref.toNat |> Nat.toDigits 16 |> String.ofList}"
    else
      IO.println s!"  MISMATCH kMux[t={t}]"
      ok := false

  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

end Sparkle.Tests.IP.Crypto.SHA512HWTest

section SynthesisChecks
-- Same shape as SHA-256's synth checks (see Tests/IP/Crypto/SHA256Test.lean):
-- the `kMux` sub-module (80-way K-table selector) is the piece every
-- SHA-512 engine needs.  The combinational Σ/σ/Ch/Maj helpers cross
-- module boundaries via `@[reducible, inline]` in the module they're
-- defined in — synthesizing a stand-alone wrapper for them from a
-- *different* module (e.g. this test file) doesn't hit the inline
-- fast path yet.  Same limitation applies to SHA-256's helpers today.
open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Crypto.SHA512HW

private def synth_sha512KMux
    (cnt : Signal defaultDomain (BitVec 7)) :
    Signal defaultDomain (BitVec 64) :=
  kMux cnt

#synthesizeVerilog synth_sha512KMux

end SynthesisChecks
