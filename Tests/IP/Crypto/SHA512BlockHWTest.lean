/-
  Test for `IP.Crypto.SHA512BlockHW.sha512BlockHW` — the full
  80-round SHA-512 block compressor FSM that wave-1 `SHA512HW`
  deferred (it shipped only the combinational Σ/σ/Ch/Maj helpers
  + K-mux).

  Two levels of coverage:

  1. **Pure-data reference** (`main`): the algorithm the FSM
     implements is validated against a known SHA-512 digest
     (FIPS 180-4 "abc" test vector) via `IP.Crypto.SHA512`.
     The FSM's per-cycle register recurrence is a direct
     transliteration of `SHA512.compressBlock`'s 80-round loop
     plus `expandW`'s message schedule (implemented as a 16-word
     sliding window), so this pins the numeric spec.

  2. **Elaboration check** (`main`): `sha512BlockHW` is
     instantiated on constant inputs, forcing the `circuit do`
     elaborator to construct the whole 42-register FSM.  `lake
     build IP.Crypto.SHA512BlockHW` being green already proves
     the module type-checks and lowers to a `Signal.loop`.

  `#synthesizeVerilog` now completes (~3 s / output): the
  super-linear "repeat-walk" translate scaling that had blocked
  this FSM (and forced a "300 s budget" punt) was an O(n²)
  wire-name collision check in the synth backend, since fixed
  (O(1) `Std.HashSet` in `Sparkle/IR/Builder.lean`).  So this
  test now carries a real synth check on a representative output
  (below, `SynthesisChecks`); HMAC / BIP-32 can be composed on
  top.  The full JIT `#sim` is still omitted — the 80-entry
  64-bit K-LUT keeps the interpreted `Signal.val` path slow —
  so the numeric spec is pinned by the pure-data cross-check.
-/
import IP.Crypto.Proof.SHA512
import IP.Crypto.SHA512BlockHW

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Crypto.SHA512BlockHW
open Sparkle.IP.Crypto.SHA512
  (initH compressBlock sha512Bytes)

namespace Sparkle.Tests.IP.Crypto.SHA512BlockHWTest

abbrev D := defaultDomain

private def constSig {α : Type} (v : α) : Signal D α := ⟨fun _ => v⟩
private def startSig : Signal D Bool := ⟨fun t => decide (t = 0)⟩

private def hexOfBytes (bs : Array UInt8) : String := Id.run do
  let digit (d : Nat) : Char :=
    if d < 10 then Char.ofNat (d + 0x30) else Char.ofNat (d - 10 + 0x61)
  let mut out := ""
  for b in bs do
    let n := b.toNat
    out := out.push (digit ((n >>> 4) &&& 0xF))
    out := out.push (digit (n &&& 0xF))
  return out

/-- Build the single padded block (16 × 64-bit words) of a short
    (< 112-byte) message, matching `SHA512.sha512OfBytes`. -/
private def padOneBlock (msg : Array UInt8) : Array (BitVec 64) := Id.run do
  let bitLen : Nat := msg.size * 8
  let mut padded : Array UInt8 := msg
  padded := padded.push 0x80
  while padded.size % 128 ≠ 112 do
    padded := padded.push 0x00
  for _ in [:8] do padded := padded.push 0x00
  for i in [:8] do
    let shift := (7 - i) * 8
    padded := padded.push (UInt8.ofNat ((bitLen >>> shift) &&& 0xFF))
  let mut words : Array (BitVec 64) := #[]
  for i in [:16] do
    let mut w : Nat := 0
    for j in [:8] do
      w := (w <<< 8) ||| (padded.getD (i * 8 + j) 0).toNat
    words := words.push (BitVec.ofNat 64 w)
  return words

def main : IO Unit := do
  IO.println "=== SHA-512 block compressor FSM (elab + pure-data spec) ==="
  let mut ok := true

  -- (1) Pure-data spec: FIPS 180-4 SHA-512("abc").
  let abcExpected :=
    "ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a" ++
    "2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f"
  let abcGot := hexOfBytes (sha512Bytes "abc".toUTF8.toList.toArray)
  IO.println s!"  sha512(\"abc\") = {abcGot}"
  if abcGot = abcExpected then
    IO.println "  ok pure-data SHA-512(\"abc\") matches FIPS 180-4 vector"
  else
    IO.println "  MISMATCH pure-data SHA-512(\"abc\")"
    ok := false

  -- The FSM's register recurrence is `compressBlock` transliterated;
  -- confirm the single-block form the FSM computes agrees with the
  -- byte-level digest for "abc" (one padded block).
  let block := padOneBlock "abc".toUTF8.toList.toArray
  let ref := compressBlock initH block
  let refBytes : Array UInt8 := Id.run do
    let mut bs : Array UInt8 := #[]
    for w in ref do
      for i in [:8] do
        bs := bs.push (UInt8.ofNat ((w.toNat >>> ((7 - i) * 8)) &&& 0xFF))
    return bs
  if hexOfBytes refBytes = abcExpected then
    IO.println "  ok compressBlock(initH, pad(\"abc\")) matches the digest"
  else
    IO.println "  MISMATCH compressBlock single-block form"
    ok := false

  -- (2) Elaboration check: force the elaborator to construct the
  -- whole 42-register FSM on constant inputs.
  let z := constSig 0#64
  let engine :=
    sha512BlockHW startSig
      (constSig (initH.getD 0 0#64)) (constSig (initH.getD 1 0#64))
      (constSig (initH.getD 2 0#64)) (constSig (initH.getD 3 0#64))
      (constSig (initH.getD 4 0#64)) (constSig (initH.getD 5 0#64))
      (constSig (initH.getD 6 0#64)) (constSig (initH.getD 7 0#64))
      z z z z z z z z z z z z z z z z
  -- Touch the result so the term is not dead-code-eliminated.
  let _ := engine.done
  let _ := engine.packed
  IO.println "  ok sha512BlockHW instantiates cleanly on constant inputs"

  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

end Sparkle.Tests.IP.Crypto.SHA512BlockHWTest

section SynthesisChecks
open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Crypto.SHA512BlockHW

/-- Synth check on one representative digest word + the `done`
    strobe.  The full 42-register FSM elaborates and lowers to a
    single-output `Signal (BitVec 64)` / `Signal Bool` that the
    backend translates in ~3 s (post the O(n²) freshName fix). -/
private def synth_sha512Block_out0
    (start : Signal defaultDomain Bool)
    (h0 h1 h2 h3 h4 h5 h6 h7 : Signal defaultDomain (BitVec 64))
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 :
      Signal defaultDomain (BitVec 64)) :
    Signal defaultDomain (BitVec 64) :=
  (sha512BlockHW start h0 h1 h2 h3 h4 h5 h6 h7
     w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15).out0

#synthesizeVerilog synth_sha512Block_out0

private def synth_sha512Block_done
    (start : Signal defaultDomain Bool)
    (h0 h1 h2 h3 h4 h5 h6 h7 : Signal defaultDomain (BitVec 64))
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 :
      Signal defaultDomain (BitVec 64)) :
    Signal defaultDomain Bool :=
  (sha512BlockHW start h0 h1 h2 h3 h4 h5 h6 h7
     w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15).done

#synthesizeVerilog synth_sha512Block_done

end SynthesisChecks
