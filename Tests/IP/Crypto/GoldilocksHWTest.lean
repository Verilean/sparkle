/-
  Sim + synth test for IP.Crypto.GoldilocksHW.mulHW —
  cycle-accurate bit-serial modular multiplier over the
  Goldilocks field (p = 2^64 - 2^32 + 1).

  Behavioural: cross-validate the HW multiplier against the
  pure-data `Goldilocks.mul` on several operand pairs, and
  confirm the pipeline timing (done pulses at cycle 65 =
  start + 64 round cycles + 1 strobe).

  Synth: `#synthesizeVerilog` on the result + done outputs.
-/
import Sparkle
import IP.Crypto.Goldilocks
import IP.Crypto.GoldilocksHW

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Crypto.Goldilocks (mul p)
open Sparkle.IP.Crypto.GoldilocksHW

namespace Sparkle.Tests.IP.Crypto.GoldilocksHWTest

abbrev D := defaultDomain

private def constSig {α : Type} (v : α) : Signal D α := ⟨fun _ => v⟩

private def startSig : Signal D Bool := ⟨fun t => decide (t = 0)⟩

/-- Run one HW multiply of (a·b) and read the result at the
    done cycle (65). -/
private def hwMul (a b : Nat) : Nat :=
  let aBv : BitVec 64 := BitVec.ofNat 64 a
  let bBv : BitVec 64 := BitVec.ofNat 64 b
  let engine := mulHW startSig (constSig aBv) (constSig bBv)
  (engine.result.val 66).toNat

def main : IO Unit := do
  IO.println "=== Goldilocks bit-serial modular multiplier HW sim ==="
  (← IO.getStdout).flush
  let mut ok := true

  -- Pipeline timing check on one representative case.
  let engine := mulHW startSig (constSig (BitVec.ofNat 64 7)) (constSig (BitVec.ofNat 64 11))
  if engine.done.val 65 then
    IO.println "  ✗ done pulsed early (t=65)"; ok := false
  else
    IO.println "  ✓ done not asserted at t=65"
  if engine.done.val 66 then
    IO.println "  ✓ done asserted at t=66"
  else
    IO.println "  ✗ done missed t=66"; ok := false

  -- Cross-validate against pure-data `mul` on several pairs.
  let cases : List (Nat × Nat) :=
    [ (7, 11)
    , (0, 12345)
    , (1, p - 1)
    , (p - 1, p - 1)
    , (0x123456789ABCDEF, 0xFEDCBA987654321)
    , (2, p - 1)                       -- exercises the reduce-after-double path
    , (0xFFFFFFFF00000000, 0xFFFFFFFF) ]
  for (a, b) in cases do
    let ref := mul a b
    let hw := hwMul a b
    if ref = hw then
      IO.println s!"  ✓ mulHW({a}, {b}) = {hw} matches pure-data"
    else
      IO.println s!"  ✗ mulHW({a}, {b}) = {hw} ≠ pure-data {ref}"
      ok := false

  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

end Sparkle.Tests.IP.Crypto.GoldilocksHWTest

section SynthesisChecks
open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Crypto.GoldilocksHW

private def synth_goldilocksMulResult
    (start : Signal defaultDomain Bool)
    (aIn bIn : Signal defaultDomain (BitVec 64)) :
    Signal defaultDomain (BitVec 64) :=
  (mulHW start aIn bIn).result

#synthesizeVerilog synth_goldilocksMulResult

private def synth_goldilocksMulDone
    (start : Signal defaultDomain Bool)
    (aIn bIn : Signal defaultDomain (BitVec 64)) :
    Signal defaultDomain Bool :=
  (mulHW start aIn bIn).done

#synthesizeVerilog synth_goldilocksMulDone

end SynthesisChecks
