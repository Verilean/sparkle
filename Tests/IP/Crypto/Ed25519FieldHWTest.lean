/-
  Sim + synth test for IP.Crypto.Ed25519FieldHW.mulHW —
  cycle-accurate bit-serial modular multiplier over the
  Curve25519 base field (p = 2^255 - 19).

  Behavioural: cross-validate the HW multiplier against the
  pure-data `Ed25519Field.mul` on several operand pairs, and
  confirm the pipeline timing (done pulses at cycle 258 =
  start + 256 round cycles + strobe).

  Synth: `#synthesizeVerilog` on the result + done outputs.
-/
import Sparkle
import IP.Crypto.Ed25519Field
import IP.Crypto.Ed25519FieldHW

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Crypto.Ed25519Field (mul p)
open Sparkle.IP.Crypto.Ed25519FieldHW

namespace Sparkle.Tests.IP.Crypto.Ed25519FieldHWTest

abbrev D := defaultDomain

private def constSig {α : Type} (v : α) : Signal D α := ⟨fun _ => v⟩

private def startSig : Signal D Bool := ⟨fun t => decide (t = 0)⟩

/-- Run one HW multiply of (a·b) and read the result at the
    done cycle (258). -/
private def hwMul (a b : Nat) : Nat :=
  let aBv : BitVec 256 := BitVec.ofNat 256 a
  let bBv : BitVec 256 := BitVec.ofNat 256 b
  let engine := mulHW startSig (constSig aBv) (constSig bBv)
  (engine.result.val 258).toNat

def main : IO Unit := do
  IO.println "=== Curve25519 field bit-serial modular multiplier HW sim ==="
  (← IO.getStdout).flush
  let mut ok := true

  -- Pipeline timing check on one representative case.
  let engine := mulHW startSig (constSig (BitVec.ofNat 256 7)) (constSig (BitVec.ofNat 256 11))
  if engine.done.val 257 then
    IO.println "  ✗ done pulsed early (t=257)"; ok := false
  else
    IO.println "  ✓ done not asserted at t=257"
  if engine.done.val 258 then
    IO.println "  ✓ done asserted at t=258"
  else
    IO.println "  ✗ done missed t=258"; ok := false

  -- Cross-validate against pure-data `mul` on several pairs.
  let cases : List (Nat × Nat) :=
    [ (7, 11)
    , (0, 99999)
    , (1, p - 1)
    , (p - 1, p - 1)
    , (2, p - 1)
    , (0x123456789ABCDEF123456789ABCDEF, 0xFEDCBA9876543210FEDCBA9876543210) ]
  for (a, b) in cases do
    let ref := mul a b
    let hw := hwMul a b
    if ref = hw then
      IO.println s!"  ✓ mulHW matches pure-data (ref={ref})"
    else
      IO.println s!"  ✗ mulHW = {hw} ≠ pure-data {ref} (a={a}, b={b})"
      ok := false

  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

end Sparkle.Tests.IP.Crypto.Ed25519FieldHWTest

section SynthesisChecks
open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Crypto.Ed25519FieldHW

private def synth_ed25519MulResult
    (start : Signal defaultDomain Bool)
    (aIn bIn : Signal defaultDomain (BitVec 256)) :
    Signal defaultDomain (BitVec 256) :=
  (mulHW start aIn bIn).result

#synthesizeVerilog synth_ed25519MulResult

private def synth_ed25519MulDone
    (start : Signal defaultDomain Bool)
    (aIn bIn : Signal defaultDomain (BitVec 256)) :
    Signal defaultDomain Bool :=
  (mulHW start aIn bIn).done

#synthesizeVerilog synth_ed25519MulDone

end SynthesisChecks
