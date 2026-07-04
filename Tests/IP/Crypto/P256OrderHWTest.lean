/-
  Sim + synth test for IP.Crypto.P256OrderHW.mulModNHW —
  bit-serial modular multiplier over the P-256 curve order n.

  Behavioural: cross-validate the HW multiplier against the pure
  `(a·b) mod n` on several operand pairs, and confirm the pipeline
  timing (done pulses at cycle 258 = start + 256 round cycles +
  strobe).  This engine has no feedback loop, so direct `.val`
  sampling is fine (as for Secp256k1FieldHWTest).

  Synth: `#synthesizeVerilog` on the result + done outputs.
-/
import Sparkle
import IP.Crypto.P256ECDSA
import IP.Crypto.P256OrderHW

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Crypto.P256OrderHW

namespace Sparkle.Tests.IP.Crypto.P256OrderHWTest

abbrev D := defaultDomain

private def constSig {α : Type} (v : α) : Signal D α := ⟨fun _ => v⟩

private def startSig : Signal D Bool := ⟨fun t => decide (t = 0)⟩

/-- Run one HW multiply of (a·b) mod n and read at the done cycle (258). -/
private def hwMul (a b : Nat) : Nat :=
  let aBv : BitVec 256 := BitVec.ofNat 256 a
  let bBv : BitVec 256 := BitVec.ofNat 256 b
  let engine := mulModNHW startSig (constSig aBv) (constSig bBv)
  (engine.result.val 258).toNat

def main : IO Unit := do
  IO.println "=== P-256 order (mod-n) modular multiplier HW sim ==="
  (← IO.getStdout).flush
  let mut ok := true

  let n := Sparkle.IP.Crypto.P256ECDSA.n

  -- Pipeline timing check.
  let engine := mulModNHW startSig (constSig (BitVec.ofNat 256 7)) (constSig (BitVec.ofNat 256 11))
  if engine.done.val 257 then
    IO.println "  ✗ done pulsed early (t=257)"; ok := false
  else
    IO.println "  ✓ done not asserted at t=257"
  if engine.done.val 258 then
    IO.println "  ✓ done asserted at t=258"
  else
    IO.println "  ✗ done missed t=258"; ok := false

  -- Cross-validate against (a·b) mod n.
  let cases : List (Nat × Nat) :=
    [ (7, 11)
    , (0, 99999)
    , (1, n - 1)
    , (n - 1, n - 1)
    , (2, n - 1)
    , (0x123456789ABCDEF123456789ABCDEF, 0xFEDCBA9876543210FEDCBA9876543210) ]
  for (a, b) in cases do
    let ref := (a * b) % n
    let hw := hwMul a b
    if ref = hw then
      IO.println s!"  ✓ mulModNHW matches (a·b) mod n (ref={ref})"
    else
      IO.println s!"  ✗ mulModNHW = {hw} ≠ {ref} (a={a}, b={b})"
      ok := false

  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

end Sparkle.Tests.IP.Crypto.P256OrderHWTest

section SynthesisChecks
open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Crypto.P256OrderHW

private def synth_p256OrderMulResult
    (start : Signal defaultDomain Bool)
    (aIn bIn : Signal defaultDomain (BitVec 256)) :
    Signal defaultDomain (BitVec 256) :=
  (mulModNHW start aIn bIn).result

#synthesizeVerilog synth_p256OrderMulResult

private def synth_p256OrderMulDone
    (start : Signal defaultDomain Bool)
    (aIn bIn : Signal defaultDomain (BitVec 256)) :
    Signal defaultDomain Bool :=
  (mulModNHW start aIn bIn).done

#synthesizeVerilog synth_p256OrderMulDone

end SynthesisChecks
