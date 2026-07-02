/-
  Sim + synth test for IP.Crypto.Fp381MontMulHW.montMulHW —
  word-serial CIOS Montgomery multiplier over the BLS12-381
  base field (Fp, 381-bit prime).  HW analogue of blst's
  `mul_mont_384`.

  Behavioural: the HW works in the Montgomery domain
  (result = a·b·R^-1 mod p, R = 2^384).  We feed Montgomery-form
  operands aM = a·R mod p, bM = b·R mod p, read the result at the
  done cycle, and check that mapping it back out of Montgomery
  form (× R^-1 mod p) reproduces the pure-data `Fp.mul a b`.
  Also confirms the pipeline timing (done at cycle 14 = start +
  12 word cycles + strobe).

  Synth: `#synthesizeVerilog` on the result + done outputs.
-/
import Sparkle
import IP.Crypto.BLS12_381
import IP.Crypto.Fp381MontMulHW

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Crypto.Fp381MontMulHW

namespace Sparkle.Tests.IP.Crypto.Fp381MontMulHWTest

abbrev D := defaultDomain

/-- BLS12-381 base-field prime. -/
def p : Nat := Sparkle.IP.Crypto.BLS12_381.Fp.p

/-- R = 2^384 (Montgomery radix). -/
def rMont : Nat := 2 ^ 384

/-- R^-1 mod p (precomputed; maps a Montgomery-domain value back
    to the ordinary residue). -/
def rInv : Nat :=
  0x14fec701e8fb0ce9ed5e64273c4f538b1797ab1458a88de9343ea97914956dc87fe11274d898fafbf4d38259380b4820

private def constSig {α : Type} (v : α) : Signal D α := ⟨fun _ => v⟩

private def startSig : Signal D Bool := ⟨fun t => decide (t = 0)⟩

/-- Convert `x` into Montgomery form: x·R mod p. -/
private def toMont (x : Nat) : Nat := (x * rMont) % p

/-- Run one HW Montgomery multiply on Montgomery-form operands
    and read the result at the done cycle (14). -/
private def hwMontMul (aM bM : Nat) : Nat :=
  let aBv : BitVec 384 := BitVec.ofNat 384 aM
  let bBv : BitVec 384 := BitVec.ofNat 384 bM
  let engine := montMulHW startSig (constSig aBv) (constSig bBv)
  (engine.result.val 14).toNat

def main : IO Unit := do
  IO.println "=== BLS12-381 Fp word-serial Montgomery multiplier HW sim ==="
  (← IO.getStdout).flush
  let mut ok := true

  -- Pipeline timing check.
  let engine := montMulHW startSig
                  (constSig (BitVec.ofNat 384 (toMont 7)))
                  (constSig (BitVec.ofNat 384 (toMont 11)))
  if engine.done.val 13 then
    IO.println "  ✗ done pulsed early (t=13)"; ok := false
  else
    IO.println "  ✓ done not asserted at t=13"
  if engine.done.val 14 then
    IO.println "  ✓ done asserted at t=14"
  else
    IO.println "  ✗ done missed t=14"; ok := false

  -- Cross-validate against pure-data `Fp.mul` on several pairs.
  let cases : List (Nat × Nat) :=
    [ (7, 11)
    , (0, 99999)
    , (1, p - 1)
    , (p - 1, p - 1)
    , (2, p - 1)
    , (0x1234567890ABCDEF1234567890ABCDEF1234567890ABCDEF,
       0xFEDCBA0987654321FEDCBA0987654321FEDCBA0987654321) ]
  for (a, b) in cases do
    let ref := Sparkle.IP.Crypto.BLS12_381.Fp.mul a b
    -- Feed Montgomery-form operands; HW returns a·b·R mod p in
    -- Montgomery form.  Map it back out with × R^-1 mod p.
    let hwM := hwMontMul (toMont a) (toMont b)
    let hw  := (hwM * rInv) % p
    if ref = hw then
      IO.println s!"  ✓ montMulHW matches Fp.mul (ref={ref})"
    else
      IO.println s!"  ✗ montMulHW = {hw} ≠ Fp.mul {ref} (a={a}, b={b})"
      ok := false

  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

end Sparkle.Tests.IP.Crypto.Fp381MontMulHWTest

section SynthesisChecks
open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Crypto.Fp381MontMulHW

private def synth_fp381MontMulResult
    (start : Signal defaultDomain Bool)
    (aIn bIn : Signal defaultDomain (BitVec 384)) :
    Signal defaultDomain (BitVec 384) :=
  (montMulHW start aIn bIn).result

#synthesizeVerilog synth_fp381MontMulResult

private def synth_fp381MontMulDone
    (start : Signal defaultDomain Bool)
    (aIn bIn : Signal defaultDomain (BitVec 384)) :
    Signal defaultDomain Bool :=
  (montMulHW start aIn bIn).done

#synthesizeVerilog synth_fp381MontMulDone

end SynthesisChecks
