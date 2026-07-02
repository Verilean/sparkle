/-
  Sim + synth test for IP.Crypto.Fp2MulHW.fp2MulHW — Fp2
  multiplication over BLS12-381, driving the Fp381 Montgomery
  multiplier as a sub-engine.

  Behavioural: the FSM sequences 3 Fp multiplies (t0, t1, cross)
  with combinational Fp add/sub between them.  This test
  re-executes that EXACT schedule as a pure-data model
  (`scheduleFp2Mul` — a line-by-line transcription of the operand
  routing in `fp2MulHW`, over plain Fp arithmetic) and
  cross-validates the (c0, c1) result against the independent
  reference `BLS12_381.Fp2.mul`.

  (The cycle-accurate Signal circuit is validated to *synthesize*
  by the `#synthesizeVerilog` checks below.  Full closed-loop
  cycle co-sim — tying `fp2MulHW`'s handshake to a real montMulHW
  via `Signal.loop` — is left to the JIT harness; the interpreted
  `.val` path over a nested feedback loop is the known
  multi-output-FSM slowdown documented for this repo.)

  Synth: `#synthesizeVerilog` on c0Out, c1Out, done.
-/
import Sparkle
import IP.Crypto.BLS12_381
import IP.Crypto.Fp381MontMulHW
import IP.Crypto.Fp2MulHW

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Crypto.Fp2MulHW

namespace Sparkle.Tests.IP.Crypto.Fp2MulHWTest

abbrev D := defaultDomain

open Sparkle.IP.Crypto.BLS12_381

/-- BLS12-381 base-field prime. -/
private def pMod : Nat := Sparkle.IP.Crypto.BLS12_381.Fp.p

/-- The Fp2-mul schedule EXACTLY as `fp2MulHW` routes it:
    3 Fp multiplies (t0, t1, cross) and the combinational
    Fp add/sub combinations.  Returns (c0, c1). -/
private def scheduleFp2Mul (a0 a1 b0 b1 : Nat) : Nat × Nat :=
  let t0    := Fp.mul a0 b0              -- step 0
  let t1    := Fp.mul a1 b1              -- step 1
  let aSum  := Fp.add a0 a1
  let bSum  := Fp.add b0 b1
  let cross := Fp.mul aSum bSum          -- step 2
  let c0    := Fp.sub t0 t1
  let c1    := Fp.sub cross (Fp.add t0 t1)
  (c0, c1)

def main : IO Unit := do
  IO.println "=== BLS12-381 Fp2 multiplier FSM schedule check ==="
  (← IO.getStdout).flush
  let mut ok := true

  -- Non-trivial Fp2 operands (c0 + c1·u).
  let cases : List ((Nat × Nat) × (Nat × Nat)) :=
    [ ((7, 11), (13, 17))
    , ((0, 0), (5, 9))
    , ((1, 0), (pMod - 1, 2))
    , ((pMod - 1, pMod - 2), (pMod - 3, pMod - 5))
    , ((0x1234567890ABCDEF1234567890ABCDEF, 0xFEDCBA0987654321),
       (0xCAFEBABEDEADBEEF, 0x0123456789ABCDEF0123456789ABCDEF)) ]

  for ((a0, a1), (b0, b1)) in cases do
    let ref := Fp2.mul ⟨a0, a1⟩ ⟨b0, b1⟩
    let (c0, c1) := scheduleFp2Mul (a0 % pMod) (a1 % pMod) (b0 % pMod) (b1 % pMod)
    if c0 = ref.c0 ∧ c1 = ref.c1 then
      IO.println s!"  ✓ Fp2 schedule matches Fp2.mul (c0={c0})"
    else
      IO.println s!"  ✗ Fp2 mismatch: sched=({c0},{c1}) ref=({ref.c0},{ref.c1})"
      ok := false

  IO.println s!"  · cycle cost per Fp2-mul (Fp381 mul 14 cyc + handshake):"
  IO.println s!"      3 muls → ~{3 * 16} cycles"

  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

end Sparkle.Tests.IP.Crypto.Fp2MulHWTest

section SynthesisChecks
open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Crypto.Fp2MulHW

private def synth_fp2MulC0
    (start : Signal defaultDomain Bool)
    (a0 a1 b0 b1 : Signal defaultDomain (BitVec 384))
    (mulResult : Signal defaultDomain (BitVec 384))
    (mulDone : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 384) :=
  (fp2MulHW start a0 a1 b0 b1 mulResult mulDone).c0Out

#synthesizeVerilog synth_fp2MulC0

private def synth_fp2MulC1
    (start : Signal defaultDomain Bool)
    (a0 a1 b0 b1 : Signal defaultDomain (BitVec 384))
    (mulResult : Signal defaultDomain (BitVec 384))
    (mulDone : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 384) :=
  (fp2MulHW start a0 a1 b0 b1 mulResult mulDone).c1Out

#synthesizeVerilog synth_fp2MulC1

private def synth_fp2MulDone
    (start : Signal defaultDomain Bool)
    (a0 a1 b0 b1 : Signal defaultDomain (BitVec 384))
    (mulResult : Signal defaultDomain (BitVec 384))
    (mulDone : Signal defaultDomain Bool) :
    Signal defaultDomain Bool :=
  (fp2MulHW start a0 a1 b0 b1 mulResult mulDone).done

#synthesizeVerilog synth_fp2MulDone

end SynthesisChecks
