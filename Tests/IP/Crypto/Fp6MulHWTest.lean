/-
  Sim + synth test for IP.Crypto.Fp6MulHW.fp6MulHW — Fp6
  multiplication over BLS12-381, driving the Fp2 multiplier as a
  sub-engine (which in turn drives the Fp381 Montgomery mul).

  Behavioural: the FSM sequences 6 Fp2 multiplies with
  combinational Fp2 add/sub/mulByXi between them.  This test
  re-executes that EXACT schedule as a pure-data model
  (`scheduleFp6Mul` — a transcription of the operand routing +
  output combine in `fp6MulHW`, over `BLS12_381.Fp2` arithmetic)
  and cross-validates (c0, c1, c2) against the independent
  reference `BLS12_381.Fp6.mul`.

  (The cycle-accurate Signal circuit is validated to *synthesize*
  by `#synthesizeVerilog` below.  Full closed-loop cycle co-sim is
  left to the JIT harness — the interpreted `.val` path over nested
  feedback is the known multi-output-FSM slowdown for this repo.)

  Synth: `#synthesizeVerilog` on one output coordinate + done.
-/
import Sparkle
import IP.Crypto.BLS12_381
import IP.Crypto.Fp381MontMulHW
import IP.Crypto.Fp2MulHW
import IP.Crypto.Fp6MulHW

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Crypto.Fp6MulHW

namespace Sparkle.Tests.IP.Crypto.Fp6MulHWTest

abbrev D := defaultDomain

open Sparkle.IP.Crypto.BLS12_381

/-- The Fp6-mul schedule EXACTLY as `fp6MulHW` routes it: 6 Fp2
    multiplies (v0,v1,v2,m3,m4,m5) then the combinational Fp2
    combine.  Returns (c0, c1, c2) as Fp2 elements. -/
private def scheduleFp6Mul (a0 a1 a2 b0 b1 b2 : Fp2.El) : Fp2.El × Fp2.El × Fp2.El :=
  let v0 := Fp2.mul a0 b0                                   -- step 0
  let v1 := Fp2.mul a1 b1                                   -- step 1
  let v2 := Fp2.mul a2 b2                                   -- step 2
  let m3 := Fp2.mul (Fp2.add a1 a2) (Fp2.add b1 b2)         -- step 3
  let m4 := Fp2.mul (Fp2.add a0 a1) (Fp2.add b0 b1)         -- step 4
  let m5 := Fp2.mul (Fp2.add a0 a2) (Fp2.add b0 b2)         -- step 5
  let c0 := Fp2.add v0 (Fp2.mulByXi (Fp2.sub (Fp2.sub m3 v1) v2))
  let c1 := Fp2.add (Fp2.sub (Fp2.sub m4 v0) v1) (Fp2.mulByXi v2)
  let c2 := Fp2.add (Fp2.sub (Fp2.sub m5 v0) v2) v1
  (c0, c1, c2)

def main : IO Unit := do
  IO.println "=== BLS12-381 Fp6 multiplier FSM schedule check ==="
  (← IO.getStdout).flush
  let mut ok := true

  let mk : Nat → Nat → Fp2.El := fun a b => ⟨a, b⟩
  -- Non-trivial Fp6 operands (each coord an Fp2 pair).
  let cases : List ((Fp2.El × Fp2.El × Fp2.El) × (Fp2.El × Fp2.El × Fp2.El)) :=
    [ ((mk 1 2, mk 3 4, mk 5 6), (mk 7 8, mk 9 10, mk 11 12))
    , ((mk 0 0, mk 1 0, mk 0 1), (mk 2 3, mk 4 5, mk 6 7))
    , ((mk 0x1234567890ABCDEF 0xFEDCBA0987654321,
        mk 0xCAFEBABEDEADBEEF 0x0123456789ABCDEF,
        mk 0xDEADC0DE12345678 0x8765432112345678),
       (mk 0x1111111122222222 0x3333333344444444,
        mk 0x5555555566666666 0x7777777788888888,
        mk 0x99999999AAAAAAAA 0xBBBBBBBBCCCCCCCC)) ]

  for ((a0, a1, a2), (b0, b1, b2)) in cases do
    let ref := Fp6.mul ⟨a0, a1, a2⟩ ⟨b0, b1, b2⟩
    let (c0, c1, c2) := scheduleFp6Mul a0 a1 a2 b0 b1 b2
    if c0 = ref.c0 ∧ c1 = ref.c1 ∧ c2 = ref.c2 then
      IO.println s!"  ✓ Fp6 schedule matches Fp6.mul (c0.c0={c0.c0})"
    else
      IO.println s!"  ✗ Fp6 mismatch"
      IO.println s!"      sched c0=({c0.c0},{c0.c1}) c1=({c1.c0},{c1.c1}) c2=({c2.c0},{c2.c1})"
      IO.println s!"      ref   c0=({ref.c0.c0},{ref.c0.c1}) c1=({ref.c1.c0},{ref.c1.c1}) c2=({ref.c2.c0},{ref.c2.c1})"
      ok := false

  IO.println s!"  · cycle cost per Fp6-mul (Fp2-mul ~48 cyc + handshake):"
  IO.println s!"      6 Fp2-muls → ~{6 * 50} cycles"

  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

end Sparkle.Tests.IP.Crypto.Fp6MulHWTest

section SynthesisChecks
open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Crypto.Fp6MulHW

private def synth_fp6MulC0a
    (start : Signal defaultDomain Bool)
    (a0a a0b a1a a1b a2a a2b : Signal defaultDomain (BitVec 384))
    (b0a b0b b1a b1b b2a b2b : Signal defaultDomain (BitVec 384))
    (fp2C0 fp2C1 : Signal defaultDomain (BitVec 384))
    (fp2Done : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 384) :=
  (fp6MulHW start a0a a0b a1a a1b a2a a2b b0a b0b b1a b1b b2a b2b fp2C0 fp2C1 fp2Done).c0aOut

#synthesizeVerilog synth_fp6MulC0a

private def synth_fp6MulDone
    (start : Signal defaultDomain Bool)
    (a0a a0b a1a a1b a2a a2b : Signal defaultDomain (BitVec 384))
    (b0a b0b b1a b1b b2a b2b : Signal defaultDomain (BitVec 384))
    (fp2C0 fp2C1 : Signal defaultDomain (BitVec 384))
    (fp2Done : Signal defaultDomain Bool) :
    Signal defaultDomain Bool :=
  (fp6MulHW start a0a a0b a1a a1b a2a a2b b0a b0b b1a b1b b2a b2b fp2C0 fp2C1 fp2Done).done

#synthesizeVerilog synth_fp6MulDone

end SynthesisChecks
