/-
  Sim + synth test for IP.Crypto.Fp12MulHW.fp12MulHW — Fp12
  multiplication over BLS12-381 (the pairing target group GT),
  driving the Fp6 multiplier as a sub-engine (which drives Fp2,
  which drives the Fp381 Montgomery mul).

  Behavioural: the FSM sequences 3 Fp6 multiplies (v0, v1, cross)
  with combinational Fp6 add/sub/mulByV between them.  This test
  re-executes that EXACT schedule as a pure-data model
  (`scheduleFp12Mul`) over `BLS12_381.Fp6` arithmetic and
  cross-validates (c0, c1) against the reference `BLS12_381.Fp12.mul`.

  (The Signal circuit is validated to *synthesize* by
  `#synthesizeVerilog` below; closed-loop cycle co-sim is left to
  the JIT harness — the interpreted `.val` path over nested feedback
  is the known multi-output-FSM slowdown for this repo.)

  Synth: `#synthesizeVerilog` on one output coordinate + done.
-/
import Sparkle
import IP.Crypto.Proof.BLS12_381
import IP.Crypto.Fp6MulHW
import IP.Crypto.Fp12MulHW

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Crypto.Fp12MulHW

namespace Sparkle.Tests.IP.Crypto.Fp12MulHWTest

abbrev D := defaultDomain

open Sparkle.IP.Crypto.BLS12_381

/-- The Fp12-mul schedule EXACTLY as `fp12MulHW` routes it: 3 Fp6
    multiplies (v0, v1, cross) then the combinational Fp6 combine
    (c0 = v0 + mulByV v1; c1 = cross - v0 - v1).  Returns (c0, c1). -/
private def scheduleFp12Mul (a0 a1 b0 b1 : Fp6.El) : Fp6.El × Fp6.El :=
  let v0 := Fp6.mul a0 b0                                 -- step 0
  let v1 := Fp6.mul a1 b1                                 -- step 1
  let cross := Fp6.mul (Fp6.add a0 a1) (Fp6.add b0 b1)    -- step 2
  let c0 := Fp6.add v0 (Fp6.mulByV v1)
  let c1 := Fp6.sub cross (Fp6.add v0 v1)
  (c0, c1)

def main : IO Unit := do
  IO.println "=== BLS12-381 Fp12 multiplier FSM schedule check ==="
  (← IO.getStdout).flush
  let mut ok := true

  let f2 : Nat → Nat → Fp2.El := fun a b => ⟨a, b⟩
  let f6 : Fp2.El → Fp2.El → Fp2.El → Fp6.El := fun c0 c1 c2 => ⟨c0, c1, c2⟩
  -- Two non-trivial Fp12 operands (each = 2 Fp6 = 6 Fp2 = 12 Nats).
  let a0 := f6 (f2 1 2) (f2 3 4) (f2 5 6)
  let a1 := f6 (f2 7 8) (f2 9 10) (f2 11 12)
  let b0 := f6 (f2 13 14) (f2 15 16) (f2 17 18)
  let b1 := f6 (f2 19 20) (f2 21 22) (f2 23 24)
  let a0' := f6 (f2 0x1234567890ABCDEF 0xFEDCBA0987654321)
               (f2 0xCAFEBABEDEADBEEF 0x0123456789ABCDEF)
               (f2 0xDEADC0DE12345678 0x8765432112345678)
  let a1' := f6 (f2 0x1111111122222222 0x3333333344444444)
               (f2 0x5555555566666666 0x7777777788888888)
               (f2 0x99999999AAAAAAAA 0xBBBBBBBBCCCCCCCC)
  let b0' := f6 (f2 0xABCDEF0123456789 0x9876543210FEDCBA)
               (f2 0x0F0F0F0F0F0F0F0F 0xF0F0F0F0F0F0F0F0)
               (f2 0x1122334455667788 0x99AABBCCDDEEFF00)
  let b1' := f6 (f2 0xDEADBEEFCAFEBABE 0xBAADF00DBAADF00D)
               (f2 0x0102030405060708 0x090A0B0C0D0E0F10)
               (f2 0xFFFFFFFFFFFFFFFF 0x0000000000000001)

  let cases : List ((Fp6.El × Fp6.El) × (Fp6.El × Fp6.El)) :=
    [ ((a0, a1), (b0, b1))
    , ((a0', a1'), (b0', b1')) ]

  for ((ca0, ca1), (cb0, cb1)) in cases do
    let ref := Fp12.mul ⟨ca0, ca1⟩ ⟨cb0, cb1⟩
    let (c0, c1) := scheduleFp12Mul ca0 ca1 cb0 cb1
    if c0 = ref.c0 ∧ c1 = ref.c1 then
      IO.println s!"  ✓ Fp12 schedule matches Fp12.mul (c0.c0.c0={c0.c0.c0})"
    else
      IO.println s!"  ✗ Fp12 mismatch"
      ok := false

  IO.println s!"  · cycle cost per Fp12-mul (Fp6-mul ~300 cyc):"
  IO.println s!"      3 Fp6-muls → ~{3 * 300} cycles"

  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

end Sparkle.Tests.IP.Crypto.Fp12MulHWTest

section SynthesisChecks
open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Crypto.Fp12MulHW

private def synth_fp12MulC00a
    (start : Signal defaultDomain Bool)
    (a00a a00b a01a a01b a02a a02b : Signal defaultDomain (BitVec 384))
    (a10a a10b a11a a11b a12a a12b : Signal defaultDomain (BitVec 384))
    (b00a b00b b01a b01b b02a b02b : Signal defaultDomain (BitVec 384))
    (b10a b10b b11a b11b b12a b12b : Signal defaultDomain (BitVec 384))
    (f6R0a f6R0b f6R1a f6R1b f6R2a f6R2b : Signal defaultDomain (BitVec 384))
    (f6Done : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 384) :=
  (fp12MulHW start a00a a00b a01a a01b a02a a02b a10a a10b a11a a11b a12a a12b
    b00a b00b b01a b01b b02a b02b b10a b10b b11a b11b b12a b12b
    f6R0a f6R0b f6R1a f6R1b f6R2a f6R2b f6Done).c00a

#synthesizeVerilog synth_fp12MulC00a

private def synth_fp12MulDone
    (start : Signal defaultDomain Bool)
    (a00a a00b a01a a01b a02a a02b : Signal defaultDomain (BitVec 384))
    (a10a a10b a11a a11b a12a a12b : Signal defaultDomain (BitVec 384))
    (b00a b00b b01a b01b b02a b02b : Signal defaultDomain (BitVec 384))
    (b10a b10b b11a b11b b12a b12b : Signal defaultDomain (BitVec 384))
    (f6R0a f6R0b f6R1a f6R1b f6R2a f6R2b : Signal defaultDomain (BitVec 384))
    (f6Done : Signal defaultDomain Bool) :
    Signal defaultDomain Bool :=
  (fp12MulHW start a00a a00b a01a a01b a02a a02b a10a a10b a11a a11b a12a a12b
    b00a b00b b01a b01b b02a b02b b10a b10b b11a b11b b12a b12b
    f6R0a f6R0b f6R1a f6R1b f6R2a f6R2b f6Done).done

#synthesizeVerilog synth_fp12MulDone

end SynthesisChecks
