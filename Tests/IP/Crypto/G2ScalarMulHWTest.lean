/-
  Sim test for IP.Crypto.G2ScalarMulHW.g2ScalarMulHW — the
  BLS12-381 G2 Montgomery-ladder scalar multiplier (the BLS
  signing datapath: σ = k·P).

  Behavioural: `ladderSpec` re-executes the EXACT register-update
  logic of `g2ScalarMulHW` (MSB-first over bits 254..0, invariant
  R1 = R0 + P, `r0Inf` flag for the leading-∞ prefix), using the
  pure-data `BLS12_381.G2.double`/`add` for the point ops, and
  cross-checks the final R0 against `BLS12_381.G2.mulScalar` on
  several scalars applied to G2.generator.

  Synth: the ladder drives `g2PointOpHW` over start/done PORTS (it
  does not inline it), so its own body is just the 12-register
  Fp2-coord ladder controller — `#synthesizeVerilog` completes in
  ~2 s.  (The former super-linear translate wall that had blocked
  the G2 stack is fixed by the O(1) wire-name collision check in
  Sparkle/IR/Builder.lean.)  See `section SynthesisChecks` below.
-/
import Sparkle
import IP.Crypto.BLS12_381
import IP.Crypto.G2ScalarMulHW

open Sparkle.IP.Crypto.BLS12_381

namespace Sparkle.Tests.IP.Crypto.G2ScalarMulHWTest

abbrev Pt := G2.Point

/-- Pure-data re-execution of the `g2ScalarMulHW` ladder register
    logic.  Mirrors the FSM exactly:
      R0 = ∞ (r0Inf=true), R1 = P
      for i = 254 downto 0:
        bit = bit_i(k)
        -- ADD phase: sum = (r0Inf ? R1 : R0+R1)
        --   bit=1 ⇒ R0 := sum (and clear r0Inf) ; bit=0 ⇒ R1 := sum
        -- DBL phase: dbl = 2·(bit ? R1 : R0)
        --   bit=0 ⇒ R0 := dbl ; bit=1 ⇒ R1 := dbl
    Returns R0. -/
private def ladderSpec (k : Nat) (P : Pt) : Pt := Id.run do
  let mut r0 : Pt := G2.infinity
  let mut r1 : Pt := P
  let mut r0Inf : Bool := true
  let mut i : Nat := 255
  while i > 0 do
    i := i - 1                              -- i now ranges 254 downto 0
    let bit := (k >>> i) &&& 1 = 1
    -- ADD phase.
    let sum := if r0Inf then r1 else G2.add r0 r1
    if bit then
      r0 := sum
      r0Inf := false
    else
      r1 := sum
    -- DOUBLE phase.
    let base := if bit then r1 else r0
    let dbl := G2.double base
    if bit then
      r1 := dbl
    else
      r0 := dbl
  return r0

def main : IO Unit := do
  IO.println "=== BLS12-381 G2 scalar-mul ladder FSM logic check ==="
  (← IO.getStdout).flush
  let mut ok := true

  let G := G2.generator
  -- Compare ladder logic vs. the double-and-add reference on
  -- several scalars.  (Both use the same G2.double/add, so this
  -- checks the ladder's sequencing/flag logic is correct.)
  for k in [1, 2, 3, 7, 8, 12345, 0xDEADBEEF] do
    let viaLadder := ladderSpec k G
    let viaRef := G2.mulScalar k G
    -- Compare in affine form (Jacobian reps are not unique).
    if G2.toAffine viaLadder = G2.toAffine viaRef then
      IO.println s!"  ✓ ladder k={k} matches G2.mulScalar"
    else
      IO.println s!"  ✗ ladder k={k} MISMATCH"
      ok := false

  IO.println s!"  · cycle cost per G2 scalar-mul (255-bit, Fp2-mul ~48 cyc):"
  IO.println s!"      ≈ 255 · (16+7) Fp2-muls · 48 ≈ {255 * 23 * 48} cycles"

  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

end Sparkle.Tests.IP.Crypto.G2ScalarMulHWTest

section SynthesisChecks
open Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.IP.Crypto.G2ScalarMulHW

-- The ladder controller synthesizes cleanly (~2 s): it drives the
-- point-op over ports rather than inlining it, so its body is only
-- the 12-register Fp2 ladder + phase FSM.
private def synth_g2ScalarMul_x0
    (start : Signal defaultDomain Bool) (k : Signal defaultDomain (BitVec 256))
    (px0 px1 py0 py1 pz0 pz1 : Signal defaultDomain (BitVec 384))
    (rx0 rx1 ry0 ry1 rz0 rz1 : Signal defaultDomain (BitVec 384))
    (rdone : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 384) :=
  (g2ScalarMulHW start k px0 px1 py0 py1 pz0 pz1 rx0 rx1 ry0 ry1 rz0 rz1 rdone).x0Out

#synthesizeVerilog synth_g2ScalarMul_x0

private def synth_g2ScalarMul_done
    (start : Signal defaultDomain Bool) (k : Signal defaultDomain (BitVec 256))
    (px0 px1 py0 py1 pz0 pz1 : Signal defaultDomain (BitVec 384))
    (rx0 rx1 ry0 ry1 rz0 rz1 : Signal defaultDomain (BitVec 384))
    (rdone : Signal defaultDomain Bool) : Signal defaultDomain Bool :=
  (g2ScalarMulHW start k px0 px1 py0 py1 pz0 pz1 rx0 rx1 ry0 ry1 rz0 rz1 rdone).done

#synthesizeVerilog synth_g2ScalarMul_done

end SynthesisChecks
