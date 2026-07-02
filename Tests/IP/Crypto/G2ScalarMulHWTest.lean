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

  SYNTH PUNTED.  `g2ScalarMulHW` nests `g2PointOpHW`, whose
  `#synthesizeVerilog` already hits the known super-linear
  translate wall (see G2PointOpHWTest); the ladder's synth is
  likewise punted.  The module builds (elaborates to Signal.loop)
  — `lake build IP.Crypto.G2ScalarMulHW` is the well-formedness
  smoke test — and this schedule-level check validates the ladder
  logic.
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
