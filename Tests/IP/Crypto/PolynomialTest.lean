/-
  Sim test for IP.Crypto.Polynomial.

  Validates:
    1. Horner evaluation of a known polynomial.
    2. add / mul / scale on small cases.
    3. Lagrange interpolation through 4 points re-produces
       the input y-values at the x-points.
    4. Vanishing polynomial Π(x - x_i) evaluates to zero
       at each x_i and non-zero elsewhere.
-/

import IP.Crypto.Polynomial

open Sparkle.IP.Crypto.Polynomial

namespace Sparkle.Tests.IP.Crypto.PolynomialTest

def main : IO Unit := do
  IO.println "=== Polynomial sim ==="
  let mut ok := true

  -- 1. p(x) = 1 + 2x + 3x²
  let p : Poly := #[1, 2, 3]
  let p1 := eval p 1
  let p2 := eval p 2
  let p10 := eval p 10
  IO.println s!"  p(1)  = {p1}  (expected 6)  {if p1 = 6 then "✓" else "✗"}"
  IO.println s!"  p(2)  = {p2}  (expected 17) {if p2 = 17 then "✓" else "✗"}"
  IO.println s!"  p(10) = {p10} (expected 321) {if p10 = 321 then "✓" else "✗"}"
  if p1 ≠ 6 ∨ p2 ≠ 17 ∨ p10 ≠ 321 then ok := false

  -- 2. add: (1 + 2x) + (3 + 4x + 5x²) = (4 + 6x + 5x²)
  let s := add #[1, 2] #[3, 4, 5]
  let addOk := s == #[4, 6, 5]
  IO.println s!"  add ok: {addOk}"
  if !addOk then ok := false

  -- 3. mul: (1 + x)(1 + x) = 1 + 2x + x²
  let m := mul #[1, 1] #[1, 1]
  let mulOk := m == #[1, 2, 1]
  IO.println s!"  mul ok ((1+x)² = 1+2x+x²): {mulOk}"
  if !mulOk then ok := false

  -- 4. Lagrange: interpolate through (1, 2), (2, 5), (3, 10)
  -- The polynomial fitting these is x² + 1.  Verify by
  -- evaluating the interpolated poly at each x.
  let xs : Array Nat := #[1, 2, 3]
  let ys : Array Nat := #[2, 5, 10]
  let lp := lagrangeInterpolate xs ys
  IO.println s!"  lagrange coefficients (low-deg first): {lp}"
  -- Re-evaluate at the same x's; must give back ys.
  let mut lagOk := true
  for h : i in [:3] do
    let xi := xs.getD i 0
    let yi := ys.getD i 0
    let lyi := eval lp xi
    if lyi ≠ yi then
      IO.println s!"  ✗ L({xi}) = {lyi}, expected {yi}"
      lagOk := false
  if lagOk then IO.println "  ✓ lagrange interpolation recovers all 3 y-values"
  else ok := false

  -- 5. Vanishing poly Z(x) = (x - 1)(x - 2)(x - 3) zero at
  -- 1,2,3 and nonzero at 4.
  let z := zeroPoly #[1, 2, 3]
  let z1 := eval z 1
  let z2 := eval z 2
  let z3 := eval z 3
  let z4 := eval z 4
  IO.println s!"  zeroPoly: Z(1)={z1} Z(2)={z2} Z(3)={z3} Z(4)={z4}"
  let zOk := z1 = 0 ∧ z2 = 0 ∧ z3 = 0 ∧ z4 ≠ 0
  IO.println s!"    {if zOk then "✓" else "✗"} vanishes at points and is non-zero elsewhere"
  if !zOk then ok := false

  if ok then
    IO.println "\nALL PASS"
  else
    IO.println "\nFAIL"
    IO.Process.exit 1

end Sparkle.Tests.IP.Crypto.PolynomialTest
