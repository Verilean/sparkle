/-
  Test for IP.Crypto.P256PointJac — LOCKS the a = -3 Jacobian
  doubling formula against the trusted affine `P256Point`.

  This is the de-risking gate for the whole P-256 HW sign stack:
  the bit-serial DOUBLE hardware schedule is transcribed from the
  `P256PointJac.double` formula validated here, so a wrong a = -3
  doubling shows up as a FAIL here (pure data) rather than as a
  silent-wrong signature deep in hardware.
-/

import IP.Crypto.Proof.P256PointJac
import IP.Crypto.Proof.P256Point

open Sparkle.IP.Crypto

namespace Sparkle.Tests.IP.Crypto.P256PointJacTest

/-- Affine (x, y) of a `P256Point`, using (0,0) for infinity. -/
private def affOf : P256Point.Point → Nat × Nat
  | .infinity    => (0, 0)
  | .affine x y  => (x, y)

def main : IO Unit := do
  IO.println "=== P256PointJac (a=-3 Jacobian) vs affine P256Point ==="
  (← IO.getStdout).flush
  let mut ok := true

  let g : P256Point.Point := P256Point.base
  let gJac := P256PointJac.generator

  -- 1. onCurve sanity for the generator.
  if P256PointJac.onCurve gJac then
    IO.println "  ✓ generator on curve (Jacobian)"
  else
    IO.println "  ✗ generator NOT on curve"; ok := false

  -- 2. double G matches.
  let jDbl := P256PointJac.toAffine (P256PointJac.double gJac)
  let aDbl := affOf (P256Point.double g)
  if jDbl == aDbl then
    IO.println "  ✓ double G matches affine (a=-3 doubling correct)"
  else
    IO.println s!"  ✗ double G mismatch: jac {jDbl} vs aff {aDbl}"; ok := false

  -- 3. add(G, 2G) = 3G.
  let twoG := P256PointJac.double gJac
  let threeGJac := P256PointJac.toAffine (P256PointJac.add gJac twoG)
  let threeGAff := affOf (P256Point.add g (P256Point.double g))
  if threeGJac == threeGAff then
    IO.println "  ✓ add(G, 2G) = 3G matches affine"
  else
    IO.println s!"  ✗ 3G mismatch: jac {threeGJac} vs aff {threeGAff}"; ok := false

  -- 4. mulScalar for several k, incl. large scalars.
  let ks : List Nat :=
    [ 2, 3, 5, 7, 255, 65537,
      0xC9AFA9D845BA75166B5C215767B1D6934E50C3DB36E89B127B8A622B120F6721 ]
  for k in ks do
    let jm := P256PointJac.toAffine (P256PointJac.mulScalar k gJac)
    let am := affOf (P256Point.mulScalar k g)
    if jm == am then
      IO.println s!"  ✓ [k·G matches] k={k}"
    else
      IO.println s!"  ✗ k·G mismatch k={k}: jac {jm} vs aff {am}"; ok := false

  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

end Sparkle.Tests.IP.Crypto.P256PointJacTest
