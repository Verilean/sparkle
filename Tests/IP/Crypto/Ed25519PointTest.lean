/-
  Sim test for IP.Crypto.Ed25519Point.

  Validates:
    1. Base point B is on the curve.
    2. 0 + B = B  (identity laws).
    3. B + 0 = B
    4. B + B = 2·B (consistency between add and double).
    5. n·B is on the curve for several small n.
    6. Order check: l · B = 0  where
       l = 2^252 + 27742317777372353535851937790883648493
       (the curve order per RFC 8032 §5.1).
-/

import IP.Crypto.Proof.Ed25519Point

open Sparkle.IP.Crypto.Ed25519Point

namespace Sparkle.Tests.IP.Crypto.Ed25519PointTest

/-- Curve order l per RFC 8032. -/
def curveOrderL : Nat :=
  2^252 + 27742317777372353535851937790883648493

def main : IO Unit := do
  IO.println "=== Ed25519 point arithmetic sim ==="
  let mut ok := true

  -- 1. Base point on curve?
  let baseOk := onCurve base
  IO.println s!"  base point on curve = {baseOk} (expected true)"
  if !baseOk then ok := false

  -- 2. Identity laws.
  let z := zero
  let l1 := add z base
  let id0Ok := l1 == base
  IO.println s!"  0 + B = B → {id0Ok}"
  if !id0Ok then ok := false

  let r1 := add base z
  let id1Ok := r1 == base
  IO.println s!"  B + 0 = B → {id1Ok}"
  if !id1Ok then ok := false

  -- 3. add p p == double p
  let dBase := double base
  let twoB := add base base
  let dblOk := dBase == twoB
  IO.println s!"  B + B = double B → {dblOk}"
  if !dblOk then ok := false

  -- 4. 2·B, 3·B both on the curve.
  let twoOnCurve := onCurve twoB
  IO.println s!"  2·B on curve → {twoOnCurve}"
  if !twoOnCurve then ok := false

  let threeB := add twoB base
  let threeOnCurve := onCurve threeB
  IO.println s!"  3·B on curve → {threeOnCurve}"
  if !threeOnCurve then ok := false

  -- 5. mulScalar consistency: mulScalar 3 B == 3·B
  let mul3 := mulScalar 3 base
  let mul3Ok := mul3 == threeB
  IO.println s!"  mulScalar 3 B = B + B + B → {mul3Ok}"
  if !mul3Ok then ok := false

  -- 6. Order check: l · B = identity (0, 1).
  --    This is the most stringent invariant — proves the
  --    group law + scalar-mult implementation agrees with
  --    the curve's defined order.  Costs ~252 iterations
  --    of add/double, each ~3 inversions = ~600 Fermat
  --    powMods.  Slow but tractable in Lean sim.
  IO.println "  (computing l · B — may take 30s..)"
  let lB := mulScalar curveOrderL base
  let lBIsZero := lB == zero
  IO.println s!"  l · B = (0, 1) → {lBIsZero}"
  if !lBIsZero then ok := false

  if ok then
    IO.println "\nALL PASS"
  else
    IO.println "\nFAIL"
    IO.Process.exit 1

end Sparkle.Tests.IP.Crypto.Ed25519PointTest
