/-!
# Dense linear solver

A small, dependency-free dense solver (Gaussian elimination with partial
pivoting) over `Float`. Dense is adequate for proof-of-concept circuit sizes; a
sparse factorization is a later optimization, and the heavy inner loop can move
to JIT-compiled C++ if throughput ever demands it.

Matrices are row-major `Array (Array Float)`; the right-hand side and solution
are `Array Float`.
-/

namespace Sparkle.Analog

/-- Solve `A x = b` for a square system. Returns `none` if `A` is singular (a
zero pivot column). Partial pivoting keeps it numerically reasonable. -/
def linSolve (a0 : Array (Array Float)) (b0 : Array Float) : Option (Array Float) := Id.run do
  let n := b0.size
  let mut a := a0
  let mut b := b0
  for k in [0:n] do
    -- Partial pivot: largest |a[i][k]| in column k at or below the diagonal.
    let mut piv := k
    let mut maxv := Float.abs (a[k]!)[k]!
    for i in [k+1:n] do
      let v := Float.abs (a[i]!)[k]!
      if v > maxv then
        piv := i
        maxv := v
    if maxv == 0.0 then
      return none
    if piv != k then
      let rk := a[k]!
      a := a.set! k (a[piv]!)
      a := a.set! piv rk
      let bk := b[k]!
      b := b.set! k (b[piv]!)
      b := b.set! piv bk
    -- Eliminate column k below the diagonal.
    let pivotRow := a[k]!
    let akk := pivotRow[k]!
    for i in [k+1:n] do
      let factor := (a[i]!)[k]! / akk
      if factor != 0.0 then
        let mut row := a[i]!
        for j in [k:n] do
          row := row.set! j (row[j]! - factor * pivotRow[j]!)
        a := a.set! i row
        b := b.set! i (b[i]! - factor * b[k]!)
  -- Back-substitution.
  let mut x := Array.replicate n 0.0
  for kk in [0:n] do
    let i := n - 1 - kk
    let row := a[i]!
    let mut s := b[i]!
    for j in [i+1:n] do
      s := s - row[j]! * x[j]!
    x := x.set! i (s / row[i]!)
  return some x

end Sparkle.Analog
