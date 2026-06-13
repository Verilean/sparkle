import Sparkle.Analog.Complex

/-!
# Dense linear solver

A small, dependency-free dense solver (Gaussian elimination with partial
pivoting). Dense is adequate for proof-of-concept circuit sizes; a sparse
factorization is a later optimization, and the heavy inner loop can move to
JIT-compiled C++ if throughput ever demands it.

There is no suitable reusable Lean package for this: Mathlib's linear algebra is
`noncomputable` (built for proofs over exact fields, not numerical `Float`), and
the one numerical library, SciLean, drags in Mathlib + OpenBLAS — both of which
would break this simulator's Mathlib-free, WASM-light design. So the algorithm is
hand-rolled here, but written *once*: `linSolveGen` is generic over the scalar
carrier (`Pivotable`), and the real (`linSolve`) and complex (`linSolveComplex`)
solvers — the DC/transient and AC paths respectively — are both instantiations of
it, sharing a single implementation.

Matrices are row-major `Array (Array α)`; the right-hand side and solution are
`Array α`.
-/

namespace Sparkle.Analog

/-- What Gaussian elimination needs of a scalar carrier beyond the field
operations: a zero, and a real magnitude for pivot selection and singularity
detection. `Float` pivots on `|x|`, `Complex` on `‖z‖`. -/
class Pivotable (α : Type) where
  zero : α
  magnitude : α → Float

instance : Pivotable Float where
  zero := 0.0
  magnitude := Float.abs

instance : Pivotable Complex where
  zero := Complex.ofFloat 0.0
  magnitude := Complex.magnitude

/-- Solve `A x = b` for a square system by Gaussian elimination with partial
pivoting, generic over the scalar carrier. Returns `none` if `A` is singular (a
zero-magnitude pivot column). -/
def linSolveGen {α : Type} [Inhabited α] [Add α] [Sub α] [Mul α] [Div α] [Pivotable α]
    (a0 : Array (Array α)) (b0 : Array α) : Option (Array α) := Id.run do
  let n := b0.size
  let mut a := a0
  let mut b := b0
  for k in [0:n] do
    -- Partial pivot: largest magnitude in column k at or below the diagonal.
    let mut piv := k
    let mut maxv := Pivotable.magnitude (a[k]!)[k]!
    for i in [k+1:n] do
      let v := Pivotable.magnitude (a[i]!)[k]!
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
      let mut row := a[i]!
      for j in [k:n] do
        row := row.set! j (row[j]! - factor * pivotRow[j]!)
      a := a.set! i row
      b := b.set! i (b[i]! - factor * b[k]!)
  -- Back-substitution.
  let mut x := Array.replicate n Pivotable.zero
  for kk in [0:n] do
    let i := n - 1 - kk
    let row := a[i]!
    let mut s := b[i]!
    for j in [i+1:n] do
      s := s - row[j]! * x[j]!
    x := x.set! i (s / row[i]!)
  return some x

/-- Real dense solve — the DC and transient path. -/
def linSolve (a0 : Array (Array Float)) (b0 : Array Float) : Option (Array Float) :=
  linSolveGen a0 b0

/-- Complex dense solve — the AC small-signal path. -/
def linSolveComplex (a0 : Array (Array Complex)) (b0 : Array Complex) :
    Option (Array Complex) :=
  linSolveGen a0 b0

end Sparkle.Analog
