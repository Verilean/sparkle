/-
  IP.Crypto.Polynomial — polynomial operations over the
  Goldilocks field, used as the algebraic primitive in
  STARK-style ZK schemes.

  A polynomial is represented as an `Array Nat` of
  coefficients, low-degree-first:
    p(x) = c₀ + c₁ x + c₂ x² + ... + c_{n-1} x^{n-1}

  Provides:
    * `eval` — Horner evaluation at a field point.
    * `add` / `mul` / `scale` — polynomial arithmetic.
    * `lagrangeInterpolate` — interpolate (x_i, y_i) points
      into a polynomial of degree n-1.
    * `zeroPoly` — the vanishing polynomial Π(x - x_i)
      of a list of points.

  Pure-data only.  HW variants for evaluation domains in
  the form {ω^0, ω^1, ..., ω^{n-1}} (FFT-friendly) follow
  in a future phase.
-/

import IP.Crypto.Goldilocks

namespace Sparkle.IP.Crypto.Polynomial

abbrev fAdd := Sparkle.IP.Crypto.Goldilocks.add
abbrev fSub := Sparkle.IP.Crypto.Goldilocks.sub
abbrev fMul := Sparkle.IP.Crypto.Goldilocks.mul
abbrev fInv := Sparkle.IP.Crypto.Goldilocks.inv
abbrev fP   := Sparkle.IP.Crypto.Goldilocks.p

/-- A polynomial: array of coefficients, low-degree first.
    The empty array represents the zero polynomial. -/
abbrev Poly := Array Nat

/-- Degree of a polynomial.  Returns 0 for the zero
    polynomial (no leading term). -/
def degree (p : Poly) : Nat := Id.run do
  -- Find the highest index with a non-zero coefficient.
  let mut d : Nat := 0
  for h : i in [:p.size] do
    if p.getD i 0 ≠ 0 then d := i
  return d

/-- Horner evaluation: p(x) = ((c_{n-1} x + c_{n-2}) x + …
    c_1) x + c_0.  Computed back-to-front so each iteration
    is a multiply-and-add. -/
def eval (p : Poly) (x : Nat) : Nat := Id.run do
  let n := p.size
  if n = 0 then return 0
  let mut acc := p.getD (n - 1) 0
  let mut i := n - 1
  while i > 0 do
    i := i - 1
    acc := fAdd (fMul acc x) (p.getD i 0)
  return acc

/-- Polynomial addition: (p + q)[i] = p[i] + q[i]. -/
def add (p q : Poly) : Poly := Id.run do
  let n := max p.size q.size
  let mut out : Poly := #[]
  for i in [:n] do
    out := out.push (fAdd (p.getD i 0) (q.getD i 0))
  return out

/-- Polynomial scaling: out[i] = c * p[i]. -/
def scale (c : Nat) (p : Poly) : Poly := Id.run do
  let mut out : Poly := #[]
  for x in p do
    out := out.push (fMul c x)
  return out

/-- Polynomial multiplication via the naïve schoolbook
    O(n²) algorithm.  For small degrees (≤ 32) this is
    fine. -/
def mul (p q : Poly) : Poly := Id.run do
  if p.size = 0 ∨ q.size = 0 then return #[]
  let out_size := p.size + q.size - 1
  let mut out : Poly := Array.replicate out_size 0
  for h : i in [:p.size] do
    for h2 : j in [:q.size] do
      let v := out.getD (i + j) 0
      out := out.set! (i + j) (fAdd v (fMul (p.getD i 0) (q.getD j 0)))
  return out

/-- The vanishing polynomial for a list of x-points:
    Z(x) = Π_i (x - x_i). -/
def zeroPoly (points : Array Nat) : Poly := Id.run do
  let mut acc : Poly := #[1]  -- the constant polynomial 1
  for xi in points do
    -- multiply by (x - xi)
    let lin : Poly := #[fSub 0 xi, 1]
    acc := mul acc lin
  return acc

/-- Lagrange interpolation through n (x_i, y_i) points,
    producing a polynomial of degree ≤ n - 1.

      L(x) = Σ_i y_i · Π_{j ≠ i} (x - x_j) / (x_i - x_j)

    Computes each Lagrange basis polynomial L_i, scales by
    y_i, and sums.

    Inputs:
      xs, ys : same length n.  xs must be all distinct
      (else the denominator is zero). -/
def lagrangeInterpolate (xs ys : Array Nat) : Poly := Id.run do
  let n := xs.size
  let mut acc : Poly := #[]
  for h : i in [:n] do
    let xi := xs.getD i 0
    let yi := ys.getD i 0
    -- Numerator: Π_{j ≠ i} (x - x_j).
    let mut numer : Poly := #[1]
    let mut denom : Nat := 1
    for h2 : j in [:n] do
      if j ≠ i then
        let xj := xs.getD j 0
        numer := mul numer #[fSub 0 xj, 1]
        denom := fMul denom (fSub xi xj)
    -- L_i(x) = (yi / denom) · numer
    let coeff := fMul yi (fInv denom)
    acc := add acc (scale coeff numer)
  return acc

end Sparkle.IP.Crypto.Polynomial
