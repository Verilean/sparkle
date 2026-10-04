/-
  IP.Crypto.MiniSTARK — toy polynomial commitment scheme
  that captures the HW-primitive shape of a STARK verifier
  without the soundness-amplifying FRI layer.

  Protocol:
    Setup:
      Prover has a polynomial p(x) over Goldilocks, degree
      ≤ d.  Chooses an evaluation domain D = {x_0, x_1, ...,
      x_{N-1}} with N > d, computes y_i = p(x_i).
      Commits to [y_0..y_{N-1}] as a Merkle tree → root.

    Open:
      Verifier picks an index j.  Prover sends:
        * y_j  (the leaf value)
        * the Merkle authentication path
      The polynomial p (its coefficients) is also revealed
      to the verifier (the "evaluation oracle" part of a
      real STARK is what FRI provides).

    Verify:
      1. Merkle path checks → leaf y_j is in the committed set.
      2. Horner-eval p(x_j) and compare with y_j.

  Real STARKs replace step 2's full coefficient reveal with
  a FRI-based low-degree-test.  This toy keeps the wire
  format identical but skips the soundness amplification —
  the "I know p" part is delegated to coefficient reveal.

  Sufficient as a demo for the HW pieces a real STARK
  verifier needs:
    * Merkle leaf hashing  (handled by IP.Crypto.Merkle)
    * Field arithmetic     (Goldilocks)
    * Horner evaluation    (Polynomial)
-/

import IP.Crypto.Proof.Merkle
import IP.Crypto.Proof.Polynomial
import IP.Crypto.Proof.Goldilocks

namespace Sparkle.IP.Crypto.MiniSTARK

open Sparkle.IP.Crypto.Merkle (Digest commit openAt verifyOpen)
open Sparkle.IP.Crypto.Polynomial (Poly eval)
open Sparkle.IP.Crypto.Goldilocks (p)

/-- Prover's setup: given p (coefficients, low-deg first)
    and an evaluation domain `xs`, returns the (root,
    evaluations) pair. -/
def commitPoly (poly : Poly) (xs : Array Nat) :
    Digest × Array Nat := Id.run do
  let mut ys : Array Nat := #[]
  for h : i in [:xs.size] do
    let xi := xs.getD i 0
    ys := ys.push (eval poly xi)
  return (commit ys, ys)

/-- Prover's open at index j: produce (claimed_y, auth_path).
    Requires the same domain to be reproduced. -/
def openPoly (ys : Array Nat) (j : Nat) :
    Nat × Array Digest :=
  (ys.getD j 0, openAt ys j)

/-- Verifier: given the polynomial (claimed by the prover),
    domain, root, opening index, claimed value, auth path —
    return true iff the opening is consistent. -/
def verifyOpenPoly
    (poly : Poly) (xs : Array Nat) (root : Digest)
    (j : Nat) (claimedY : Nat) (path : Array Digest) :
    Bool :=
  -- 1. Merkle authentication.
  let merkleOk := verifyOpen root claimedY j path
  -- 2. Polynomial evaluation consistency.
  let xj := xs.getD j 0
  let yEval := eval poly xj
  let polyOk := yEval == claimedY
  merkleOk && polyOk

end Sparkle.IP.Crypto.MiniSTARK
