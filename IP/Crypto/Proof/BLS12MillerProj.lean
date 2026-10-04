/-
  IP.Crypto.BLS12MillerProj — a fully PROJECTIVE Miller loop for
  BLS12-381, the HW-friendly counterpart of the affine
  `Pairing.millerLoop` in `BLS12_381.lean`.

  Why a separate reference:  the existing `Pairing.millerLoop`
  advances the running point in G2 (Jacobian) and calls
  `untwist (G2.toAffine R)` EVERY iteration — a full Fp inverse
  per step.  That is correct but a poor HW datapath.  Here we
  keep the running point as a homogeneous-projective `P12`
  (X : Y : Z over Fp12) and advance it with `double12` / `add12`
  (no inverse), evaluating the generic projective `linefunc`.
  The whole loop needs ZERO Fp12 inversions; we divide the
  accumulated numerator by the denominator exactly ONCE at the
  end.

  This is exactly py_ecc's *optimized* miller loop vs its plain
  one:  the two compute the same Miller function up to a scaling
  in Fp* which the final exponentiation annihilates, so
  `finalExp (millerLoopProj P Q) = pairing P Q`.  The test
  asserts that equality directly against the shipped `pairing`.

  This `millerLoopProj` is the spec the HW Miller-loop FSM
  (`BLS12MillerHW`) mirrors: its per-iteration schedule is a
  line-for-line transcription of the body below.
-/
import IP.Crypto.Proof.BLS12_381

namespace Sparkle.IP.Crypto.BLS12MillerProj

open Sparkle.IP.Crypto.BLS12_381
open Sparkle.IP.Crypto.BLS12_381.Pairing

/-- Fp12 constant `k` in the base (real Fp) slot. -/
private def fpConst (k : Nat) : Fp12.El :=
  ⟨⟨⟨k, 0⟩, Fp2.zero, Fp2.zero⟩, Fp6.zero⟩

/-- Tangent-line function at the projective point `R`, evaluated
    at `T`.  This is the `mDen0 = 0 ∧ mNum0 = 0` (doubling) branch
    of `Pairing.linefunc`, specialised to `P1 = P2 = R` so the HW
    can use it unconditionally on the DOUBLE step. -/
def lineTangent (R T : P12) : Fp12.El × Fp12.El :=
  let x1 := R.x; let y1 := R.y; let z1 := R.z
  let xt := T.x; let yt := T.y; let zt := T.z
  let sx := Fp12.sub (Fp12.mul xt z1) (Fp12.mul x1 zt)
  let sy := Fp12.sub (Fp12.mul yt z1) (Fp12.mul y1 zt)
  let mNum := Fp12.mul (fpConst 3) (Fp12.mul x1 x1)      -- 3 X²
  let mDen := Fp12.mul (fpConst 2) (Fp12.mul y1 z1)      -- 2 Y Z
  let num := Fp12.sub (Fp12.mul mNum sx) (Fp12.mul mDen sy)
  let den := Fp12.mul mDen (Fp12.mul zt z1)
  (num, den)

/-- Chord-line function through the projective points `R` and `Q`,
    evaluated at `T`.  The `mDen0 ≠ 0` (addition) branch of
    `Pairing.linefunc`, used on the ADD step. -/
def lineChord (R Q T : P12) : Fp12.El × Fp12.El :=
  let x1 := R.x; let y1 := R.y; let z1 := R.z
  let x2 := Q.x; let y2 := Q.y; let z2 := Q.z
  let xt := T.x; let yt := T.y; let zt := T.z
  let mNum0 := Fp12.sub (Fp12.mul y2 z1) (Fp12.mul y1 z2)
  let mDen0 := Fp12.sub (Fp12.mul x2 z1) (Fp12.mul x1 z2)
  let sx := Fp12.sub (Fp12.mul xt z1) (Fp12.mul x1 zt)
  let sy := Fp12.sub (Fp12.mul yt z1) (Fp12.mul y1 zt)
  let num := Fp12.sub (Fp12.mul mNum0 sx) (Fp12.mul mDen0 sy)
  let den := Fp12.mul mDen0 (Fp12.mul zt z1)
  (num, den)

/-- The projective Miller loop.  `castP` is the (fixed) G1 point
    embedded in Fp12; `twistQ` the untwisted G2 point.  Both are
    supplied as `P12` so the caller does the one-time
    `embedG1`/`untwist` setup (the HW takes them as inputs). -/
def millerLoopProjP12 (castP twistQ : P12) : Fp12.El := Id.run do
  let mut fNum := Fp12.one
  let mut fDen := Fp12.one
  let mut R := twistQ
  for i in [:63] do
    let v := pseudoBinaryEncoding.getD (62 - i) 0
    -- DOUBLE step: tangent line at R, square the accumulators.
    let (n, d) := lineTangent R castP
    fNum := Fp12.mul (Fp12.mul fNum fNum) n
    fDen := Fp12.mul (Fp12.mul fDen fDen) d
    R := double12 R
    if v == 1 then
      -- ADD step: chord line through R and twistQ.
      let (n2, d2) := lineChord R twistQ castP
      fNum := Fp12.mul fNum n2
      fDen := Fp12.mul fDen d2
      R := add12 R twistQ
  return Fp12.mul fNum (Fp12.inv fDen)

/-- Convenience wrapper taking the same `(G1, G2)` inputs as
    `Pairing.millerLoop`, doing the one-time embed/untwist. -/
def millerLoopProj (P : G1.Point) (Q : G2.Point) : Fp12.El :=
  let (px, py) := G1.toAffine P
  let castP := embedG1 px py
  let (ax, ay) := G2.toAffine Q
  let twistQ := untwist ax ay
  millerLoopProjP12 castP twistQ

/-- The projective pairing: same final exponentiation as the
    shipped `pairing`, over the projective Miller loop. -/
def pairingProj (P : G1.Point) (Q : G2.Point) : Fp12.El :=
  if P.inf || Q.inf then Fp12.one
  else finalExp (millerLoopProj P Q)

end Sparkle.IP.Crypto.BLS12MillerProj
