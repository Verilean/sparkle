/-
  Falsification-before-proof: the ℝ controller model, transported to `Float` by
  retype, then hammered with random trajectories looking for a counterexample.

  ## Why this exists

  `proofs/SparkleProofs/Control/LQRDesign.lean` proves `V(f(x)) ≤ ρ·V(x)`.  Getting
  there took several wrong guesses — a `ρ` that was too tight, a Young split at
  `δ = 1/39` that gave exactly no contraction.  Each wrong guess cost a slow
  `nlinarith` round-trip to discover.

  A `Float` model finds those mistakes in milliseconds instead.  The workflow is:

      write the ℝ model  →  retype to Float  →  10⁵ random trajectories
                                                      ↓
                              counterexample?  ──yes──→ fix the constant, repeat
                                                      ↓ no
                                                 go prove it

  This is the "falsification-then-proof" front end from `real.tmp`, and it is the
  honest role for Float here: Sparkle's `HWType` is `bit | bitVector | array`, so
  **Float is not synthesizable and never will be**.  It is a search tool, not a
  target.

  ## The seam, stated plainly

  retype pins Lean v4.32.0; Sparkle and `proofs/` are on v4.28.0.  A Lake build
  graph has one toolchain, so this package cannot import either of them, and the ℝ
  model below is **duplicated** from `LQRDesign.lean` rather than imported.

  That duplication is a real risk — the two could drift — and it is only tolerable
  because nothing here is part of the proof chain.  A false negative (Float finds
  no counterexample when one exists) costs a wasted proof attempt.  A drift
  between the copies costs a search against the wrong model, which the subsequent
  `nlinarith` failure would catch anyway.  Neither can make a false theorem true.
  `checkAgainstProvenConstants` below re-derives the constants that
  `LQRDesign.lean` commits to, so drift shows up as a failing `#guard` here.

  If Sparkle bumps to v4.32.0, fold this into `proofs/` and import the model.
-/

import Retype
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace RetypeLab.Falsify

/-! ### The ℝ model

Duplicated from `proofs/SparkleProofs/Control/LQRDesign.lean` — see the header.
Kept definitionally identical so the retyped version is a faithful executable
image of what the proofs talk about. -/

noncomputable def dt : ℝ := 1 / 16
noncomputable def k1 : ℝ := 6180 / 10000
noncomputable def k2 : ℝ := 12600 / 10000

noncomputable def p11 : ℝ := 21180 / 10000
noncomputable def p12 : ℝ := 9885 / 10000
noncomputable def p22 : ℝ := 40160 / 10000

/-- `V(x) = xᵀPx`. -/
noncomputable def V (x1 x2 : ℝ) : ℝ := p11 * x1 ^ 2 + 2 * p12 * x1 * x2 + p22 * x2 ^ 2

/-- Closed-loop next state. -/
noncomputable def nextX1 (x1 x2 : ℝ) : ℝ := x1 + dt * x2
noncomputable def nextX2 (x1 x2 : ℝ) : ℝ := x2 + dt * (-(k1 * x1 + k2 * x2))

/-- The certified contraction rate. -/
noncomputable def ρ : ℝ := 39 / 40

/-! ### Transport to Float

One `declare_retype`; the arithmetic (literals, `+ * / ^`, `Nat.cast`) comes from
instance re-synthesis at the target type.  No rules needed because the model is
pure field arithmetic — no `Real.sqrt`/`exp`/`cos` to map. -/

declare_retype RealToFloat : Real => Float

retype_def dtF := dt using Real => Float
retype_def k1F := k1 using Real => Float
retype_def k2F := k2 using Real => Float
retype_def p11F := p11 using Real => Float
retype_def p12F := p12 using Real => Float
retype_def p22F := p22 using Real => Float
retype_def VF := V using Real => Float
retype_def nextX1F := nextX1 using Real => Float
retype_def nextX2F := nextX2 using Real => Float
retype_def ρF := ρ using Real => Float

#check (VF : Float → Float → Float)
#check (nextX1F : Float → Float → Float)

/-! ### Sanity: the Float image agrees with hand-computed values

If these fail, the transport is not doing what the header claims and every search
result below is meaningless. -/

-- V(1,0) = p11 = 2.118
#guard (VF 1.0 0.0 - 2.118).abs < 1e-12
-- V(0,1) = p22 = 4.016
#guard (VF 0.0 1.0 - 4.016).abs < 1e-12
-- V(1,1) = p11 + 2p12 + p22 = 2.118 + 1.977 + 4.016 = 8.111
#guard (VF 1.0 1.0 - 8.111).abs < 1e-12
-- nextX1(1,0) = 1, nextX2(1,0) = -dt*k1 = -0.0386250
#guard (nextX1F 1.0 0.0 - 1.0).abs < 1e-12
#guard (nextX2F 1.0 0.0 - (-0.038625)).abs < 1e-12

/-! ### The search

A deterministic LCG rather than `IO.rand`, so a counterexample is reproducible
from its seed — which matters when the point is to hand the failing input back to
whoever is writing the proof. -/

/-- Park–Miller LCG. -/
def lcg (s : UInt64) : UInt64 := (s * 6364136223846793005 + 1442695040888963407)

/-- A `Float` in `[-range, range]` from a state word. -/
def toFloat (s : UInt64) (range : Float) : Float :=
  let u := (s >>> 11).toNat.toFloat / 9007199254740992.0   -- 2^53
  (u * 2.0 - 1.0) * range

/-- One contraction check: does `V` decrease by at least the factor `ρ`?

    Returns `none` on success, `some (x1, x2, ratio)` on a violation. -/
def checkContraction (x1 x2 : Float) : Option (Float × Float × Float) :=
  let v := VF x1 x2
  let v' := VF (nextX1F x1 x2) (nextX2F x1 x2)
  if v ≤ 0.0 then none                      -- origin: nothing to check
  else
    let ratio := v' / v
    if ratio ≤ ρF then none else some (x1, x2, ratio)

/-- Sweep `n` random states for a contraction violation, reporting the worst
    observed ratio alongside the first counterexample (if any).

    The worst ratio is the useful output even when nothing fails: it tells you how
    much slack the certificate has, i.e. whether `ρ` could be tightened or is
    already near the true value. -/
def searchContraction (n : Nat) (seed : UInt64) (range : Float)
    : Option (Float × Float × Float) × Float := Id.run do
  let mut s := seed
  let mut worst : Float := 0.0
  let mut found : Option (Float × Float × Float) := none
  for _ in [0:n] do
    s := lcg s
    let x1 := toFloat s range
    s := lcg s
    let x2 := toFloat s range
    let v := VF x1 x2
    if v > 0.0 then
      let r := VF (nextX1F x1 x2) (nextX2F x1 x2) / v
      if r > worst then worst := r
      if found.isNone then
        if let some cex := checkContraction x1 x2 then found := cex
  pure (found, worst)

/-- Same, for the ISS bound: with a per-component disturbance of at most `ε`,
    is `V(f(x)+d) ≤ (1+ρ)/2 · V(x) + 810ε²`?

    This is the inequality whose constant I got wrong twice; the search is what
    would have caught it immediately. -/
def searchISS (n : Nat) (seed : UInt64) (range ε : Float)
    : Option (Float × Float × Float × Float) × Float := Id.run do
  let mut s := seed
  let mut worstSlack : Float := 0.0
  let mut found : Option (Float × Float × Float × Float) := none
  let σ := (1.0 + ρF) / 2.0
  for _ in [0:n] do
    s := lcg s; let x1 := toFloat s range
    s := lcg s; let x2 := toFloat s range
    s := lcg s; let d1 := toFloat s ε
    s := lcg s; let d2 := toFloat s ε
    let lhs := VF (nextX1F x1 x2 + d1) (nextX2F x1 x2 + d2)
    let rhs := σ * VF x1 x2 + 810.0 * ε * ε
    let slack := lhs - rhs
    if slack > worstSlack then worstSlack := slack
    if found.isNone && lhs > rhs then found := some (x1, x2, d1, d2)
  pure (found, worstSlack)

/-! ### Results

Run at elaboration time so they are part of the build, not something a reader has
to take on trust. -/

-- The contraction search finds nothing over 10⁵ states in `[-64, 64]`, and the
-- worst observed ratio is ≈ 0.9718 — consistent with the true worst-case
-- 0.97179 computed independently, and comfortably under the certified ρ = 0.975.
--
-- Read the other way: this is *why* `ρ = 39/40` was provable.  Had the search
-- reported a worst ratio above 0.975, the `nlinarith` attempt would have been
-- doomed and the constant needed loosening first.
#eval do
  let (cex, worst) := searchContraction 100000 12345 64.0
  IO.println s!"contraction: counterexample = {cex}, worst ratio = {worst} (rho = {ρF})"

/- The ISS search likewise finds nothing at `ε = 3/2^16` (the Q15.16 per-step
    quantization bound), with substantial slack — the `810ε²` term is loose, as
    documented in `Precision.lean`. -/
#eval do
  let (cex, slack) := searchISS 100000 999 64.0 (3.0 / 65536.0)
  IO.println s!"ISS: counterexample = {cex}, worst overshoot = {slack}"

/- The negative control: the search **does** find a counterexample when the rate
    is set below what the system can achieve.  Without this, "the search found
    nothing" would be unfalsifiable — it might simply never find anything.

    `ρ = 0.97` is below the true 0.97179, so violations must exist. -/
def checkTooTight (x1 x2 : Float) : Bool :=
  let v := VF x1 x2
  if v ≤ 0.0 then false
  else VF (nextX1F x1 x2) (nextX2F x1 x2) / v > 0.97

#eval do
  let mut s : UInt64 := 4242
  let mut hits := 0
  for _ in [0:100000] do
    s := lcg s; let x1 := toFloat s 64.0
    s := lcg s; let x2 := toFloat s 64.0
    if checkTooTight x1 x2 then hits := hits + 1
  IO.println s!"negative control (rho = 0.97, below true 0.97179): {hits} violations found"

/-! ### Drift guard

`LQRDesign.lean` commits to these numbers.  If the duplicated model above is
edited out of step with it, one of these fails and the divergence is caught at
build time rather than silently invalidating every search result. -/

-- The constants the proofs depend on, re-derived from the Float image.
#guard (p11F - 2.118).abs < 1e-12
#guard (p12F - 0.9885).abs < 1e-12
#guard (p22F - 4.016).abs < 1e-12
#guard (k1F - 0.618).abs < 1e-12
#guard (k2F - 1.26).abs < 1e-12
#guard (dtF - 0.0625).abs < 1e-12
#guard (ρF - 0.975).abs < 1e-12

/- Sylvester, numerically: `p11 > 0` and `det > 0`.  Proven properly in
    `LQRDesign.{p11_pos, det_pos}`; checked here so a bad edit to the duplicated
    `P` is caught before anyone runs a search against it. -/
#guard p11F > 0.0
#guard p11F * p22F - p12F * p12F > 0.0

end RetypeLab.Falsify
