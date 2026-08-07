# sparkle-proofs — the ℝ ↔ fixed-point bridge

A **sidecar** Lake package. It is not part of Sparkle.

## Why it is separate

Sparkle is an HDL. It has nothing to do with real analysis or control theory,
and the circuits in `IP/Control/` are ordinary fixed-point integer arithmetic —
no Mathlib, no `ℝ`. That is deliberate: `lake build` at the repo root, the path
an RTL user takes, must not pay for Mathlib.

What *does* need Mathlib is the argument that the coefficients baked into those
circuits are the right ones. Proving a controller stable means quadratic forms,
positive-definite matrices, and a decay rate — i.e. `ℝ`, `nlinarith`,
`positivity`. So that argument lives here, in a package that depends on both
Mathlib and Sparkle, and nothing in the main build graph depends on it.

Same pattern as `docbuild/`: `packagesDir = "../.lake/packages"` shares the
package cache, `[[require]] name = "sparkle" path = "../"` points back at the
main package.

## The split, concretely

| | Where | Mathlib? | What it is |
|---|---|---|---|
| Circuits | `IP/Control/*.lean` | no | Q15.16 `BitVec 32`, synthesizes to Verilog |
| Cycle-accurate tests | `Tests/IP/Control/*.lean` | no | LSpec + `#synthesizeVerilog` |
| ℝ design + Lyapunov | `proofs/SparkleProofs/Control/LQRDesign.lean` | **yes** | `V = xᵀPx`, contraction, ISS |
| The bridge | `proofs/SparkleProofs/Control/Transport.lean` | **yes** | quantization error → ultimate bound (Q15.16) |
| Precision selection | `proofs/SparkleProofs/Control/Precision.lean` | **yes** | the bound as a function of `f`; which formats meet a budget |
| ℝ⇒Float falsification | `retypelab/` (separate pkg, **v4.32.0**) | yes (v4.32.0) | counterexample search before proving |

## What is actually proven

`LQRDesign.lean` — over `ℝ`, for the double integrator with the shipped gain
`K = [0.618, 1.26]` and the exhibited Riccati matrix `P`:

- `p11_pos`, `det_pos` — `P ≻ 0` by Sylvester's criterion.
- `V_lower`, `V_upper` — the sandwich `½‖x‖² ≤ V(x) ≤ 5‖x‖²`.
- **`lyapunov_decrease`** — `V(f(x)) ≤ ρ·V(x)` with `ρ = 39/40`. The true
  worst-case ratio is 0.97179, so the certificate has real slack.
- **`lyapunov_iss`** — the contraction survives an additive per-component
  disturbance of size `ε`, degrading to rate `(1+ρ)/2 = 79/80` plus a `810ε²`
  floor. Proven via an explicit Young split at `δ = 1/80`, chosen so
  `(1+δ)·ρ = 0.98719` stays inside the margin.

`Transport.lean` — the connection to the integers:

- **`mulQ_error`** — one Q15.16 multiply is the exact rational product floored
  to a multiple of `2⁻¹⁶`, so its error lies in `(-1, 0]` LSB. The interval is
  *one-sided* because Lean's `Int./` floors and `BitVec.sshiftRight` floors, so
  the RTL's shifter and the spec's division are the same function. A truncating
  shifter would make the error sign-dependent and double the bound.
- **`ultimate_bound`** — for every trajectory of the quantized loop,
  `V(x_n) ≤ σⁿ·V(x₀) + Vbound`, by induction on `n`. Unbounded, kernel-checked.
- **`ultimate_norm_bound`** — the same as a bound on `‖x‖²`.

Axiom base is `[propext, Classical.choice, Quot.sound]` — the three standard
ones; `Classical.choice` arrives with `ℝ` itself. No `sorry`, no custom axioms.

## Precision selection — `Precision.lean`

`Transport.lean` fixes Q15.16.  `Precision.lean` makes the fractional-bit count a
variable, giving `Vbound f = 583200 / 4^f` in closed form, and then decides the
engineering question:

- `Vbound_succ` — each extra fractional bit cuts the bound 4×;
- `Vbound_antitone` — finer is never worse;
- `q7_8_misses_budget`, `q11_4_misses_budget` — Q7.8 and Q11.4 miss a `V ≤ 0.01`
  budget (Vbound 8 ≈ 8.9, Vbound 4 ≈ 2278);
- `q15_16_meets_budget` — Q15.16 meets it (≈ 1.4e-4);
- **`min_fracBits_for_budget`** — 13 fractional bits is exactly the threshold: 12
  is not enough, 13 is, and every `f ≥ 13` follows by monotonicity.

The bound depends on `f` alone, never on the total width `w`. That is not an
omission — it is the point, and the measured sweep agrees: Q7.8 (16-bit) and
Q23.8 (32-bit) give bit-identical output because they share `f = 8`.

**What it does not cover:** coefficient rounding, which moves the poles (perturbs
`ρ`) rather than adding a disturbance. Worth knowing because the naive guess about
that is wrong — for `IIRBiquadGen.marginalCoeffs`, coarse quantization pulls the
poles *inward* and *damps* the filter, so the measured residual is non-monotone in
`f`. See `Tests/IP/Control/PrecisionSweepTest.lean`.

## ℝ ⇒ Float falsification — `retypelab/`

A second sidecar. It is no longer a *toolchain* split — root, `proofs/` and
`retypelab/` are all on **v4.32.1** — but it is still its own Lake package with
its own mathlib copy, so the ℝ model is duplicated rather than imported;
folding it in is the pending follow-up. It uses
`declare_retype RealToFloat : Real => Float` and `retype_def` to turn the ℝ
controller model into executable `Float`, then searches 10⁵ random trajectories
for a contraction or ISS violation before anyone spends time on `nlinarith`.

Measured on build:

```
contraction: counterexample = none, worst ratio = 0.971789  (certified ρ = 0.975)
ISS:         counterexample = none, worst overshoot = 0
negative control (ρ = 0.97, below the true 0.97179): 4832 violations found
```

The worst ratio 0.971789 matches the independently-computed true worst case, and
the negative control is what makes "found nothing" meaningful rather than
vacuous — the search demonstrably *can* fail.

Float is **not** a synthesis target and never can be: Sparkle's `HWType` is
`bit | bitVector | array`. It is a search tool. The cost of the toolchain split is
that the ℝ model is *duplicated* there rather than imported; `#guard`s on the
proven constants catch drift at build time. Fold it into `proofs/` if Sparkle ever
moves to v4.32.0.

## Estimator certificates — `EstimatorDesign.lean`

For the Kalman / H∞ pair in `IP/Control/Observer.lean` (same RTL, different
gain constants):

- `kf_contraction`, `hinf_contraction` — both error dynamics contract at
  ρ = 0.98.  Shared; says nothing about which filter to pick.
- **`hinf_dissipation`** — only the H∞ gain satisfies
  `V(e⁺) − V(e) ≤ 128w² + 400v² − ‖e‖²` for ALL disturbances (γ = 2,
  weighted supply), proven by handing `nlinarith` the rows of an exact
  rational LDLᵀ of the Gram matrix (pivots 551.3 / 6.60 / 4.57 / 14.27).
- **`hinf_energy_bound`** — the telescoped worst-case guarantee:
  Σ‖e‖² ≤ Σ(128w² + 400v²) + V(e₀) over any horizon, no distributional
  assumption.  This is the theorem that distinguishes the two filters; the
  measured 9 % adversarial win is the anecdote, this is the product.

The LDLᵀ-hint recipe generalizes: compute the certificate's Gram matrix
over exact rationals offline, LDLᵀ-decompose it exactly, hand the rows to
`nlinarith` as `sq_nonneg` hints.  Every quadratic-form proof in this
package now follows it.

## Honest scope

Two gaps, both stated rather than papered over:

1. **The `Signal`-level step is not yet proven.** That the `circuit do` in
   `LQRStateFeedback.lean` computes exactly `LQR.step` every cycle is provable
   with `Sparkle.Verification.LoopProps.loop_iterate` (see
   `Sparkle/Verification/Divider/` for the worked multi-register precedent) and
   needs no Mathlib, but it is not written yet. `Transport.lean` assumes it.
   Until it exists, the chain is: proven ℝ→quantized, *assumed* quantized→RTL,
   with the RTL side checked by cycle-accurate simulation instead.
2. **`P` and `K` are exhibited, not derived.** They are a verified *certificate*
   — the Lyapunov inequality is proven for them — but the DARE solve that
   produced them happened outside Lean. That is the normal shape of a Lyapunov
   argument (guess-and-verify), and the verification is what carries the weight.

## Build

```
cd proofs && lake exe cache get && lake build
```

Needs the Mathlib olean cache; the first `cache get` also builds `batteries`,
`aesop`, `Qq`, `importGraph`, `plausible` and `ProofWidgets` from source
(~10 min). The main `sparkle` package builds without any of this.
