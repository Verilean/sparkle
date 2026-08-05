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
| The bridge | `proofs/SparkleProofs/Control/Transport.lean` | **yes** | quantization error → ultimate bound |

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
