# IP.Control — fixed-point control datapaths with transported Lyapunov proofs

Q15.16 signed arithmetic on `BitVec 32`. Three synthesizable blocks, plus a
machine-checked stability argument that lives in the `proofs/` sidecar.

## The blocks

| Module | What | State |
|---|---|---|
| `IP/Control/FixedPoint.lean` | Q15.16 widening multiply, saturating add, symmetric clamp — and the `Signal` versions that lower to Verilog | — |
| `IP/Control/IIRBiquad.lean` | Direct-Form-II-transposed biquad, saturating | 2 regs |
| `IP/Control/PID.lean` | PID with anti-windup, plus a closed loop against a first-order plant | 2 (+1) regs |
| `IP/Control/LQRStateFeedback.lean` | 2-state LQR feedback on a double integrator | 2 regs |

All six tops (`stableBiquad`, `naiveBiquad`, `demoPID`, `closedLoopCircuit`,
`demoLQR`, `lqrController`) pass `#synthesizeVerilog` and are iverilog-clean.

## The point of the design: clamps make boundedness structural

Every state register goes through `clampSym` *inside* the update, not after it.
So the reachable state set is contained in `[-lim, lim]` by construction, for
any coefficients and any input — overflow-freedom needs no stability argument at
all, just one case split on two comparators.

What that does **not** give you is convergence. A badly tuned controller will sit
at the rails or oscillate forever while respecting every bound. Separating the
two claims is what makes the interesting one tractable:

- *bounded* → structural, holds unconditionally, checked by simulation;
- *converges* → needs a Lyapunov function, proven over ℝ in `proofs/` and
  transported to the fixed-point implementation.

## The stable / limit-cycling contrast

`IIRBiquad.lean` ships two instances of the same block:

- **`stableLPF`** — 2nd-order low-pass, poles at |p| ≈ 0.651. Decays to exactly
  zero after an impulse and stays there.
- **`naiveLPF`** — a resonator whose ℝ poles sit at radius 0.999 (stable), but
  whose coefficients rounded to a coarse grid land on `a1 = -1, a2 = 1`, i.e.
  radius exactly 1. From a *single impulse with zero input thereafter* it
  sustains the period-6 limit cycle

  ```
  62, 62, 0, -63, -63, 0, 62, 62, 0, -63, -63, 0, …    (×1e-3, forever)
  ```

  `Tests/IP/Control/IIRBiquadTest.lean` pins that sequence, and running the
  **emitted Verilog** under iverilog reproduces it — the oscillation is in the
  hardware, not just the model.

  The up/down asymmetry (`62` vs `-63`) is the floor-rounding of the arithmetic
  shift, so this is a genuine fixed-point artefact rather than the ℝ resonator's
  ringing.

This is the DSVerifier limit-cycle scenario, reached without doing anything
obviously stupid — and the contrast is the demo: the good filter's stability is
an *unbounded* theorem, where a BMC tool could only check a finite horizon.

## Where the proofs are, and why not here

`proofs/` — a separate Lake package that depends on Mathlib. Sparkle is an HDL;
it has nothing to do with real analysis, and keeping the two apart means
`lake build` at the repo root never pays for Mathlib. See `proofs/README.md` for
the full list of theorems, the axiom base, and two honestly-stated gaps (the
`Signal`-level step equality is not yet written, and `P`/`K` are verified
certificates rather than in-Lean DARE solutions).

The short version of what is proven: `V(x) = xᵀPx` contracts by `ρ = 39/40` for
the ℝ closed loop; the contraction survives a bounded disturbance (ISS); one
Q15.16 multiply errs by at most one LSB in a *one-sided* interval (because
`sshiftRight` and Lean's `Int./` both floor); therefore the quantized loop obeys
`V(xₙ) ≤ σⁿV(x₀) + Vbound` for all `n`, by induction.

`Tests/IP/Control/LQRTest.lean` closes the loop on that claim from the other
side: it evaluates the *same* `P` on the trajectory the integer circuit actually
computes and asserts `V` is non-increasing. Retune the gain without redoing the
certificate and it fails.

## Estimators and the Q divider (2026-08 additions)

| Module | What | Cycles |
|---|---|---|
| `DividerQ.lean` | width-generic restoring divider + Q-format division `(a·2^f)/b`, saturating, symmetric range | `w+f+2` per divide |
| `Observer.lean : fixedGainObserver` | predictor-form observer; **Kalman and H∞ are this same RTL with different gain constants** | 1 |
| `Observer.lean : tvKalman` | time-varying Kalman: covariance on-chip, gains via two `dividerQ` divisions, 5-phase FSM sharing one engine | ~115 per sample |

Design constants (offline Riccati): Kalman `K = [0.4636, 1.3960]`
(`q = 1/32`, `r = 0.01`); H∞ `K = [0.4974, 1.5472]` (`γ = 1.964`,
`γ_min ≈ 1.309`).  Certificates in
`proofs/SparkleProofs/Control/EstimatorDesign.lean`:

* both gains — error-dynamics contraction at `ρ = 0.98`;
* **H∞ only** — the dissipation inequality at `γ = 2`
  (`V(e⁺)−V(e) ≤ 128w² + 400v² − ‖e‖²` for **all** disturbances) and its
  telescoped energy bound `hinf_energy_bound`.  This is the theorem that
  separates the two filters; the RTL difference is just the constants.

Measured (deterministic seeds, `Tests/IP/Control/ObserverTest.lean`):
random noise → KF beats H∞ by 0.6 %; adversarial square-wave gust →
H∞ beats KF by ~9 %.  The certificate, not the 9 %, is the product.

The divider exists because `Signal` has no division operator and the RV32
integer divider can't do fractional Q division (and its 33-step proof is
pinned to 32 bits).  Making the width-generic divider synthesize required an
elaborator fix: `extractNat` now evaluates closed `Nat` arithmetic
(`Nat.succ`/`add`/`sub`/`mul`/`pow`/…) instead of demanding a raw literal —
previously ANY width-generic module died at synthesis with
"Expected Nat literal, got constant: Nat.succ" once instantiated.

On-chip Riccati cross-validation: iterated from `P = 0`, `tvKalman`'s gains
converge to within 49 / 12 LSB of the offline constants.

See also tutorial **Chapter 12** (`docs/tutorial/md/Ch12_ControlPrecision.md`),
which walks PID → Lyapunov → quantization → the measured SMT boundary →
Kalman/H∞ → two drone use cases.

## Running it

```
lake build IP.Control                    # circuits (no Mathlib)
lake exe control-iir-test                # limit-cycle regression
lake exe control-pid-test                # anti-windup + convergence
lake exe control-lqr-test                # Lyapunov V decreasing
cd proofs && lake exe cache get && lake build   # the ℝ proofs (Mathlib)
```

`lake test` runs all three sim suites; the `#synthesizeVerilog` checks run at
`lake build` time.
