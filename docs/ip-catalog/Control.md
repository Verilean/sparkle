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
