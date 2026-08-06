
# Chapter 12 — Control, estimation, and the engineering of precision

Chapters 6 and 7 proved properties of *digital* circuits — counters,
pipelines, protocol FSMs — where the specification is exact and the
question is "does the RTL meet it".  Control hardware is different:
the specification lives in ℝ ("this loop is stable", "this filter
attenuates disturbances"), the implementation lives in `BitVec`, and
the gap between them is *quantization* — a gap that is not a rounding
footnote but the central engineering decision.  Pick too few
fractional bits and a provably-stable design oscillates on the bench.
Pick too many and you burn LUTs, closing timing gets harder, and
nothing improves.

This chapter walks the whole path on real, synthesizable Sparkle
designs from `IP/Control/`: a PID loop, an LQR regulator, IIR
filters at five precisions, and two state estimators (Kalman and
H∞) including one that computes its own gains on-chip with a
multi-cycle divider.  Along the way it answers a practical question
with *measured* data: **which verification tool covers which claim**
— SMT, Monte-Carlo falsification, or Lyapunov induction — and where
each one stops.

Everything below that is stated as a number was measured or proven in
this repository; the chapter cites the file each time.

## 12.1 Two different claims: "bounded" and "converges"

Start with the PID controller (`IP/Control/PID.lean`):

```
e[n]    = r[n] − y[n]
I[n+1]  = clamp_iLim( I[n] + Ki·e[n] )      -- anti-windup
u[n]    = clamp_uLim( Kp·e[n] + I[n+1] + Kd·(e[n] − e[n−1]) )
```

Note where the clamp sits: *inside* the integrator update, not on the
output afterwards.  That placement is classical anti-windup, and it
splits the correctness story into two claims of very different
strength:

1. **Bounded** — `I` never leaves `[−iLim, iLim]` and `u` never
   leaves `[−uLim, uLim]`.  This holds *unconditionally*: for any
   gains, any input, any noise, by a one-line case split on the two
   comparators.  No control theory involved.  Overflow in the
   datapath is therefore structurally impossible, which is why every
   state register in `IP/Control/` is clamped this way.

2. **Converges** — the closed loop actually tracks the setpoint
   instead of oscillating between the rails forever.  This is a real
   theorem about the *dynamics*, it depends on the gains, and no
   amount of clamping gives it to you.

`Tests/IP/Control/PIDTest.lean` checks claim 1 by slamming the loop
with a huge constant error and watching the integrator saturate at
exactly ±16.0.  Claim 2 is what the rest of this chapter is about.

## 12.2 Lyapunov stability, from zero

The tool for claim 2 is a **Lyapunov function**: a scalar "energy"
`V(x) ≥ 0` that every step of the closed loop strictly shrinks:

```
V(x⁺) ≤ ρ·V(x),      ρ < 1
```

If such a `V` exists, the state converges geometrically — not for the
inputs you simulated, but for *all* states, forever.  For linear
systems the standard candidate is a quadratic form `V(x) = xᵀPx`
with `P` positive definite.

Sparkle's LQR demo (`IP/Control/LQRStateFeedback.lean`) makes this
concrete.  The plant is a double integrator sampled at `dt = 1/16`,
the gain `K = [0.618, 1.26]` comes from an offline Riccati solve, and
the certificate is

```
P = [ 2.1180  0.9885 ]        ρ = 39/40 = 0.975
    [ 0.9885  4.0160 ]
```

`proofs/SparkleProofs/Control/LQRDesign.lean` proves, with Mathlib
over ℝ and zero `sorry`:

* `P ≻ 0` (Sylvester's criterion),
* the sandwich `½‖x‖² ≤ V(x) ≤ 5‖x‖²`,
* **`lyapunov_decrease`** : `V(x⁺) ≤ 0.975·V(x)` for every state.

Two practical notes that generalize:

* The certificate is *loose on purpose*.  The true worst-case ratio
  is 0.97179 (measured by sweep, and independently by the Float
  falsification harness in `retypelab/`).  Proving 0.975 instead of
  0.972 costs nothing and makes the `nlinarith` proof robust.
* `P` and `K` are **verified, not derived**.  The Riccati solve
  happened in an offline script; Lean checks the inequality.  This
  guess-and-verify shape is how Lyapunov arguments normally work, and
  the verification is what carries the weight — a wrong guess simply
  fails to prove.

## 12.3 Quantization as a bounded disturbance

The synthesized datapath does not compute over ℝ.  It computes
Q15.16: integers scaled by 2⁻¹⁶, products floored by an arithmetic
shift.  The bridge between the proof and the silicon rests on one
small fact and one standard theorem.

**The small fact.**  In Lean 4, `Int./` floors — and
`BitVec.sshiftRight` also floors.  They are *the same function*.  So
the RTL's `>>> 16` and the spec's `/ 2^16` agree exactly, and one
Q15.16 multiply errs by less than **one LSB, always downward** —
error confined to `(−1, 0]` LSB, independent of sign
(`proofs/SparkleProofs/Control/Transport.lean`, `mulQ_error`).
Contrast the divider below, which truncates toward zero and pays a
two-sided `(−1, 1)` LSB interval for it.

**The standard theorem (ISS).**  A per-step error bounded by ε is a
*bounded disturbance*, and a Lyapunov contraction survives bounded
disturbances in degraded form:

```
V(x⁺) ≤ σ·V(x) + c·ε²,     σ = (1+ρ)/2 < 1
```

Iterating telescopes into an **ultimate bound**: the state enters and
stays in a ball whose radius scales with ε
(`Transport.ultimate_bound` — an unbounded-horizon induction, checked
by the kernel).  Quantization does not threaten stability; it buys a
steady-state error floor.  How big a floor is exactly the precision
question:

```
Vbound(f) = 583200 / 4^f        (f = fractional bits)
```

`proofs/SparkleProofs/Control/Precision.lean` proves this closed form
and its consequences: each extra fractional bit cuts the floor by 4×,
and for a representative budget `V ≤ 0.01`,

* `f = 12` **fails** (`Vbound ≈ 0.035`),
* `f = 13` **passes** (`Vbound ≈ 0.0087`), and monotonically every
  `f ≥ 13` passes  (`min_fracBits_for_budget`).

"How many fractional bits do I need?" is a *theorem* now, not a
guess.

### A measured warning: more bits ≠ better behaviour

`Tests/IP/Control/PrecisionSweepTest.lean` runs one impulse through
the same marginal IIR resonator (ℝ poles at radius 0.999) at five
formats.  Residual ringing after 200 samples, in 1e-3 units:

```
f = 4  → 62        f = 8  → 0        f = 16 → 52        f = 24 → 52
```

Non-monotone.  Two separate mechanisms, and the bound above covers
only one of them:

* **Datapath quantization** (covered): adds the ε-disturbance, floor
  shrinks 4× per bit.
* **Coefficient quantization** (not covered — it perturbs ρ, not ε):
  rounding the coefficients moved the poles *inward* at every format
  (radius 0.968 at f=4, 0.998 at f=8, 0.99899 at f=16 — all stable),
  and at coarse f the **deadband** — products flooring to zero once
  the state is below one LSB — kills the ringing outright, while fine
  f faithfully reproduces the marginal design and keeps ringing for
  hundreds of cycles.

Fine precision gives you a *more faithful copy of whatever you
designed* — including its flaws.  Precision and design margin are
separate budgets; the worksheet in §12.8 keeps them separate.

Also measured in the same sweep: Q7.8 (16-bit) and Q23.8 (32-bit)
produce **bit-identical** output — they share `f = 8`.  Width buys
range (later saturation), never accuracy.  If a review comment says
"widen the datapath for accuracy", this test is the counterexample.

## 12.4 Three verifiers, three coverage zones — measured

You now have three ways to check a fixed-point control claim.  They
are not interchangeable; each has a hard edge, and we measured where.

**(a) SMT / `bv_decide`** (SAT over bit-vectors, in `Std`).  A
*decision procedure*: it proves or hands you a concrete
counterexample assignment.  Measured on this machine, on a two-state
biquad-shaped recurrence (4 multiplies per step, state boxed, asking
for an output bound), timeout 420 s:

| width | steps unrolled | result |
|---|---|---|
| 8, 16, 32 | 1 | proved, **≈0.5 s** (even with a 32×32 multiply) |
| 32 | 8 | proved, 124 s |
| 32 | 16 | proved, 8 s (SAT solvers are non-monotone) |
| 16 | 20 | proved, 187 s |
| 16 | 24 | **timeout** |
| 32 | 24 | **timeout** |

Two lessons.  First, the folklore "SMT dies at 32 bits" is wrong for
single-step goals — a one-step invariant with a full-width multiply
is instant at any width, so *inductive step obligations are ideal SMT
targets*.  Second, the wall is **unrolling depth**, around N≈20–24
here regardless of width.  Bounded-model-checking a trajectory
further than that is hopeless, and an *unbounded* claim ("never
oscillates, ever") is structurally out of reach — BMC can only ever
say "no violation in the first N steps".  This is precisely the gap
DSVerifier-style tools live in.

**(b) Monte-Carlo falsification** (`retypelab/`).  The ℝ design is
transported to executable `Float` by `retype`
(`retype_def VF := V using Real => Float`) and hammered with 10⁵
random states *before* anyone writes a proof.  Measured output, from
the build log:

```
contraction: counterexample = none, worst ratio = 0.971789  (ρ = 0.975)
ISS:         counterexample = none, worst overshoot = 0
negative control (ρ = 0.97 < true 0.97179): 4832 violations found
```

The negative control is the important line: with the rate set just
below the true worst case the search *does* find thousands of
violations, so "found nothing" is evidence, not vacuity.  Cost:
milliseconds per candidate certificate.  What it can never give:
a guarantee.  Its role is to kill wrong constants cheaply — the ρ and
the Young-split δ in `LQRDesign.lean` each went through one wrong
guess that the Float harness would have (and later did) flag
instantly, versus a slow failed `nlinarith` round-trip.

**(c) Lyapunov induction in the kernel** (`proofs/`).  Unbounded
horizon, all states, quantization included — the only tool of the
three that can state "for every n" — at the price of needing a
certificate to verify and `nlinarith` labour to check it.  The
division of labour that emerges, and that this repo actually uses:

```
Float search  →  find/refute the certificate candidate   (milliseconds)
bv_decide     →  discharge one-step BitVec side goals     (seconds)
Lyapunov      →  the unbounded claim itself               (kernel-checked)
```

**(d) …and none of them see the backend.**  A war story from building this
chapter, kept because it is the sharpest possible illustration of coverage
zones.  The width-generic divider below passed *every* Lean-side check —
pure-model-vs-reference on 40 cases, all proofs, `#synthesizeVerilog`
accepted it, iverilog *parsed* the output — and the emitted RTL still
computed `1.0/3.0 = saturate`.  Cause: the Verilog backend's width inference
hit the symbolic width `w + f + 1`, could not reduce `Nat.succ 48` to a
literal, and **silently defaulted to 8 bits**, so a 49-bit divisor register
was fed through an 8-bit wire and latched zero.  Nothing on the Lean side
can catch that class of bug, because the bug is in the translation itself.
What caught it: **simulating the emitted Verilog** against the pure model —
which then agreed bit-for-bit once the backend was fixed (five full
time-varying-Kalman samples, FSM + shared divider + covariance recursion:
`0, 0, 1581, 8167, 22409` from both).  The moral for the toolbox: theorem,
SAT and search all verify the *model*; only simulation of the *artifact*
verifies the compiler that produced it.  Keep one RTL-level cross-sim in the
loop no matter how much you have proven.

## 12.5 Estimators: Kalman and H∞ are the same circuit

Real loops close on *estimated* state — gyro rates are noisy, and
position comes through a filter.  `IP/Control/Observer.lean`
implements the standard predictor-form observer for one drone axis
(angle + rate, `y = angle + noise`):

```
x̂₁⁺ = x̂₁ + dt·x̂₂ + k₁·(y − x̂₁)
x̂₂⁺ = x̂₂ + dt·u  + k₂·(y − x̂₁)
```

Here is the fact that surprises people: the **steady-state Kalman
filter** and the **H∞ filter** are *this same RTL* with different
values in the two gain constants:

```
Kalman:  K = [0.4636, 1.3960]     (Riccati, q = 1/32, r = 0.01)
H∞:      K = [0.4974, 1.5472]     (H∞ Riccati at γ = 1.964; γ_min ≈ 1.309)
```

Every meaningful difference lives offline — in how the gains were
designed and in **what can be proven about them**
(`proofs/SparkleProofs/Control/EstimatorDesign.lean`):

* Both gains: the error dynamics contract a quadratic `V` at
  ρ = 0.98 (`kf_contraction`, `hinf_contraction`).  Convergence under
  zero disturbance — shared, and not the interesting part.
* **Only the H∞ gain**: the dissipation inequality

  ```
  V(e⁺) − V(e) ≤ γ²·(w²/q + v²/r) − ‖e‖²        γ = 2, for ALL w, v
  ```

  which telescopes (`hinf_energy_bound`) into: *over any horizon, the
  estimation-error energy is at most γ² times the weighted
  disturbance energy, plus the initial storage.*  No Gaussian
  assumption, no smallness assumption — `w` may be a worst-case gust,
  a sensor glitch, an adversary.  Kalman's optimality claim is an
  *average* under the noise model you assumed; this is a *bound*
  under no model at all.

### The on-chip Riccati (`tvKalman`)

The full time-varying Kalman filter propagates its covariance in
hardware and *divides* each sample to get the gain — the operation
`Signal` has no operator for.  This is what the width-generic
restoring divider `IP/Control/DividerQ.lean` exists for (the RV32
integer divider can't do fractional Q15.16 division; its proof is
pinned to 32 bits, so the generic core is a new module in the same
loop shape).  Gain step, 50 cycles per division at Q15.16:

```
s  = p₁₁ + r          -- r > 0 and p₁₁ clamped ≥ 0  ⇒  never divides by zero
k₁ = (p₁₁ + dt·p₁₂)/s
k₂ = p₁₂/s
```

A 5-phase FSM (IDLE → DIV1 → START2 → DIV2 → UPDATE) shares one
divider engine between the two divisions.  Measured cross-validation
(`Tests/IP/Control/ObserverTest.lean`): iterated from `P = 0`, the
on-chip fixed-point Riccati converges to gains within **49 and 12
LSB** of the offline design constants — the hardware recursion and
the offline script confirming each other to ~0.1%.

## 12.6 Use case A: the fast drone

A racing-drone rate loop closes at 1–8 kHz on a controller running at
27 MHz.  Sample-period budget at 4 kHz: 6750 cycles.  What the
numbers in this chapter say about that design:

* **Latency**: the fixed-gain observer and the PID/LQR update are
  single-cycle datapaths — measurement to actuator in one clock,
  0.015% of the budget.  The tvKalman FSM needs ~115 cycles (two
  50-cycle divisions): 1.7% of the budget.  *Both fit trivially* —
  run the fixed-gain observer in the fast loop and, if you want
  adaptive gains, let tvKalman update them at a slower rate.
* **Precision**: the inner loop's signals are small (rate errors,
  ±10 rad/s) and the budget is tight.  `Vbound(f) = 583200/4^f` says
  f = 13 meets a 0.01 budget; Q15.16 gives 30× margin, and §12.3's
  sweep says the *16-bit* Q7.8 datapath — half the multiplier area —
  fails the same budget by three orders of magnitude.  The correct
  cheap choice is a 16-bit *container* only if you can spend 13+ bits
  on fraction, i.e. Q2.13 for a ±4 signal range: the theorem, not the
  bit-width folklore, decides.
* **Verification split**: the per-step overflow-freedom obligations
  are 1-step `bv_decide` goals (instant at 32 bits); the "never
  diverges under quantization" claim is the transported Lyapunov
  bound; and every gain retune gets the millisecond Float-falsifier
  pass before anyone re-proves anything.

## 12.7 Use case B: the disturbance-heavy environment

Now the other regime: an inspection drone next to a building in gusty
wind, a vehicle with unmodelled vibration — the disturbance is large,
structured, and *not* the white Gaussian noise the Kalman design
assumed.  Measured head-to-head (deterministic seeds,
`ObserverTest.lean`), error energy over the run:

| profile | Kalman | H∞ | winner |
|---|---|---|---|
| A: LCG noise (the KF's design case) | 1 081 071 | 1 087 559 | KF by 0.6 % |
| B: square-wave gust, half-period 10 (worst of a swept range) | 1 282 428 | 1 175 037 | **H∞ by 9 %** |

Read this honestly, because the honest reading *is* the lesson:

* On its home turf the Kalman filter wins, by less than a percent.
  H∞'s insurance premium is small.
* Under the adversarial gust H∞ wins by single-digit percent.  If 9%
  were the whole story, you might not bother.
* The story is the **certificate**: `hinf_energy_bound` holds for
  *every* disturbance sequence — including the ones the bench never
  produced.  The Kalman gain has no such theorem at this γ.  When the
  disturbance model is the thing you don't trust, the filter with the
  worst-case guarantee is the engineering choice, and the guarantee —
  not the 9% — is the product.

This is also where the three-verifier split from §12.4 pays off: the
dissipation inequality is a 4-variable quadratic form — far beyond
BMC's unrolling wall as a trajectory claim, but as a one-shot
algebraic inequality it is exactly what an SOS certificate plus
`nlinarith` handles, and the exact rational LDLᵀ that seeds those
hints was found in milliseconds offline.

## 12.8 The precision-selection worksheet

The procedure this chapter justifies, step by step, for a new control
datapath:

1. **Design in ℝ** (any tool).  Extract gains and a Lyapunov /
   dissipation certificate candidate.
2. **Falsify first** (`retypelab/` pattern): retype the model to
   Float, sweep 10⁵ states against the candidate, include a negative
   control.  Fix constants until the search goes quiet.
3. **Prove the ℝ certificate** (`proofs/` pattern): `nlinarith` with
   LDLᵀ-derived square hints; keep ρ deliberately loose.
4. **Pick f from the budget**: `Vbound(f) = c/4^f`, take the minimal
   `f` under budget (here: theorem `min_fracBits_for_budget`), then
   one bit of margin.  Pick `w` from *range* (saturation headroom),
   never from accuracy.
5. **Sweep the formats in simulation**
   (`PrecisionSweepTest` pattern): confirm the residuals, and check
   the *coefficient*-quantization effect separately — it moves poles,
   and the bound from step 4 does not see it.
6. **Discharge step obligations with `bv_decide`** where they are
   1-step; never ask it for an unbounded claim.
7. **Synthesize every format you compared** — a comparison in which
   only one column is real hardware is a spreadsheet, not a sweep.

Every step exists as working code in this repository; the chapter's
role was only to put them in order.

```lean
import IP.Control.IIRBiquadGen

open Sparkle.IP.Control.IIRBiquadGen
open Sparkle.IP.Control.FixedPointGen

-- The §12.3 sweep, live: the same marginal resonator at three formats.
-- Residual ringing amplitude (×1e-3) after 200 quiet samples:
def tail (w f : Nat) : Nat :=
  let impulse := (q w f 1 1) :: List.replicate 300 (BitVec.zero w)
  let ys := run w f (quantize w f marginalCoeffs) (limOf w f)
    ⟨BitVec.zero w, BitVec.zero w⟩ impulse
  (((ys.drop 200).map (fun y => (y.toInt * 1000 / (2 ^ f : Int)).natAbs))).foldl
    Nat.max 0

#eval tail 16 8    -- 0   : coarse f — the deadband killed the ringing
#eval tail 32 16   -- 52  : fine f — faithfully still ringing
#eval tail 32 8    -- 0   : same f as Q7.8, twice the width — identical
```

## 12.9 Where this stops, honestly

* The `Signal`-level equality (`circuit do` = the pure `step`
  functions, every cycle) is checked by cycle-accurate co-simulation,
  not yet by the `loop_iterate` proof — that bridge exists in the
  repo (`Sparkle/Verification/Divider/` proved it for the RV32
  divider) and is the natural next proof.
* All certificates are verified, not synthesized: the Riccati and
  LDLᵀ computations run in offline scripts, Lean checks the
  inequalities.  A DARE solver *inside* Lean would close that gap.
* The H∞ dissipation is proven for the ℝ model; its fixed-point
  transport (the estimator analogue of `Transport.lean`) follows the
  same ISS pattern but is not written.
* `retype` pins a newer toolchain than Sparkle, so the Float
  falsifier lives in its own package with a duplicated (and
  `#guard`-drift-checked) model — an accepted seam until the
  toolchains align.
