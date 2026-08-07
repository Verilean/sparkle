
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

The chapter has **one argument**, and every section is a step in it:

> Write the system down once, in ℝ.  Prove it stable there.  Then carry
> that ℝ text down to hardware mechanically, and account for exactly what
> the trip costs.

Three layers, and the interesting work is at the joints between them:

1. **ℝ is the reference.**  `V(f(x)) ≤ ρ·V(x)`, kernel-checked, no `sorry`
   (§12.1, §12.3).
2. **The fixed-point equation is *derived*, not re-typed.**  `retype`
   transports the ℝ definition to Q15.16 fixed point (the format is
   introduced from scratch in §12.1.2), and that transported equation is
   checked to be the one the RTL datapath actually computes (§12.2).  This
   is the joint people skip, and it is where a proved model quietly stops
   describing the shipped circuit.
3. **The circuit's own stability.**  Quantization is not a rounding
   footnote — flooring is a nonlinearity that can sustain a limit cycle —
   so the ℝ theorem is re-earned as an ISS ultimate bound, and the residual
   gap is stated plainly (§12.4, §12.10).

The vehicles are real synthesizable designs from `IP/Control/`: a PID loop,
an LQR regulator, IIR filters at five precisions, and two state estimators
(Kalman and H∞), one of which computes its own gains on-chip with a
multi-cycle divider.  Along the way the chapter answers a practical
question with *measured* data — **which verification tool covers which
claim** (SMT, Monte-Carlo falsification, Lyapunov induction), and where
each one stops (§12.5).

Everything below that is stated as a number was measured or proven in
this repository; the chapter cites the file each time.  Where a link in
the chain is checked-on-cases rather than proved, it says so.

## 12.1 The worked example: one PID loop, from equations to theorem

Everything in this chapter is demonstrated on one concrete system, small
enough to hold in your head and real enough to synthesize.  This section
walks it end to end: the equations, the RTL that implements them, and the
theorem that certifies them — each line of one mapped to the others.

### 12.1.1 The equations

A first-order plant (think: the rate response of one drone axis — command a
torque, the rate follows with a lag), sampled at `dt = 1/16 s`:

```
x[n+1] = 0.9·x[n] + 0.1·u[n]
```

and the textbook discrete PID regulating it to a setpoint r:

```
e[n]   = r − x[n]                          error
I[n+1] = I[n] + Ki·e[n]                    integrator      Ki = 0.25
u[n]   = Kp·e[n] + I[n+1] + Kd·(e[n]−p[n]) control         Kp = 2, Kd = 0.125
p[n+1] = e[n]                              previous error
```

Two state registers in the controller (`I`, `p`), one in the plant (`x`).

### 12.1.2 The RTL, line for line

**Fixed point, and the Q notation, in one paragraph.**  Hardware has no
real numbers, and floating point costs far more than a control loop can
usually justify.  So a fractional value is stored as a plain integer with
an *implied* scale factor: the 32-bit integer `n` represents the value
`n / 2¹⁶`.  Nothing in the hardware marks where the point is — the
convention lives in your head and in the code that reads the register.

`Q15.16` names that convention: **16 fractional bits**, **15 integer
bits**, plus one sign bit — 32 in total.  So the representable range is
about ±32768 (2¹⁵) and the resolution is 2⁻¹⁶ ≈ 0.0000153.  That
resolution — the value of one integer step — is the **LSB** (least
significant bit), the unit every error bound in this chapter is quoted in.
Two consequences follow immediately, and both drive the rest of the
chapter:

* **Adding** two Q15.16 values is just integer addition — the scales
  already match.
* **Multiplying** them is not.  `(a/2¹⁶)·(b/2¹⁶) = a·b/2³²`, so the
  integer product carries *twice* the intended scale and must be shifted
  back down by 16 to return to Q15.16.  That shift discards the low 16
  bits, and discarding them is where quantization error enters (§12.4).

So `mulQSig` below is a 32×32→64 multiply followed by an arithmetic shift
right by 16 — widen to avoid overflowing the product, then rescale.

`IP/Control/PID.lean` implements exactly the four lines above in Q15.16:

```
def pid (iLim uLim : BitVec 32)
    (r y kp ki kd : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  circuit do
    let integReg ← Signal.reg (0#32)                    -- I
    let ePrevReg ← Signal.reg (0#32)                    -- p

    let e := r - y                                      -- e[n]   = r − x[n]
    let integNext := clampSymC iLim                     -- I[n+1] = I[n] + Ki·e[n]
      (integ + mulQSig ki e)                            --          (clamped: anti-windup)
    let d := e - ePrev                                  -- e[n] − p[n]
    let u := clampSymC uLim                             -- u[n]   = Kp·e + I⁺ + Kd·d
      (mulQSig kp e + integNext + mulQSig kd d)         --          (clamped: actuator limit)

    integReg <~ integNext                               -- register writes
    ePrevReg <~ e                                       -- p[n+1] = e[n]
    return u
```

The correspondence is one-to-one — that is the point of writing hardware in
the same language as the specification.  Note the two `clampSymC`s: they are
*not* in the textbook equations.  They are the implementation's two safety
nonlinearities, and they carry the first of two very different claims:

1. **Bounded, unconditionally.**  `|I| ≤ iLim` and `|u| ≤ uLim` for ANY
   gains, ANY input, ANY noise — because the clamp is inside the update, the
   claim is a one-line case split on two comparators, no control theory
   involved.  `Tests/IP/Control/PIDTest.lean` slams the loop with a huge
   constant error and watches the integrator saturate at exactly ±16.0:

   ```
   ✓ integrator stays within ±16.0 under a huge sustained error
   ✓ integrator actually saturates (the clamp is exercised)
   ```

   This is why the datapath can never overflow — and it is also why claim 1
   is NOT stability: a badly tuned loop happily bangs between the rails
   forever while satisfying every bound.

2. **Converges** — the actual control claim.  That needs a theorem about the
   dynamics, which is §12.1.3.

### 12.1.3 The theorem

Close the loop symbolically (set r = 0; substitute u into the plant) and the
three states evolve linearly:

```
x[n+1] = 0.6625·x + 0.1·I − 0.0125·p      (0.6625 = 0.9 − 0.1·(Kp+Ki+Kd))
I[n+1] = −0.25·x  + I
p[n+1] = −x
```

Eigenvalues: 0.8717, 0.8085, −0.0177 — all inside the unit circle, so the
loop is stable.  But "I computed eigenvalues" is a *numerical remark*, not a
proof.  The machine-checked version
(`proofs/SparkleProofs/Control/PIDDesign.lean`) exhibits a quadratic
certificate instead:

```
P = ⎡ 8.0999  −5.4050  −0.0850 ⎤        V(s) = sᵀPs
    ⎢−5.4050   9.7880   0.0574 ⎥
    ⎣−0.0850   0.0574   1.0013 ⎦
```

and proves, over ℝ with Mathlib, zero `sorry`:

```
theorem pid_lyapunov_decrease (x I p : ℝ) :
    V (nextX x I p) (nextI x I p) (nextP x I p) ≤ (39/40) * V x I p := by
  unfold V nextX nextI nextP p11 p12 p13 p22 p23 p33 Kp Ki Kd pa pb
  nlinarith [sq_nonneg (x + (1694/10000)*I + (27/10000)*p),
             sq_nonneg (I − (25/10000)*p), sq_nonneg p, …]
```

Every sample, the energy `V` shrinks by at least the factor 39/40 — for
*every* state, not the trajectories you happened to simulate.  Together with
`P ≻ 0` (Sylvester, also proven) and the sandwich
`0.999·‖s‖² ≤ V(s) ≤ 15·‖s‖²`, the corollary `pid_geometric_decay` gives
geometric convergence of the state itself, by a five-line induction.

Where did `P` and those strange `nlinarith` hints come from?  Offline — and
this recipe is used for every quadratic-form proof in the repo, so learn it
once:

1. iterate the discrete Lyapunov equation `P ← AᵀPA + I` numerically to a
   fixed point; round to 4 decimals;
2. sweep for the true worst ratio `V(As)/V(s)` (here 0.9306) and pick a
   *round* certified rate above it (39/40 = 0.975 — slack is robustness);
3. compute `ρP − AᵀPA` over exact rationals and take its exact LDLᵀ; if all
   pivots are positive (here 0.798 / 0.732 / 0.975) the matrix is PSD and
   the LDLᵀ rows are literally a sum-of-squares witness;
4. hand those rows to `nlinarith` as `sq_nonneg` hints.  The proof lands on
   the first try, because you are not asking the tactic to *find* the
   certificate — only to *check* it.

Guess-and-verify is the honest shape of every Lyapunov argument; the kernel
checking step 4 is what turns the numerical remark into a theorem.

### 12.1.4 What just happened, and what did not

The theorem is about the ℝ model.  The RTL runs Q15.16.  **That gap is the
subject of the rest of the chapter**, and it has two distinct halves that
are easy to conflate:

* *Is the RTL computing the same equation?*  A question about
  **transport** — answered by deriving the fixed-point equation from the ℝ
  one instead of hand-writing it, then checking the datapath against the
  derivation (§12.2).
* *Does the equation still converge once every product is floored?*  A
  question about **dynamics** — answered by ISS: the quantization error of
  each multiply is one-sided and < 1 LSB (`mulQ_error`), and a Lyapunov
  contraction absorbs bounded per-step disturbances into a computable
  ultimate bound (§12.4).  Plus the circuit held to the pure model
  cycle-by-cycle on three backends (§12.5d).

Answering only the second — the usual practice — leaves you with a proof
about an equation you have not established the hardware implements.

What is *deliberately not* claimed: that the clamps never engage (they
exist precisely for the transients where they do), and that the certificate
covers the saturated regions — extending `V` piecewise across the clamp
boundaries is the natural next theorem, and is open.

## 12.2 The spine: one equation, three layers

Everything from here to §12.10 is one argument, and it is worth stating
before the details bury it.  There is **one** system.  It is written down
once, in ℝ, and that ℝ text is the reference — the thing the design *means*.
Everything else in the chapter is an attempt to carry that meaning down to
something you can put on an FPGA, and to be honest about what survives the
trip.

The system is the one you already have in your head: the PID closed loop of
§12.1.1.  Written out over ℝ, its three states evolve by the three functions
§12.1.3 proved a certificate for —

```
nextX x I p  =  0.6625·x + 0.1·I − 0.0125·p      -- plant
nextI x I p  =  −0.25·x + I                      -- integrator
nextP x I p  =  −x                               -- previous error
```

— and those three names are what the rest of this section transports.

Three layers, three different kinds of claim:

| Layer | Artifact | What is claimed | How |
|---|---|---|---|
| 1. Design | `nextX, nextI, nextP : ℝ → ℝ` | `V(f(s)) ≤ ρ·V(s)`, ρ = 39/40 | Lean proof, kernel-checked |
| 2. Implementation | `nextXQ, nextIQ, nextPQ : FixQ → FixQ` | the Q15.16 equations **are** the ℝ equations, retyped | mechanical transport, then equality vs the RTL |
| 3. Circuit | `IP/Control/PID.lean` (Verilog) | ℝ stability + bounded error ⟹ ultimate bound | ISS, plus co-sim |

Layer 1 is §12.1.3 — already done, same three functions.  Layer 3 is §12.4.
This section is
**layer 2**, which is the one that is easy to skip and is exactly where
designs go wrong: the ℝ model is proved, the RTL is simulated, and nobody
ever checks that the RTL implements *that* model rather than a slightly
different one someone typed in by hand.

### 12.2.1 Transporting the equation, not re-typing it

The usual practice is to write the fixed-point version by hand.  That
creates a second source of truth, and the two drift: a gain rounded
differently, a `-` that became a saturating `-` on one side only.  No
amount of simulating the RTL finds this, because the RTL is being compared
against *itself*.

Instead, generate it.  `retype` replaces a type throughout a definition and
substitutes the corresponding operations, so the fixed-point equation is
*derived from* the ℝ equation rather than written beside it:

```lean
structure FixQ where            -- Q15.16: the stored integer is value·2¹⁶
  n : Int

instance : Add FixQ := ⟨fun a b => ⟨a.n + b.n⟩⟩
instance : Mul FixQ := ⟨fun a b => ⟨(a.n * b.n) / 65536⟩⟩   -- floors; see §12.2.2

declare_retype RealToFixQ : Real => FixQ

-- the gains and plant of §12.1.1, unchanged
noncomputable def Kp : ℝ := 2 ; noncomputable def Ki : ℝ := 1 / 4
noncomputable def Kd : ℝ := 1 / 8
noncomputable def pa : ℝ := 9 / 10 ; noncomputable def pb : ℝ := 1 / 10

noncomputable def nextX (x I p : ℝ) : ℝ :=
  (pa - pb * (Kp + Ki + Kd)) * x + pb * I - pb * Kd * p

retype_def KpQ := Kp using Real => FixQ    -- …and Ki, Kd, pa, pb
attribute [retype RealToFixQ] Kp Ki Kd pa pb   -- so nextX's references follow
retype_def nextXQ := nextX using Real => FixQ
```

`nextXQ` is now a Q15.16 function nobody wrote.  Evaluating it:

```lean
#eval KpQ                     -- { n := 131072 }  = 2        ✓
#eval KiQ                     -- { n := 16384 }   = 0.25     ✓
#eval paQ                     -- { n := 58982 }   ≈ 0.89999  ✓
#eval nextXQ ⟨65536⟩ ⟨0⟩ ⟨0⟩   -- { n := 43419 }   = 0.66250  ✓
```

The last line is the check worth pausing on.  Set `x = 1, I = 0, p = 0`: the
ℝ equation collapses to its leading coefficient, which §12.1.3 displays as
**0.6625** — and 43419/65536 = 0.66250.  The transported equation reproduces
the number the ℝ proof is about, and no human transcribed a coefficient.

The `attribute` line is the one non-obvious step.  Without it, `nextX`'s
references to `Kp`/`pa` stay at type ℝ and the elaborator reports
`pa has type ℝ but is expected to have type FixQ`; the attribute is what
makes a definition's *dependencies* follow the transport too.

### 12.2.2 Does the RTL implement *this*?

Now the question that layer 2 exists to answer.  Sparkle's datapath uses
`mulQ` on `BitVec 32` (`IP/Control/FixedPoint.lean`):

```lean
def mulQ (a b : BitVec 32) : BitVec 32 :=
  BitVec.extractLsb' 16 32 ((a.signExtend 64) * (b.signExtend 64))
```

and the retyped model uses `(a.n * b.n) / 65536` on `Int`.  These are the
same function, and the reason is not obvious: `extractLsb' 16` on a
sign-extended product is an **arithmetic** right shift, which rounds toward
−∞, and Lean's `Int./` also **floors**.  Had the hardware used a truncating
shifter, or had `FixQ` used `Int.tdiv`, the two would agree on positives and
disagree on every negative product.

That is a claim, so it is checked rather than asserted:

```lean
def refMul (a b : Int) : Int := (a * b) / 65536
def chk (a b : Int) : Bool :=
  (mulQ (BitVec.ofInt 32 a) (BitVec.ofInt 32 b)).toInt == refMul a b

#eval cases.filter (fun (a,b) => !chk a b)     -- []
```

over sign-crossing and boundary cases (`(-1, 65535)`, `(3, -65537)`,
`(-58982, -65536)`, …) — all agree.

Both halves are live code, not listings:
`proofs/SparkleProofs/Retype/FixedPointTransport.lean` does the transport and pins
every constant with `#guard` (131072, 16384, 8192, 58982, and the step
result 43419 — each checkable by hand against §12.1.1), and
`Tests/IP/Control/PrecisionSweepTest.lean`'s *Transport agreement* suite
runs the comparison on the Sparkle side under `lake test`:

```
Transport agreement (ℝ →retype→ Q15.16 vs Sparkle mulQ):
  ✓ every case agrees
  ✓ negative product with remainder floors down (not toward zero)
  ✓ positive product with remainder floors to zero
  ✓ pa = 0.9 transports to 58982
  ✓ one observer step matches the transported equation
```

So the datapath's multiply is the retyped multiply, and the chain

> ℝ equation → (retype) → Q15.16 equation → (this check) → RTL datapath

closes.  §12.5d then holds the *whole circuit* to the pure model
cycle-by-cycle on three backends, which extends the agreement from one
operation to one design.

### 12.2.3 What layer 2 does and does not buy

It buys the elimination of a specific, common, silent failure: the
implemented equation not being the designed equation.  After this section,
"the RTL computes something slightly different from the model" is not on
the table.

It also does not mean the transported equation equals the ℝ answer.  Worth
seeing concretely: `nextXQ ⟨65536⟩ ⟨0⟩ ⟨0⟩` gives **43419**, while quantizing
the already-simplified constant 0.6625 in one go gives **43417**.  Neither is
wrong.  The transport evaluates the *expression* `(pa − pb·(Kp+Ki+Kd))·x` in
Q15.16, flooring at each product; the other rounds the ℝ answer once.  Two
LSB apart — and that gap is precisely the per-step quantization error that
§12.4 has to bound rather than wish away.  (Both numbers are pinned in
`Tests/IP/Control/PrecisionSweepTest.lean`, so neither can drift silently.)

It does **not** make the fixed-point loop stable.  `nextXQ` is a different
dynamical system from `nextX` — it floors every product — and a floor is
not a small perturbation of the identity, it is a nonlinearity that can
sustain a limit cycle (§12.4 shows one doing exactly that, and §12.4's
"more bits ≠ better" warning shows a *finer* grid behaving *worse*).
Layer 2 says the two systems are related by transport; layer 3 has to say
what that relation preserves.

One honest gap in this layer, recorded rather than papered over: the `mulQ`
agreement of §12.2.2 is **checked on cases, not proved**.  The lemma to prove
is

```
(mulQ a b).toInt = (a.toInt * b.toInt) / 2¹⁶     -- when the result fits
```

and both halves of that sentence matter.  The no-overflow hypothesis is not
decoration: at 8/4 (the same shape, small enough to enumerate) the identity is
**false** without it — `a = 17, b = 121` gives `17·121/16 = 128`, one past the
signed 8-bit maximum, and `extractLsb'` wraps it to −128.  Restricted to
results that fit, all 65536 pairs at 8/4 agree.

What does *not* work is the obvious tactic.  `bv_decide` rejects the goal
outright — "none of the hypotheses are in the supported BitVec fragment" —
because `toInt` and `Int./` leave the bitvector fragment it decides.  Proving
this needs the `BitVec.toInt`/`extractLsb'` lemmas and an explicit bound
argument, not a decision procedure, and that is why it is still unwritten.

The *other* gap this section used to carry is now closed.  The transport
lives in `proofs/SparkleProofs/Retype/`, alongside the theorems, and it
**imports** `nextX`/`nextI`/`nextP` from `PIDDesign.lean` — the very terms
`pid_lyapunov_decrease` is proved about.  Earlier it had to restate them
(retype pinned a newer Lean than Sparkle, and a Lake graph has one
toolchain), so "the transported equation is the certified equation" was
underwritten by `#guard`s comparing two copies.  It now holds because there
is only one copy.

## 12.3 Lyapunov stability in general

What §12.1.3 did for one system is the general recipe.  A **Lyapunov
function** for `s⁺ = f(s)` is any `V ≥ 0` with

```
V(f(s)) ≤ ρ·V(s),      ρ < 1     (for all s)
```

— existence of such a `V` *is* geometric stability, and for linear systems a
quadratic `V(s) = sᵀPs` always works when the system is stable (solve the
discrete Lyapunov equation, as above).  Two more instances live in this
repo, proved with the same LDLᵀ recipe:

* the **LQR** double integrator (`LQRDesign.lean`) — the chapter's vehicle
  for the quantization story, ρ = 39/40, true ratio 0.97179;
* both **estimator error dynamics** (`EstimatorDesign.lean`, §12.6) — where
  the *same* recipe also proves the H∞ dissipation inequality, a 4-variable
  quadratic form.

Why insist on the contraction form `V∘f ≤ ρV` rather than mere decrease
`V∘f < V`?  Because only the former survives disturbances: ρ < 1 leaves
room to absorb a bounded perturbation into a geometric series (§12.4's ISS
argument), whereas strict-decrease-by-an-unquantified-amount absorbs
nothing.  Certificates should always be stated with slack.

## 12.4 Quantization as a bounded disturbance

The synthesized datapath does not compute over ℝ.  It computes Q15.16
(§12.1.2), and the shift that rescales every product throws the low 16
bits away.  Layer 2 established that the RTL computes the *right*
equation; this section is the other half — what flooring every product
does to the ℝ theorem.  The bridge rests on one small fact and one
standard theorem.

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
separate budgets; the worksheet in §12.9 keeps them separate.

Also measured in the same sweep: Q7.8 (16-bit) and Q23.8 (32-bit)
produce **bit-identical** output — they share `f = 8`.  Width buys
range (later saturation), never accuracy.  If a review comment says
"widen the datapath for accuracy", this test is the counterexample.

## 12.5 Three verifiers, three coverage zones — measured

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

**(b) Monte-Carlo falsification** (`proofs/SparkleProofs/Retype/`).  The ℝ design is
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
`0, 0, 1581, 8167, 22409` from both).  A second lesson from the same week, one
layer up: the interpreted `Signal.val` co-sim of a multi-register `circuit do`
FSM *hangs* (issue #95 — the Circuit monad composes per-write state-update
closures, so evaluation cost grows ~k^k in the register count).  An attempted
fix made simulation linear, but it changed expression sharing enough to alter
the generated RTL of nested engines behind multi-output records — caught only
by re-running the emitted RTL against a known-good Keccak digest, and
therefore not merged.  The estimators here are co-simulated through the CSim
JIT (`lake exe control-jit-test`) and iverilog instead.

The moral for the toolbox: theorem, SAT and search all verify the *model*;
only executing the *artifact* — the emitted RTL, the compiled simulator —
verifies the compiler that produced it.  Keep one artifact-level cross-sim per
backend in the loop no matter how much you have proven, and treat a green
`#synthesizeVerilog` as "well-formed", never as "correct".

## 12.6 Estimators: Kalman and H∞ are the same circuit

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

## 12.7 Use case A: the fast drone

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
  f = 13 meets a 0.01 budget; Q15.16 gives 30× margin, and §12.4's
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

## 12.8 Use case B: the disturbance-heavy environment

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

This is also where the three-verifier split from §12.5 pays off: the
dissipation inequality is a 4-variable quadratic form — far beyond
BMC's unrolling wall as a trajectory claim, but as a one-shot
algebraic inequality it is exactly what an SOS certificate plus
`nlinarith` handles, and the exact rational LDLᵀ that seeds those
hints was found in milliseconds offline.

## 12.9 The precision-selection worksheet

The procedure this chapter justifies, step by step, for a new control
datapath:

1. **Design in ℝ** (any tool).  Extract gains and a Lyapunov /
   dissipation certificate candidate.
2. **Falsify first** (`SparkleProofs.Retype` pattern): retype the model to
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

-- The §12.4 sweep, live: the same marginal resonator at three formats.
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

## 12.10 Where this stops, honestly

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
* ~~`retype` pins a newer toolchain than Sparkle~~ — **closed.**  Every
  package is on Lean v4.32.1, the `retypelab/` sidecar is folded into
  `proofs/SparkleProofs/Retype/`, and both the Float falsifier and the
  Q15.16 transport now *import* their ℝ models from `LQRDesign.lean` /
  `PIDDesign.lean` instead of restating them.  So §12.2's claim — the
  transported equation is the equation the certificate is about — holds
  by construction rather than by a drift check.
