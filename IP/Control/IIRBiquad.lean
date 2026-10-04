/-
  Fixed-point IIR biquad — Direct Form II transposed, Q15.16, saturating state.

  ## The circuit

  Direct Form II transposed, which is the standard choice for fixed-point because
  each state register accumulates only one product pair:

      y[n]  = b0*x[n] + s1[n]
      s1[n+1] = b1*x[n] - a1*y[n] + s2[n]
      s2[n+1] = b2*x[n] - a2*y[n]

  Every state register is passed through `clampSym stateLim` before being stored.
  That is what makes this thing analysable: the reachable state set is
  *structurally* contained in `[-stateLim, stateLim]^2`, so overflow-freedom
  needs no stability argument at all, and the Lyapunov argument is then only
  responsible for the interesting claim (that the state actually contracts into
  a small ball around the origin, rather than sitting at the clamp rails or
  limit-cycling).

  ## Two instances, deliberately contrasting

  `stableLPF`   — a well-conditioned 2nd-order low-pass.  Provably contracts.
  `naiveLPF`    — a resonator whose ℝ poles sit at radius 0.999 (stable), but
                  whose coefficients, rounded to a coarse grid, land exactly on
                  radius 1.  Sustains a period-6 limit cycle from a single
                  impulse.  See its docstring for the measured sequence.

  Both synthesize.  The point of shipping both is that "we proved the good one
  stable" is only interesting if the bad one is genuinely reachable by an
  ordinary engineer doing the obvious thing — see
  `Tests/IP/Control/IIRBiquadTest.lean`, which exhibits the sustained
  oscillation of `naiveLPF` from a zero input, and
  `proofs/SparkleProofs/Control/BiquadStability.lean`, which proves the
  contraction for `stableLPF`.
-/

import Sparkle
import Sparkle.Compiler.Elab
import IP.Control.FixedPoint

set_option maxRecDepth 100000

namespace Sparkle.IP.Control.IIRBiquad

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Control.FixedPoint

variable {dom : DomainConfig}

/-- Biquad coefficients in Q15.16.  `a1`/`a2` are the *feedback* coefficients
    with the sign convention of the recurrence above (i.e. the denominator is
    `1 + a1 z⁻¹ + a2 z⁻²`). -/
structure Coeffs where
  b0 : BitVec 32
  b1 : BitVec 32
  b2 : BitVec 32
  a1 : BitVec 32
  a2 : BitVec 32
  deriving Repr, DecidableEq

/-! ### Pure reference semantics

The proofs reason about `step`; `biquad` below is the circuit.  `Proof/` shows
they agree at every cycle. -/

/-- Biquad state: the two delay registers of the transposed form. -/
structure State where
  s1 : BitVec 32
  s2 : BitVec 32
  deriving Repr, DecidableEq, Inhabited

/-- One cycle of the biquad, with saturating output and saturating state.
    `lim` clamps both state registers; `outLim` clamps the output. -/
def step (c : Coeffs) (lim : BitVec 32) (st : State) (x : BitVec 32)
    : State × BitVec 32 :=
  let y := clampSym lim (satAdd (mulQ c.b0 x) st.s1)
  let s1' := clampSym lim
    (satAdd (satAdd (mulQ c.b1 x) (-(mulQ c.a1 y))) st.s2)
  let s2' := clampSym lim (satAdd (mulQ c.b2 x) (-(mulQ c.a2 y)))
  (⟨s1', s2'⟩, y)

/-- Run the biquad on a list of samples, collecting the outputs.
    Used by the simulation tests and as the reference the circuit is compared to. -/
def run (c : Coeffs) (lim : BitVec 32) : State → List (BitVec 32) → List (BitVec 32)
  | _, [] => []
  | st, x :: xs =>
    let (st', y) := step c lim st x
    y :: run c lim st' xs

/-! ### The circuit -/

/-- Synthesizable Direct-Form-II-transposed biquad.

    Coefficients are `Signal` inputs (so one instance serves any filter); `lim`
    is a compile-time constant so the clamp lowers to a compare-against-literal
    and the ultimate-bound theorem is a closed statement. -/
def biquad (lim : BitVec 32)
    (x b0 b1 b2 a1 a2 : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  circuit do
    let s1Reg ← Signal.reg (0#32)
    let s2Reg ← Signal.reg (0#32)

    let s1 := (s1Reg : Signal dom (BitVec 32))
    let s2 := (s2Reg : Signal dom (BitVec 32))

    let y := clampSymC lim (mulQSig b0 x + s1)

    let a1y := mulQSig a1 y
    let a2y := mulQSig a2 y
    let zero := (Signal.pure 0#32 : Signal dom (BitVec 32))

    let s1Next := clampSymC lim (mulQSig b1 x + (zero - a1y) + s2)
    let s2Next := clampSymC lim (mulQSig b2 x + (zero - a2y))

    s1Reg <~ s1Next
    s2Reg <~ s2Next

    return y

/-! ### Concrete filters

Both are 2nd-order low-pass designs for the *same* ℝ specification; they differ
only in how the coefficients were quantized.  `proofs/` derives both from a
single ℝ-level design so the comparison is honest. -/

/-- Q15.16 helper: the Q15.16 word nearest `n / d`. -/
def q (n d : Int) : BitVec 32 := BitVec.ofInt 32 (n * (2 ^ 16) / d)

/-- **Stable**: poles well inside the unit disc.

    Butterworth-ish 2nd order, fc/fs ≈ 0.1:
      b = [0.0640, 0.1279, 0.0640],  a = [-1.1683, 0.4241]
    Poles at 0.584 ± 0.291j, |p| ≈ 0.651 — comfortable margin, and the margin
    survives Q15.16 quantization of the coefficients (that is exactly what
    `BiquadStability.lean` proves). -/
def stableLPF : Coeffs where
  b0 := q 640 10000
  b1 := q 1279 10000
  b2 := q 640 10000
  a1 := q (-11683) 10000
  a2 := q 4241 10000

/-- **Limit-cycles after naive quantization.**

    A resonator whose ℝ design places the poles at radius `r = 0.999` and angle
    `θ = π/3` — stable, if only just.  Writing the denominator coefficients in
    terms of the poles, `a1 = -2r·cos θ` and `a2 = r²`, gives
    `a1 = -0.999`, `a2 = 0.998001`.

    Quantizing those to a coarse grid — here rounding to the nearest integer,
    which is what you get if the coefficient ROM is too narrow — lands exactly on
    `a1 = -1`, `a2 = 1`, i.e. `r = 1` precisely.  The poles are now *on* the unit
    circle: an undamped resonator.

    The measured consequence (see `Tests/IP/Control/IIRBiquadTest.lean`, which
    asserts this exact sequence): a single impulse at `n = 0` followed by zero
    input forever produces the **period-6 limit cycle**

        62, 62, 0, -63, -63, 0, 62, 62, 0, -63, -63, 0, …

    in units of 1e-3, sustained indefinitely with no further excitation.  Note
    the asymmetry (`62` up, `-63` down): that is the floor-rounding of the
    arithmetic shift showing through, and it is why the cycle is a genuine
    fixed-point artefact rather than just the ℝ resonator's ringing.

    This is the DSVerifier limit-cycle scenario, reached without doing anything
    obviously stupid — and unlike a BMC tool, `proofs/` can state the contrast as
    an unbounded theorem about `stableLPF` rather than a bounded-horizon check. -/
def naiveLPF : Coeffs where
  b0 := q 1 16
  b1 := 0#32
  b2 := 0#32
  a1 := q (-1) 1
  a2 := q 1 1

/-- Default state clamp: ±64.0 in Q15.16.  Leaves 9 bits of headroom below the
    32-bit rail, so `satAdd` inside a step can never itself saturate — that
    separation is what lets the proof treat the clamp as the *only* nonlinearity. -/
def defaultLim : BitVec 32 := BitVec.ofInt 32 (64 * (2 ^ 16))

/-- The stable filter, fully specialised — this is the top the tests synthesize. -/
def stableBiquad (x : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  biquad defaultLim x
    (Signal.pure stableLPF.b0) (Signal.pure stableLPF.b1) (Signal.pure stableLPF.b2)
    (Signal.pure stableLPF.a1) (Signal.pure stableLPF.a2)

/-- The naively-quantized filter, fully specialised. -/
def naiveBiquad (x : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  biquad defaultLim x
    (Signal.pure naiveLPF.b0) (Signal.pure naiveLPF.b1) (Signal.pure naiveLPF.b2)
    (Signal.pure naiveLPF.a1) (Signal.pure naiveLPF.a2)

end Sparkle.IP.Control.IIRBiquad
