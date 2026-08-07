/-
  Precision-parametric IIR biquad — Direct Form II transposed.

  The same filter as `IP/Control/IIRBiquad.lean`, but with the fixed-point format
  as an argument instead of hardcoded Q15.16.  That is what lets the *same*
  design be instantiated at several precisions and compared — and what makes the
  proven error bound a function of the fractional-bit count rather than a single
  constant.

  ## What the precision sweep shows (measured, not assumed)

  `Tests/IP/Control/PrecisionSweepTest.lean` runs one impulse through the same
  rational design at Q11.4 / Q7.8 / Q23.8 / Q15.16 / Q7.24.  Two results, both
  worth stating because neither is the naive expectation:

  **1. `f` governs accuracy; `w` is irrelevant to it.**  Q7.8 (`w=16`) and Q23.8
  (`w=32`) produce *bit-identical* tails — 15 and 15 for `stableCoeffs`, 0 and 0
  for `marginalCoeffs` — because they share `f = 8`.  Doubling the width buys
  dynamic range (it postpones saturation), not resolution.  The proven bound in
  `proofs/SparkleProofs/Control/Precision.lean` has the same shape: `Vbound`
  is a function of `f` alone.

  **2. Coarse quantization *damps* `marginalCoeffs` rather than destabilising it
  — the opposite of the folk intuition.**  Measured residual after 200 samples:

  ```
    f =  4  →  62      f = 8  →   0      f = 16 →  52      f = 24 →  52
  ```

  The non-monotonicity is real and has a clean explanation.  Rounding the
  denominator coefficients pulls the poles *inward*: the ℝ design sits at radius
  0.998999, and quantizing gives radius 0.968 at `f=4`, 0.998 at `f=8`, 0.99899
  at `f=16`.  Every format is stable.  What differs is the **deadband**: at `f=8`
  the LSB is coarse enough that once the state decays below it, `mulQ` floors the
  feedback product to zero and the ringing stops dead (measured: 62 → 23 → 0 by
  cycle 60).  At `f=16` the LSB is 256× finer, so the filter keeps ringing at the
  true ℝ decay rate and is still at 47 by cycle 290.

  So more precision means a *more faithful* reproduction of a design that was
  marginal to begin with.  Which is the honest lesson: quantization error and
  design margin are separate concerns, and adding fractional bits fixes only the
  first.  It is exactly the kind of interaction where you want a machine-checked
  bound instead of intuition.

  ## What the bound does and does not cover

  `Precision.lean` bounds the *quantization disturbance* — the additive error from
  flooring — and shows it shrinks 4× per fractional bit.  It does **not** cover
  coefficient quantization moving the poles, which perturbs the decay rate `ρ`
  rather than adding a disturbance.  The two mechanisms are kept separate on
  purpose; conflating them is how you get a bound that looks stronger than it is.
-/

import Sparkle
import Sparkle.Compiler.Elab
import IP.Control.FixedPointGen

set_option maxRecDepth 100000

namespace Sparkle.IP.Control.IIRBiquadGen

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Control.FixedPointGen

variable {dom : DomainConfig}

/-- Biquad coefficients, as exact rationals `num/den`.

    Deliberately *not* stored as `BitVec`: the whole point of the sweep is that
    one rational design gets quantized into several formats, so the design must
    be format-independent and the quantization must happen at instantiation. -/
structure RatCoeffs where
  b0n : Int
  b0d : Int
  b1n : Int
  b1d : Int
  b2n : Int
  b2d : Int
  a1n : Int
  a1d : Int
  a2n : Int
  a2d : Int
  deriving Repr

/-- Coefficients quantized into a concrete format. -/
structure Coeffs (w : Nat) where
  b0 : BitVec w
  b1 : BitVec w
  b2 : BitVec w
  a1 : BitVec w
  a2 : BitVec w
  deriving Repr, DecidableEq

/-- Quantize a rational design into Q(w-f).f.  This is the *only* place the
    format touches the coefficients. -/
def quantize (w f : Nat) (c : RatCoeffs) : Coeffs w where
  b0 := q w f c.b0n c.b0d
  b1 := q w f c.b1n c.b1d
  b2 := q w f c.b2n c.b2d
  a1 := q w f c.a1n c.a1d
  a2 := q w f c.a2n c.a2d

/-- Biquad state: the two delay registers of the transposed form. -/
structure State (w : Nat) where
  s1 : BitVec w
  s2 : BitVec w
  deriving Repr, DecidableEq

instance (w : Nat) : Inhabited (State w) := ⟨⟨BitVec.zero w, BitVec.zero w⟩⟩

/-- One cycle, with saturating output and saturating state. -/
def step (w f : Nat) (c : Coeffs w) (lim : BitVec w) (st : State w) (x : BitVec w)
    : State w × BitVec w :=
  let y := clampSym w lim (satAdd w (mulQ w f c.b0 x) st.s1)
  let s1' := clampSym w lim
    (satAdd w (satAdd w (mulQ w f c.b1 x) (-(mulQ w f c.a1 y))) st.s2)
  let s2' := clampSym w lim (satAdd w (mulQ w f c.b2 x) (-(mulQ w f c.a2 y)))
  (⟨s1', s2'⟩, y)

/-- Run on a list of samples, collecting outputs. -/
def run (w f : Nat) (c : Coeffs w) (lim : BitVec w)
    : State w → List (BitVec w) → List (BitVec w)
  | _, [] => []
  | st, x :: xs =>
    let (st', y) := step w f c lim st x
    y :: run w f c lim st' xs

/-! ### The circuit

Width-generic, so a concrete instantiation lowers to Verilog.  A top left
polymorphic in `w` cannot synthesize — there is no Verilog module of unknown
width — hence the concrete tops at the bottom of this file. -/

/-- Synthesizable Direct-Form-II-transposed biquad at format `(w, f)`. -/
def biquad (w f : Nat) (lim : BitVec w)
    (x b0 b1 b2 a1 a2 : Signal dom (BitVec w)) : Signal dom (BitVec w) :=
  circuit do
    let s1Reg ← Signal.reg (BitVec.zero w)
    let s2Reg ← Signal.reg (BitVec.zero w)

    let s1 := (s1Reg : Signal dom (BitVec w))
    let s2 := (s2Reg : Signal dom (BitVec w))

    let y := clampSymC w lim (mulQSig w f b0 x + s1)

    let a1y := mulQSig w f a1 y
    let a2y := mulQSig w f a2 y
    let zero := (Signal.pure (BitVec.zero w) : Signal dom (BitVec w))

    let s1Next := clampSymC w lim (mulQSig w f b1 x + (zero - a1y) + s2)
    let s2Next := clampSymC w lim (mulQSig w f b2 x + (zero - a2y))

    s1Reg <~ s1Next
    s2Reg <~ s2Next

    return y

/-- Instantiate the circuit from a quantized coefficient record. -/
def biquadOf (w f : Nat) (c : Coeffs w) (lim : BitVec w)
    (x : Signal dom (BitVec w)) : Signal dom (BitVec w) :=
  biquad w f lim x
    (Signal.pure c.b0) (Signal.pure c.b1) (Signal.pure c.b2)
    (Signal.pure c.a1) (Signal.pure c.a2)

/-! ### The rational designs

Both are format-independent; the sweep quantizes them. -/

/-- **Stable** — 2nd-order low-pass, fc/fs ≈ 0.1, poles at |p| ≈ 0.651.
    Comfortable margin: survives quantization down to fairly coarse formats. -/
def stableCoeffs : RatCoeffs where
  b0n :=    640
  b0d :=  10000
  b1n :=   1279
  b1d :=  10000
  b2n :=    640
  b2d :=  10000
  a1n := -11683
  a1d :=  10000
  a2n :=   4241
  a2d :=  10000

/-- **Marginal** — a resonator with ℝ poles at radius 0.998999, angle ≈ π/3.

    Stable over ℝ, but with only ~1e-3 of margin, so its behaviour is dominated by
    the format rather than by the design.  Every quantization is *also* stable
    (rounding pulls the poles inward — radius 0.968 at `f=4`, 0.998 at `f=8`,
    0.99899 at `f=16`), so this is not a "quantization destabilises it" example.

    What it exhibits instead is the **deadband**: at coarse `f` the ringing hits
    the quantization floor and stops dead, while at fine `f` it persists at the
    true ℝ decay rate.  See the file header for the measured numbers.  That
    non-monotonicity in precision is the point of including it. -/
def marginalCoeffs : RatCoeffs where
  b0n :=    1
  b0d :=   16
  b1n :=    0
  b1d :=    1
  b2n :=    0
  b2d :=    1
  a1n := -999
  a1d := 1000
  a2n :=  998
  a2d := 1000

/-- State clamp for a format: ±64.0. -/
def limOf (w f : Nat) : BitVec w := q w f 64 1

/-! ### Concrete synthesizable tops

One per format.  These are what `#synthesizeVerilog` accepts. -/

def stableQ7_8 (x : Signal dom (BitVec 16)) : Signal dom (BitVec 16) :=
  biquadOf 16 8 (quantize 16 8 stableCoeffs) (limOf 16 8) x

def stableQ15_16 (x : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  biquadOf 32 16 (quantize 32 16 stableCoeffs) (limOf 32 16) x

def stableQ23_8 (x : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  biquadOf 32 8 (quantize 32 8 stableCoeffs) (limOf 32 8) x

def marginalQ7_8 (x : Signal dom (BitVec 16)) : Signal dom (BitVec 16) :=
  biquadOf 16 8 (quantize 16 8 marginalCoeffs) (limOf 16 8) x

def marginalQ15_16 (x : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  biquadOf 32 16 (quantize 32 16 marginalCoeffs) (limOf 32 16) x

end Sparkle.IP.Control.IIRBiquadGen
