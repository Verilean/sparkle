/-
  Precision-parametric fixed-point arithmetic — Q(w-f).f signed, `BitVec w`.

  This generalises `IP/Control/FixedPoint.lean`, where the format was hardcoded
  to Q15.16 in ~44 places.  Here the total width `w` and the fractional-bit count
  `f` are ordinary `Nat` arguments, so one definition serves every precision and
  the *error bound becomes a function of `f`* — which is the point.  See
  `proofs/SparkleProofs/Control/Precision.lean`, which proves that Q7.8 misses a
  stated error budget while Q15.16 meets it.  That is a machine-checked
  precision-selection argument; it is not expressible while the format is a
  hardcoded constant.

  ## Synthesis

  Width-generic definitions **do** lower to Verilog, provided the top is
  instantiated at a *concrete* width — `mulQGen 16 8` synthesizes, a top left
  polymorphic in `w` does not (there is no such thing as a Verilog module of
  unknown width).  So the pattern throughout `IP/Control/` is:

  * generic definitions here and in `IIRBiquadGen.lean` etc. — used by the proofs;
  * a handful of concrete instantiations (Q7.8 / Q15.16 / Q23.8) that are the
    actual synthesizable tops.

  Verified by probe: both a generic `+` and the hard case (generic
  `extractLsb' f w` over a `w+w` widening multiply) emit Verilog at `w = 16`.

  ## Interpretation

  A `BitVec w` holding `x` denotes `x.toInt / 2^f`.  The scale is an explicit
  argument rather than type-level information; see `IP/Control/FixedPoint.lean`'s
  header for why (the house style keeps it in comments, which has already
  produced two false theorem statements in `IP/BitNet/Spec/FixedPoint.lean`).

  ## Rounding

  `BitVec.sshiftRight k` and `Int./ 2^k` are the same function in Lean 4 — both
  floor.  (`Int.tdiv` is the truncating one.)  So the RTL's shift and the spec's
  division agree exactly, and the quantization error of one scaling step lies in
  `(-1, 0]` LSB independent of sign.  That one-sidedness is what
  `Precision.lean`'s bound relies on.
-/

import Sparkle
import Sparkle.Compiler.Elab

namespace Sparkle.IP.Control.FixedPointGen

open Sparkle.Core.Domain
open Sparkle.Core.Signal

variable {dom : DomainConfig}

/-! ### Formats

A `Format` bundles the two numbers that describe a fixed-point encoding.  Kept as
a structure so instantiations read as `Q15_16` rather than as a bare pair. -/

/-- A signed fixed-point format: `w` total bits, `f` fractional bits. -/
structure Format where
  /-- Total width in bits (including the sign bit). -/
  w : Nat
  /-- Fractional bits. -/
  f : Nat
  deriving Repr, DecidableEq

/-- Q7.8 — 16-bit, 8 fractional. Range ±128, resolution 2⁻⁸ ≈ 3.9e-3. -/
def Q7_8 : Format := ⟨16, 8⟩

/-- Q15.16 — 32-bit, 16 fractional. Range ±32768, resolution 2⁻¹⁶ ≈ 1.5e-5.
    The format `IP/Control/FixedPoint.lean` hardcodes. -/
def Q15_16 : Format := ⟨32, 16⟩

/-- Q23.8 — 32-bit, 8 fractional. Same width as Q15.16 but trades resolution for
    range; useful for showing that it is `f`, not `w`, that drives the error
    bound. -/
def Q23_8 : Format := ⟨32, 8⟩

/-- Q11.4 — 16-bit, 4 fractional. Deliberately coarse; used as a negative
    example. -/
def Q11_4 : Format := ⟨16, 4⟩

/-- One, in the given format. -/
def one (w f : Nat) : BitVec w := BitVec.ofNat w (2 ^ f)

/-- The Q(w-f).f word nearest `n / d`.  The rounding is truncation toward zero on
    the *rational* `n/d`, which is the host-side coefficient quantization — not to
    be confused with the datapath's floor. -/
def q (w f : Nat) (n d : Int) : BitVec w := BitVec.ofInt w (n * (2 ^ f) / d)

/-! ### Pure (`BitVec`) reference semantics

The proofs reason about these; the `Signal` counterparts below are what lowers to
Verilog, and they are written to mirror these definition-for-definition. -/

/-- Signed widening Q multiply: `(a * b) >> f`, computed in `w + w` bits so the
    product cannot wrap, then narrowed back to `w`.

    This is the correct version of the multiply that
    `IP/Drone/StateEstimator.fixMul`, `IP/Humanoid/ZMPBalance.fmul` and
    `IP/Humanoid/InverseKinematics.fxMul` all get wrong: they write `a ++ 0#32`
    intending a zero-extension, but `++` puts `a` in the *high* half, so the
    product is `a*b*2^32 ≡ 0` and those functions return `0` for every input. -/
def mulQ (w f : Nat) (a b : BitVec w) : BitVec w :=
  BitVec.extractLsb' f w ((a.signExtend (w + w)) * (b.signExtend (w + w)))

/-- Saturating signed add, computed one bit wide so the sum cannot wrap before it
    is clamped. -/
def satAdd (w : Nat) (a b : BitVec w) : BitVec w :=
  let s : BitVec (w + 1) := (a.signExtend (w + 1)) + (b.signExtend (w + 1))
  let hi : BitVec (w + 1) := BitVec.ofInt (w + 1) (2 ^ (w - 1) - 1)
  let lo : BitVec (w + 1) := BitVec.ofInt (w + 1) (-(2 ^ (w - 1)))
  if BitVec.slt hi s then BitVec.ofInt w (2 ^ (w - 1) - 1)
  else if BitVec.slt s lo then BitVec.ofInt w (-(2 ^ (w - 1)))
  else BitVec.extractLsb' 0 w s

/-- Clamp to a symmetric range `[-lim, lim]`. -/
def clampSym (w : Nat) (lim x : BitVec w) : BitVec w :=
  let negLim := -lim
  if BitVec.slt lim x then lim
  else if BitVec.slt x negLim then negLim
  else x

/-! ### Signal (synthesizable) counterparts -/

/-- Sign-extend a `w`-bit signal to `w + w` bits.

    Written as an explicit MSB test + `mux` of the high word rather than
    `Signal.map (·.signExtend _)`, because the synthesis elaborator only lowers a
    `.map` lambda that is a single `extractLsb'` or a constant-prefix `append` —
    `signExtend` is neither.  Same shape as the `#synthesizeVerilog`-verified
    `IP/YOLOv8/Primitives/Requantize.mulAccScale`. -/
def sextDouble (w : Nat) (a : Signal dom (BitVec w)) : Signal dom (BitVec (w + w)) :=
  let isNeg := a.map (BitVec.extractLsb' (w - 1) 1 ·) === (Signal.pure 1#1)
  let ones : Signal dom (BitVec w) := Signal.pure (BitVec.allOnes w)
  let zeros : Signal dom (BitVec w) := Signal.pure (BitVec.zero w)
  (Signal.mux isNeg ones zeros) ++ a

/-- Signal-level Q multiply.  Mirrors `mulQ`. -/
def mulQSig (w f : Nat) (a b : Signal dom (BitVec w)) : Signal dom (BitVec w) :=
  (sextDouble w a * sextDouble w b).map (BitVec.extractLsb' f w ·)

/-- Clamp to a *constant* symmetric range.  Preferred inside `circuit do`: the
    constant bound keeps the emitted comparator a compare-against-literal, and it
    makes the ultimate-bound theorem a closed statement. -/
def clampSymC (w : Nat) (lim : BitVec w) (x : Signal dom (BitVec w))
    : Signal dom (BitVec w) :=
  let hi : Signal dom (BitVec w) := Signal.pure lim
  let lo : Signal dom (BitVec w) := Signal.pure (-lim)
  Signal.mux (Signal.slt hi x) hi (Signal.mux (Signal.slt x lo) lo x)

end Sparkle.IP.Control.FixedPointGen
