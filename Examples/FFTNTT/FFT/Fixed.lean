/-
  FFT.Fixed — the ordinary-FFT coefficient ring: complex numbers in
  two's-complement Q-format.

  `Cx w f` is a pair of `w`-bit signed words with `f` fractional bits,
  so the represented value is `(re + i·im) / 2^f` and the usable range
  is `[−2^{w−f−1}, 2^{w−f−1})`.  `Cx 16 14` — Q1.14 — is the default.

  ## Multiplication

  Textbook 4-multiply complex product, each real product taken at full
  `2w` width, then rounded back:

      re = ((a.re·b.re − a.im·b.im) + 2^{f−1}) >>a f
      im = ((a.re·b.im + a.im·b.re) + 2^{f−1}) >>a f

  The `+2^{f−1}` is round-to-nearest; without it the FFT accumulates a
  DC bias of half an LSB per stage, which is the usual reason a
  hand-rolled fixed-point FFT drifts.

  ## What is *not* modelled

  `add` and `sub` wrap.  A radix-2 DIT stage can grow the magnitude by
  up to a factor of two, so a `w`-bit unscaled transform of length `N`
  needs `log₂N` integer bits of headroom, or per-stage scaling.  That
  is a genuine design decision, not an implementation detail, so it is
  left to the caller rather than baked in: `Cx.half` is provided for a
  scaled (1/N) datapath, and the reference model wraps in exactly the
  same way as the circuit, so the equivalence statement is unaffected
  either way.

  ## Float

  Twiddle constants are produced from `Float` trigonometry at
  *elaboration* time and are frozen into `BitVec` literals before any
  circuit or proof sees them.  No `Float` survives into a theorem
  statement — Lean's kernel has no decidable equality for it (see the
  project's notes on `ℚ`/`BitVec` for proofs).
-/
import FFT.Algebra

namespace FFTNTT

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ## Elaboration-time constant generation -/

/-- π to double precision.  Used only to build twiddle literals. -/
def piF : Float := 3.14159265358979323846

/-- Round a `Float` to a signed `w`-bit Q-format word with `f`
    fractional bits, saturating rather than wrapping on overflow.
    Evaluated on literal arguments at elaboration time. -/
def qOfFloat (w f : Nat) (x : Float) : BitVec w :=
  let scaled : Float := x * (2 ^ f : Nat).toFloat
  let r : Float := scaled.round
  let hi : Int := (2 : Int) ^ (w - 1) - 1
  let lo : Int := -((2 : Int) ^ (w - 1))
  let mag : Int := Int.ofNat ((if r < 0.0 then -r else r).toUInt64.toNat)
  let v : Int := if r < 0.0 then -mag else mag
  BitVec.ofInt w (if v > hi then hi else if v < lo then lo else v)

/-! ## The ring -/

/-- A complex number in Q-format: `w` bits per component, `f`
    fractional bits, two's complement. -/
structure Cx (w : Nat) (f : Nat) where
  re : BitVec w
  im : BitVec w
  deriving Repr, DecidableEq, Inhabited, BEq

namespace Cx

variable {w f : Nat}

/-- Build from a pair of reals (elaboration time). -/
@[inline] def ofFloats (w f : Nat) (re im : Float) : Cx w f :=
  ⟨qOfFloat w f re, qOfFloat w f im⟩

/-- Interpret back as a pair of reals.  Testbench / reporting only. -/
def toFloats (a : Cx w f) : Float × Float :=
  let dec (b : BitVec w) : Float := Float.ofInt b.toInt / (2 ^ f : Nat).toFloat
  (dec a.re, dec a.im)

@[inline] def add (a b : Cx w f) : Cx w f := ⟨a.re + b.re, a.im + b.im⟩
@[inline] def sub (a b : Cx w f) : Cx w f := ⟨a.re - b.re, a.im - b.im⟩

/-- Arithmetic halving — one stage of a scaled (1/N) datapath. -/
@[inline] def half (a : Cx w f) : Cx w f :=
  ⟨a.re.sshiftRight 1, a.im.sshiftRight 1⟩

/-- Round-to-nearest requantisation of a `2w`-bit product back to
    `w` bits with `f` fractional bits. -/
@[inline] private def requant (x : BitVec (2 * w)) : BitVec w :=
  let bias : BitVec (2 * w) := BitVec.ofNat (2 * w) (if f == 0 then 0 else 2 ^ (f - 1))
  ((x + bias).sshiftRight f).setWidth w

/-- Four-multiplier complex product with round-to-nearest. -/
@[inline] def mul (a b : Cx w f) : Cx w f :=
  let W := 2 * w
  let ar : BitVec W := a.re.signExtend W
  let ai : BitVec W := a.im.signExtend W
  let br : BitVec W := b.re.signExtend W
  let bi : BitVec W := b.im.signExtend W
  ⟨requant (f := f) (ar * br - ai * bi),
   requant (f := f) (ar * bi + ai * br)⟩

/-- Complex conjugate — one inverter, and the whole of the inverse
    transform when `ifft x = conj (fft (conj x)) / N`. -/
@[inline] def conj (a : Cx w f) : Cx w f := ⟨a.re, -a.im⟩

end Cx

/-- The default fixed-point coefficient type: Q1.14 complex, 32 bits
    per sample. -/
abbrev C16_14 : Type := Cx 16 14

instance instFFTAlgCx (w f : Nat) : FFTAlg (Cx w f) where
  zero := ⟨0, 0⟩
  one  := Cx.ofFloats w f 1.0 0.0
  add  := Cx.add
  sub  := Cx.sub
  mul  := Cx.mul

instance instFFTRootCx (w f : Nat) : FFTRoot (Cx w f) where
  -- ω_n^k = exp(−2πik/n) = cos θ − i sin θ, each component rounded
  -- directly from the real value rather than built by iterating `mul`.
  twiddle n k :=
    let θ : Float := -2.0 * piF * k.toFloat / n.toFloat
    Cx.ofFloats w f θ.cos θ.sin
  invTwiddle n k :=
    let θ : Float := 2.0 * piF * k.toFloat / n.toFloat
    Cx.ofFloats w f θ.cos θ.sin
  scaleInv n a := Cx.mul (Cx.ofFloats w f (1.0 / n.toFloat) 0.0) a

/-! ## Hardware wiring -/

instance (w f : Nat) : Sparkle.Core.Wireable (Cx w f) := ⟨2 * w⟩

instance (w f : Nat) : Sparkle.Data.BitPack.BitPack (Cx w f) (w + w) where
  toBitVec a   := a.im ++ a.re
  fromBitVec b := ⟨b.setWidth w, (b >>> w).setWidth w⟩

end FFTNTT
