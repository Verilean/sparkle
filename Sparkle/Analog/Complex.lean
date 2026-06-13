import Sparkle.Analog.Num

/-!
# Complex numbers for AC small-signal analysis

A small, Mathlib-free complex type, in the same spirit as `Num.lean`'s scalar
operations: just enough arithmetic to run Modified Nodal Analysis over phasors.
AC analysis evaluates each device's linearized law with the differential operator
`ddt` replaced by `jω`, so the resulting admittance stamps are complex; this is
the carrier they live in.

Kept distinct from Mathlib's `ℂ` (used only in the proofs library) so the
simulator stays Mathlib-free and the WASM build intact. An `Analog Complex`
instance lets the existing `AExpr` evaluator interpret an expression into phasors
with no solver changes.
-/

namespace Sparkle.Analog

/-- A complex number `re + im·j`. -/
structure Complex where
  re : Float
  im : Float
  deriving Repr, Inhabited, BEq

namespace Complex

/-- A real embedded as a complex number. -/
def ofFloat (x : Float) : Complex := ⟨x, 0.0⟩

/-- The imaginary unit `j`. -/
def I : Complex := ⟨0.0, 1.0⟩

def add (a b : Complex) : Complex := ⟨a.re + b.re, a.im + b.im⟩
def sub (a b : Complex) : Complex := ⟨a.re - b.re, a.im - b.im⟩
def neg (a : Complex) : Complex := ⟨-a.re, -a.im⟩

/-- `(a+bj)(c+dj) = (ac−bd) + (ad+bc)j`. -/
def mul (a b : Complex) : Complex :=
  ⟨a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re⟩

/-- `|z|² = re² + im²`. -/
def normSq (a : Complex) : Float := a.re * a.re + a.im * a.im

/-- Complex division `a / b = a·conj b / |b|²`. -/
def div (a b : Complex) : Complex :=
  let d := b.normSq
  ⟨(a.re * b.re + a.im * b.im) / d, (a.im * b.re - a.re * b.im) / d⟩

/-- Magnitude `|z| = √(re² + im²)`. -/
def magnitude (a : Complex) : Float := Float.sqrt a.normSq

/-- Argument `arg z ∈ (−π, π]`, in radians. -/
def phase (a : Complex) : Float := Float.atan2 a.im a.re

/-- `e^(re + im·j) = e^re·(cos im + j·sin im)`. -/
def exp (a : Complex) : Complex :=
  let r := Float.exp a.re
  ⟨r * Float.cos a.im, r * Float.sin a.im⟩

/-- Principal branch `log z = ln|z| + j·arg z`. -/
def log (a : Complex) : Complex := ⟨Float.log a.magnitude, a.phase⟩

/-- `sin (a+bj) = sin a·cosh b + j·cos a·sinh b`. -/
def sin (a : Complex) : Complex :=
  ⟨Float.sin a.re * Float.cosh a.im, Float.cos a.re * Float.sinh a.im⟩

/-- `cos (a+bj) = cos a·cosh b − j·sin a·sinh b`. -/
def cos (a : Complex) : Complex :=
  ⟨Float.cos a.re * Float.cosh a.im, -(Float.sin a.re * Float.sinh a.im)⟩

instance : Add Complex := ⟨add⟩
instance : Sub Complex := ⟨sub⟩
instance : Mul Complex := ⟨mul⟩
instance : Div Complex := ⟨div⟩
instance : Neg Complex := ⟨neg⟩

end Complex

/-- The complex carrier: `AExpr.eval`/`evalWith` over `Complex` interprets an
expression as a phasor. -/
instance : Analog Complex where
  ofFloat := Complex.ofFloat
  add := Complex.add
  sub := Complex.sub
  mul := Complex.mul
  div := Complex.div
  neg := Complex.neg
  exp := Complex.exp
  log := Complex.log
  sin := Complex.sin
  cos := Complex.cos

/-- Forward-mode dual number over the complex carrier: `val + eps·ε`, where `eps`
carries the derivative with respect to a single seeded unknown. This is `Dual`
(in `Num.lean`) with `Complex` in place of `Float`; AC small-signal analysis uses
it to linearize a device law at the DC operating point and read off the complex
admittance `∂(residual)/∂(unknown)` directly. -/
structure DualC where
  val : Complex
  eps : Complex
  deriving Repr, Inhabited

namespace DualC

/-- A constant: derivative zero. -/
def const (x : Complex) : DualC := ⟨x, Complex.ofFloat 0.0⟩

/-- The unknown being differentiated against: derivative one. -/
def var (x : Complex) : DualC := ⟨x, Complex.ofFloat 1.0⟩

instance : Analog DualC where
  ofFloat x := const (Complex.ofFloat x)
  add a b := ⟨a.val + b.val, a.eps + b.eps⟩
  sub a b := ⟨a.val - b.val, a.eps - b.eps⟩
  mul a b := ⟨a.val * b.val, a.eps * b.val + a.val * b.eps⟩
  div a b := ⟨a.val / b.val, (a.eps * b.val - a.val * b.eps) / (b.val * b.val)⟩
  neg a := ⟨-a.val, -a.eps⟩
  exp a := let e := Complex.exp a.val; ⟨e, a.eps * e⟩
  log a := ⟨Complex.log a.val, a.eps / a.val⟩
  sin a := ⟨Complex.sin a.val, a.eps * Complex.cos a.val⟩
  cos a := ⟨Complex.cos a.val, -(a.eps * Complex.sin a.val)⟩

end DualC

-- |3 + 4j| = 5
#guard (Complex.mk 3.0 4.0).magnitude == 5.0
-- e^(jπ) ≈ −1 (within Float tolerance)
#guard ((Complex.exp ⟨0.0, pi⟩).re + 1.0).abs < 1e-12

end Sparkle.Analog
