/-
  FFT.Spec — the specification layer: the DFT written as a sum.

  This is the top of the VDD stack for the FFT work.  It is
  deliberately the *slowest possible* description — `n²` products, no
  structure exploited — because its only job is to be obviously
  correct.  Everything else in `FFT/` is judged against it.

  Note that it is written against the same `AlgOn` carrier as the
  circuits, so `dft` instantiated at `β := Signal dom α` is itself a
  (huge, but legal) circuit.  That is what makes the equivalence
  statement `ct m x = dft (2^m) x` a statement about two circuits of
  the same type rather than a refinement across two languages.
-/
import FFT.Algebra

namespace FFTNTT

open Sparkle.Core.Domain
open Sparkle.Core.Signal

variable {β α : Type} [AlgOn β α]

/-- The DFT as a literal sum, parameterised by the twiddle family:

      X[k] = Σ_{j<n} tw(n, j·k mod n) · x[j]

    `Fin.foldr` walks `j` from `n−1` down to `0`, so the accumulation
    order is fixed and the definition is bit-exact rather than merely
    mathematically determined — which matters for the fixed-point
    instance, where addition is not associative. -/
def dftWith (tw : Nat → Nat → α) (n : Nat) (x : HVec β n) : HVec β n :=
  fun k => Fin.foldr n
    (fun j acc => cadd (cmul (tw n (j.val * k.val % n)) (x j)) acc)
    (czero (α := α))

/-- Forward DFT. -/
@[inline] def dft [FFTRoot α] (n : Nat) (x : HVec β n) : HVec β n :=
  dftWith FFTRoot.twiddle n x

/-- Unnormalised inverse DFT (`n · x`). -/
@[inline] def idftRaw [FFTRoot α] (n : Nat) (x : HVec β n) : HVec β n :=
  dftWith FFTRoot.invTwiddle n x

/-- Inverse DFT, normalised by `1/n`. -/
@[inline] def idft [FFTRoot α] (n : Nat) (x : HVec β n) : HVec β n :=
  HVec.map (cmul (FFTRoot.scaleInv n (FFTAlg.one : α))) (idftRaw n x)

end FFTNTT
