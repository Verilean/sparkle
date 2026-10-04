/-
  FFT.Algebra — coefficient algebra and carrier abstraction for
  the generic FFT / NTT datapath.

  ## Why two type classes

  A butterfly needs two *independent* things:

  1. **What the coefficients are** — a commutative ring with a
     primitive n-th root of unity.  For an NTT this is `ZMod p`
     realised as a `BitVec`; for a fixed-point FFT it is a complex
     Q-format pair.  This is `FFTAlg` / `FFTRoot`.

  2. **What the wires carry** — during *specification* a butterfly
     network operates on plain coefficients (`α`), during
     *implementation* on hardware signals (`Signal dom α`).  This is
     `AlgOn β α`: "the carrier `β` transports coefficients of type
     `α`".  `α` is an `outParam`, so writing `cadd a b` picks the
     coefficient ring from the carrier without any annotation.

  Splitting them this way means the Cooley–Tukey network is written
  **once** and instantiated four ways by type inference alone:

  | carrier `β`           | coeff `α`  | what you get                |
  |-----------------------|------------|-----------------------------|
  | `Zp p w`              | `Zp p w`   | NTT reference model         |
  | `Signal dom (Zp p w)` | `Zp p w`   | NTT *circuit*               |
  | `Cx w f`              | `Cx w f`   | fixed-point reference model |
  | `Signal dom (Cx w f)` | `Cx w f`   | fixed-point FFT *circuit*   |

  and the circuit-vs-model equivalence proof is an induction over the
  *same* recursion, not over two separately written programs.

  ## Vectors

  Data is carried as `HVec β n := Fin n → β`.  A function is the right
  choice here: it is total (no `Array` bounds panics inside a circuit
  description), every index resolves at elaboration time for a
  statically sized transform, and `funext` makes equational reasoning
  about permutations (bit-reversal, transpose) painless.
-/
import Sparkle

namespace FFTNTT

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ## Statically sized vectors -/

/-- A statically sized bundle of hardware values.  Elements are
    individual wires, so `HVec (Signal dom α) n` is `n` parallel
    buses rather than one packed word. -/
abbrev HVec (β : Type) (n : Nat) : Type := Fin n → β

namespace HVec

/-- Reindex along an index function.  Permutations, transposes and
    decimations are all instances of this. -/
@[inline] def comap {β : Type} {m n : Nat} (f : Fin m → Fin n)
    (x : HVec β n) : HVec β m := fun i => x (f i)

/-- Elementwise map. -/
@[inline] def map {β γ : Type} {n : Nat} (f : β → γ) (x : HVec β n) :
    HVec γ n := fun i => f (x i)

/-- Build from a list, padding with `default` if the list is short.
    Testbench convenience only. -/
def ofList {β : Type} [Inhabited β] (n : Nat) (l : List β) : HVec β n :=
  fun i => l.getD i.val default

/-- Read out in index order. -/
def toList {β : Type} {n : Nat} (x : HVec β n) : List β :=
  Fin.foldr n (fun i acc => x i :: acc) []

end HVec

/-! ## The coefficient ring -/

/-- The ring operations a butterfly needs from its coefficient type.

    Deliberately *not* Mathlib's `CommRing`: the instances here are
    concrete `BitVec`-backed hardware types whose `mul` is a specific
    reduction algorithm (Barrett, Q-format rounding).  Keeping the
    class small keeps bit-exactness obligations `decide`-shaped. -/
class FFTAlg (α : Type) where
  zero : α
  one  : α
  add  : α → α → α
  sub  : α → α → α
  mul  : α → α → α

/-- A coefficient ring that also supplies roots of unity.

    `twiddle n k` must be `ω_n ^ k` for a primitive `n`-th root `ω_n`,
    and the family must be *consistent across `n`*: `ω_{n·m} ^ m = ω_n`.
    Both provided instances satisfy this — the NTT one exactly, the
    fixed-point one up to rounding — and it is precisely the property
    the four-step decomposition needs.

    Exposing `twiddle` per-`n`, rather than a single `ω` iterated with
    `mul`, matters for the fixed-point instance: powers built by
    repeated rounded multiplication accumulate error linearly in `k`,
    whereas a directly rounded `exp(-2πik/n)` does not. -/
class FFTRoot (α : Type) extends FFTAlg α where
  /-- `twiddle n k = ω_n ^ k`, `ω_n` a primitive `n`-th root of unity. -/
  twiddle : Nat → Nat → α
  /-- `invTwiddle n k = ω_n ^ (−k)`, for the inverse transform. -/
  invTwiddle : Nat → Nat → α
  /-- Multiplication by the constant `1/n`, normalising an inverse
      transform. -/
  scaleInv : Nat → α → α

/-! ## The carrier -/

/-- `AlgOn β α` says: values of type `β` carry coefficients of type
    `α`, and α's ring operations lift to β.

    `cmul` takes its left operand as a *coefficient*, not a carrier
    value: every multiplication in a Cooley–Tukey network is by a
    compile-time twiddle constant, so this signature is what lets the
    elaborator fold the multiplier into constant logic (a shift-add
    tree, or a ROM entry) instead of instantiating a general
    multiplier.

    `α` is an `outParam`: the carrier determines the ring. -/
class AlgOn (β : Type) (α : outParam Type) where
  czero : β
  cadd  : β → β → β
  csub  : β → β → β
  /-- Multiply a carried value by a coefficient constant. -/
  cmul  : α → β → β
  /-- Pipeline barrier.  `id` for the reference model, a register for
      a pipelined circuit.  Keeping it in the class (rather than
      threading an extra argument through the recursion) keeps the
      network description free of latency bookkeeping. -/
  creg  : β → β

export AlgOn (czero cadd csub cmul creg)

/-- The reference-model carrier: coefficients carry themselves.

    Low priority because its head is a bare variable — instance search
    should reach for a concrete carrier first and only fall back here. -/
instance (priority := low) instAlgOnSelf {α : Type} [FFTAlg α] : AlgOn α α where
  czero := FFTAlg.zero
  cadd  := FFTAlg.add
  csub  := FFTAlg.sub
  cmul  := FFTAlg.mul
  creg  := id

/-- The combinational hardware carrier.  `creg` is `id`, so a network
    built with this instance is one cone of logic between two register
    boundaries. -/
instance (priority := high) instAlgOnSignal {α : Type} [FFTAlg α]
    {dom : DomainConfig} : AlgOn (Signal dom α) α where
  czero := Signal.pure FFTAlg.zero
  cadd  := Signal.lift2 FFTAlg.add
  csub  := Signal.lift2 FFTAlg.sub
  cmul  := fun w s => Signal.map (FFTAlg.mul w) s
  creg  := id

/-- The pipelined hardware carrier: identical to `instAlgOnSignal`
    except that `creg` is a real D flip-flop, so consecutive FFT
    stages are separated by one clock cycle.

    Not registered as an instance — it has the same type as
    `instAlgOnSignal`, so the choice is made explicitly at the call
    site (see `ctPipelined`). -/
@[reducible] def algOnSignalPipelined (α : Type) [FFTAlg α]
    {dom : DomainConfig} : AlgOn (Signal dom α) α where
  czero := Signal.pure FFTAlg.zero
  cadd  := Signal.lift2 FFTAlg.add
  csub  := Signal.lift2 FFTAlg.sub
  cmul  := fun w s => Signal.map (FFTAlg.mul w) s
  creg  := Signal.register FFTAlg.zero

/-! ## Butterfly -/

section Butterfly
variable {β α : Type} [AlgOn β α]

/-- The radix-2 butterfly with the twiddle folded into the lower leg
    (decimation-in-time form):

        a ──────────┬── a + w·b
                    │
        b ──[× w]───┴── a − w·b

    One constant multiplier, one adder, one subtractor. -/
@[inline] def butterfly (w : α) (a b : β) : β × β :=
  let t := cmul w b
  (cadd a t, csub a t)

/-- Decimation-in-frequency butterfly: the twiddle sits *after* the
    subtract.  Same cost, different placement of the multiplier —
    which is what makes DIF's dataflow (natural in, bit-reversed out)
    the mirror image of DIT's. -/
@[inline] def butterflyDIF (w : α) (a b : β) : β × β :=
  (cadd a b, cmul w (csub a b))

end Butterfly

end FFTNTT
