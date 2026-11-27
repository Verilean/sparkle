/-
  FFT.Unrolled — fixed-size, non-recursive spellings of the network.

  ## Why these exist

  Sparkle's Verilog elaborator inlines non-recursive definitions, but it
  cannot unfold a recursive one and does not reduce type-class
  projections.  `ctWith` is both recursive and reached through
  `AlgOn`'s projections, so a top written directly against it stalls.

  These definitions remove exactly those two obstacles and nothing
  else:

  * the recursion is unrolled for `N = 2, 4, 8`;
  * the carrier operations arrive as **explicit function arguments**
    (`…Ops`) rather than through a dictionary, so the synthesiser sees
    concrete, inlinable functions.

  The class-driven wrappers (`ct2u`, `ct4u`, `ct8u`, `fs8u`) are then
  defined by applying the `…Ops` forms to the inferred instance, and
  each is proved **definitionally equal** to the recursive `ctWith` /
  `fourStepWith` by `rfl`.  So the synthesisable spelling and the
  spelling the proofs in `FFT/Equiv.lean` talk about are the same
  term — there is no second implementation to keep in step.

  A macro that unrolls `ctWith` at elaboration time for arbitrary `N`
  would generalise this; these three sizes are what the current tops
  need.
-/
import FFT.Algebra
import FFT.CooleyTukey
import FFT.FourStep

namespace FFTNTT

/-! ## Explicit-dictionary forms

    `add`/`sub`/`mulc`/`reg` are the four carrier operations, passed by
    hand.  Everything downstream of these is first-order and
    projection-free, which is what the Verilog elaborator needs. -/

section Ops
variable {β α : Type}
  (add sub : β → β → β) (mulc : α → β → β) (reg : β → β)
  (tw : Nat → Nat → α)

/-- 2-point transform: one butterfly, trivial twiddle. -/
def ct2uOps (x0 x1 : β) : β × β :=
  let e := reg x0
  let o := reg x1
  let t := mulc (tw 2 0) o
  (add e t, sub e t)

/-- 4-point transform: two 2-point stages and a twiddle row. -/
def ct4uOps (x0 x1 x2 x3 : β) : β × β × β × β :=
  let ev := ct2uOps add sub mulc reg tw x0 x2
  let od := ct2uOps add sub mulc reg tw x1 x3
  let e0 := reg ev.1; let e1 := reg ev.2
  let o0 := reg od.1; let o1 := reg od.2
  let t0 := mulc (tw 4 0) o0
  let t1 := mulc (tw 4 1) o1
  (add e0 t0, add e1 t1, sub e0 t0, sub e1 t1)

/-- 8-point transform: `(8/2)·3 = 12` butterflies in one cone. -/
def ct8uOps (x0 x1 x2 x3 x4 x5 x6 x7 : β) :
    β × β × β × β × β × β × β × β :=
  let ev := ct4uOps add sub mulc reg tw x0 x2 x4 x6
  let od := ct4uOps add sub mulc reg tw x1 x3 x5 x7
  let e0 := reg ev.1; let e1 := reg ev.2.1
  let e2 := reg ev.2.2.1; let e3 := reg ev.2.2.2
  let o0 := reg od.1; let o1 := reg od.2.1
  let o2 := reg od.2.2.1; let o3 := reg od.2.2.2
  let t0 := mulc (tw 8 0) o0
  let t1 := mulc (tw 8 1) o1
  let t2 := mulc (tw 8 2) o2
  let t3 := mulc (tw 8 3) o3
  (add e0 t0, add e1 t1, add e2 t2, add e3 t3,
   sub e0 t0, sub e1 t1, sub e2 t2, sub e3 t3)

/-- The same 8-point transform as a four-step `2 × 4`: four 2-point
    column networks, a twiddle array, two 4-point row networks, and a
    transpose that is pure wiring. -/
def fs8uOps (x0 x1 x2 x3 x4 x5 x6 x7 : β) :
    β × β × β × β × β × β × β × β :=
  -- Step 1: columns.  Column `c` holds `x[c]` and `x[4+c]`.
  let b0 := ct2uOps add sub mulc reg tw x0 x4
  let b1 := ct2uOps add sub mulc reg tw x1 x5
  let b2 := ct2uOps add sub mulc reg tw x2 x6
  let b3 := ct2uOps add sub mulc reg tw x3 x7
  -- Steps 2+3: twiddle by ω_8^{c·k₁}, then a 4-point row transform.
  let d0 := ct4uOps add sub mulc reg tw
    (reg (mulc (tw 8 0) b0.1)) (reg (mulc (tw 8 0) b1.1))
    (reg (mulc (tw 8 0) b2.1)) (reg (mulc (tw 8 0) b3.1))
  let d1 := ct4uOps add sub mulc reg tw
    (reg (mulc (tw 8 0) b0.2)) (reg (mulc (tw 8 1) b1.2))
    (reg (mulc (tw 8 2) b2.2)) (reg (mulc (tw 8 3) b3.2))
  -- Step 4: transpose.  X[k₂·2 + k₁] = D[k₁][k₂].
  (d0.1, d1.1, d0.2.1, d1.2.1, d0.2.2.1, d1.2.2.1, d0.2.2.2, d1.2.2.2)

end Ops

/-! ## Class-driven wrappers

    What ordinary callers use: the operations come from `AlgOn` by
    inference, exactly as in the recursive network. -/

section Wrappers
variable {β α : Type} [AlgOn β α] (tw : Nat → Nat → α)

@[inline] def ct2u : β → β → β × β := ct2uOps cadd csub cmul creg tw
@[inline] def ct4u : β → β → β → β → β × β × β × β := ct4uOps cadd csub cmul creg tw
@[inline] def ct8u : β → β → β → β → β → β → β → β →
    β × β × β × β × β × β × β × β := ct8uOps cadd csub cmul creg tw
@[inline] def fs8u : β → β → β → β → β → β → β → β →
    β × β × β × β × β × β × β × β := fs8uOps cadd csub cmul creg tw

/-- The recursive four-step network at `2 × 4`, for comparison. -/
def fs8ref (x : HVec β 8) : HVec β 8 :=
  fourStepWith tw 2 4 (ctWith tw 1) (ctWith tw 2) x

end Wrappers

/-! ## Each unrolled form *is* the recursive one

    All four hold by `rfl`: the unrolling is a definitional identity,
    not a separate implementation that happens to agree.  That is what
    carries the circuit/model equivalence and the pipeline-latency
    theorem over to the synthesised tops. -/

section Equalities
variable {β α : Type} [AlgOn β α] (tw : Nat → Nat → α)

theorem ct2u_eq (x : HVec β 2) :
    ct2u tw (x 0) (x 1) = (ctWith tw 1 x 0, ctWith tw 1 x 1) := rfl

theorem ct4u_eq (x : HVec β 4) :
    ct4u tw (x 0) (x 1) (x 2) (x 3)
      = (ctWith tw 2 x 0, ctWith tw 2 x 1, ctWith tw 2 x 2, ctWith tw 2 x 3) := rfl

theorem ct8u_eq (x : HVec β 8) :
    ct8u tw (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)
      = (ctWith tw 3 x 0, ctWith tw 3 x 1, ctWith tw 3 x 2, ctWith tw 3 x 3,
         ctWith tw 3 x 4, ctWith tw 3 x 5, ctWith tw 3 x 6, ctWith tw 3 x 7) := rfl

theorem fs8u_eq (x : HVec β 8) :
    fs8u tw (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)
      = (fs8ref tw x 0, fs8ref tw x 1, fs8ref tw x 2, fs8ref tw x 3,
         fs8ref tw x 4, fs8ref tw x 5, fs8ref tw x 6, fs8ref tw x 7) := rfl

end Equalities

end FFTNTT
