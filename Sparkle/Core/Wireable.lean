/-
  Sparkle.Core.Wireable — wire-typeclass for heterogeneous state.

  `Wireable α` asserts that values of type α correspond to a
  fixed bit-width hardware signal.  The class itself only
  carries the width; the per-slot encoding/decoding stays
  structural (we lean on the IR elaborator's existing Prod /
  BitVec / Bool / HWVector wire-translation rules rather than
  introducing a new toBits / fromBits round-trip).

  The companion type `HList` is defined as a right-nested Prod
  chain terminated by `Unit`, so any wire shape an HList takes
  reduces to a sequence of `Prod` constructors the elaborator
  already knows how to lower (`Signal.map Prod.fst` /
  `Signal.map Prod.snd` accessor recognition lives in
  `Sparkle/Compiler/Elab.lean`).

  This is the foundation for the v2 attempt at a state-monad
  DSL — the v1 PoC used `Vector τ n` for state and hit the wall
  that `Signal dom (Vector τ n)` has no wire-translation path.
  By reanchoring on a Prod chain we stay inside the elaborator's
  existing recognition.
-/

namespace Sparkle.Core

/-- Asserts that `α` has a known hardware bit-width.

    Instances are intentionally minimal — no `toBits`/`fromBits`.
    The IR elaborator recognises the structural shape of
    `α` (BitVec / Bool / Prod / HWVector) directly when wiring,
    so the typeclass only needs to expose the width for
    code that reasons about state size statically. -/
class Wireable (α : Type) where
  width : Nat

instance : Wireable Bool := ⟨1⟩
instance (n : Nat) : Wireable (BitVec n) := ⟨n⟩

/-- Right-nested heterogeneous product over a static type list.

    `HList [α, β, γ] = α × β × γ × Unit`.  Definitionally a Prod
    chain so `Prod.fst` / `Prod.snd` projections (which the IR
    elaborator already lowers to bit slices) reach individual
    slots without needing new wire rules. -/
@[reducible] def HList : List Type → Type
  | []      => Unit
  | α :: αs => α × HList αs

namespace HList

/-- Element-wise construction (the same shape `α × HList αs` of
    the inductive `HList (α :: αs)`, just sugared). -/
@[reducible] def cons {α : Type} {αs : List Type} (x : α) (xs : HList αs) : HList (α :: αs) := (x, xs)

@[reducible] def nil : HList [] := ()

/-- Head of a non-empty HList — definitionally `Prod.fst`. -/
@[reducible] def head {α : Type} {αs : List Type} (h : HList (α :: αs)) : α := h.1

/-- Tail of a non-empty HList — definitionally `Prod.snd`. -/
@[reducible] def tail {α : Type} {αs : List Type} (h : HList (α :: αs)) : HList αs := h.2

end HList

/-- Empty HList wires to a zero-width slot.  Matches the Prod
    chain's `Unit` terminator. -/
instance : Wireable Unit := ⟨0⟩

/-- Prod of two Wireables is Wireable.  Width is the sum, exactly
    what the elaborator's existing Prod wire rule does. -/
instance {α β : Type} [Wα : Wireable α] [Wβ : Wireable β] : Wireable (α × β) :=
  ⟨Wα.width + Wβ.width⟩

/-- `HListWireable αs` asserts that every element type in `αs`
    has a `Wireable` instance.  Used as a constraint on
    `runCircuit` so users can't accidentally place non-
    synthesisable types (e.g. `Option Nat`) into the register
    state list — the type check fires at the `runCircuit` call
    site, well before `#synthesizeVerilog` would.

    The class is intentionally empty: its presence is the
    assertion.  Instances are derived structurally on the list
    so any `αs` whose elements are individually `Wireable`
    automatically gets an instance.

    `Wireable (HList αs)` follows by induction over the Prod
    chain `α × HList αs`, using the existing
    `Wireable (α × β)` instance above. -/
class HListWireable (αs : List Type) : Type

instance : HListWireable [] := ⟨⟩
instance {α : Type} {αs : List Type} [Wireable α] [HListWireable αs] :
    HListWireable (α :: αs) := ⟨⟩

/-- `HList αs` is `Wireable` whenever every element is.
    Induction over the list. -/
instance : Wireable (HList []) := ⟨0⟩
instance {α : Type} {αs : List Type} [Wireable α] [Wireable (HList αs)] :
    Wireable (HList (α :: αs)) :=
  -- HList (α :: αs) reduces to `α × HList αs`, so we go through
  -- the existing `Wireable (α × β)` instance.
  inferInstanceAs (Wireable (α × HList αs))

end Sparkle.Core
