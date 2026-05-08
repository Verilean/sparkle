/-
  SimPureLean — pure-Lean backend for the unified `Sim` typeclass.

  Wraps a `Signal dom α` value as a `Sim` instance whose state is just
  an `IORef Nat` (the current cycle).  `step` advances the counter,
  `read` evaluates the signal at that cycle via `Signal.val`.

  This backend is intentionally minimal:

  - No support for runtime input injection.  Inputs in pure-Lean are
    typically baked into the `Signal` itself before `Sim.PureLean.of`
    is called (e.g. by composing with `Signal.lift` over a
    `Nat → α` driver).  The instance therefore parametrises `I`
    over `Unit` and ignores its argument.
  - `read` produces values of type `α`, the same type the underlying
    `Signal` carries.  No `SimOutput` record translation — pure-Lean
    is for tutorial-scale ad-hoc inspection, not typed I/O parity.

  For typed I/O records and 1 M cycles/sec, use the `#sim`-generated
  JIT wrapper.
-/
import Sparkle.Core.Domain
import Sparkle.Core.Signal
import Sparkle.Core.Sim

namespace Sparkle.Core.Sim.PureLean

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-- Pure-Lean simulator state: a closure over the signal and a
    mutable cycle counter.  `t` is the next cycle to read. -/
structure Simulator (α : Type) where
  /-- Cycle to evaluate on the next `read`. -/
  t : IO.Ref Nat
  /-- Closure that, given a cycle index, returns the signal value. -/
  evalAt : Nat → α

/-- Construct a pure-Lean simulator from a Signal value.  The
    returned simulator is positioned at cycle 0 — call `Sim.reset`
    before reading if you've already stepped through it. -/
def of {dom : DomainConfig} {α : Type} (s : Signal dom α) :
    IO (Simulator α) := do
  let t ← IO.mkRef 0
  pure { t := t, evalAt := s.val }

instance {α : Type} : Sparkle.Core.Sim.Sim (Simulator α) Unit α where
  reset sim := sim.t.set 0
  step sim _ := sim.t.modify (· + 1)
  read sim := do
    let i ← sim.t.get
    pure (sim.evalAt i)
  destroy _ := pure ()

end Sparkle.Core.Sim.PureLean
