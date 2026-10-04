/-
  Sim — unified simulation interface

  Sparkle exposes three runtime simulation backends:

    1. Pure-Lean (`Signal.sample` / `Signal.val`) — no toolchain,
       slow, useful for tutorials and tiny tests.
    2. JIT (`#sim` macro → CppSim → dlopen) — typed I/O records,
       ~1 M cycles/sec.
    3. Verilator (`writeVerilogFile` → `verilator --cc --build`)
       — golden reference, multi-step shell pipeline.

  This module unifies all three behind one typeclass:

      class Sim (S : Type) (I O : outParam Type) where
        reset   : S → IO Unit
        step    : S → I → IO Unit
        read    : S → IO O
        destroy : S → IO Unit

  The associated `load` constructor is *not* part of the class —
  each backend takes different arguments at construction time
  (a `Signal` for pure-Lean, a generated `.cpp` path for JIT,
  a generated `.sv` path for Verilator).  The typeclass covers
  the shared *runtime* loop: reset → step+read repeatedly →
  destroy.

  The existing `#sim`-generated wrappers (`Foo.Sim.Simulator`
  with method names `step` / `read` / `reset` / `destroy`)
  satisfy this signature structurally; one `instance` line per
  design opts the wrapper into the typeclass.  No regenerated
  wrappers, no breaking changes.
-/
namespace Sparkle.Core.Sim

/-- The unified simulation interface.

    `S` is the per-design simulator state (e.g. `Foo.Sim.Simulator`).
    `I` is the typed input record, `O` the output record.  Both are
    `outParam`s so writing `sim.step inp` lets Lean infer them.

    All four methods are `IO`-monadic; backends that don't need
    to run effects (pure-Lean) still wrap their work in `IO` so
    the call-site signature is identical across backends. -/
class Sim (S : Type) (I O : outParam Type) where
  /-- Restore the simulator to its initial state (cycle 0,
      registers at their declared `init` values). -/
  reset : S → IO Unit
  /-- Drive the inputs and advance one clock cycle. -/
  step : S → I → IO Unit
  /-- Read the current outputs. -/
  read : S → IO O
  /-- Release any resources (close the dlopen handle, free
      Verilator obj_dir, ...).  Implementations should be
      idempotent. -/
  destroy : S → IO Unit

namespace Sim

variable {S I O : Type} [Sim S I O]

/-- Run `n` cycles, returning the per-cycle output trace.
    Convenience wrapper over `step` + `read`; useful for
    chapter-scale demos where you don't want to hand-roll a
    `for` loop. -/
def trace (sim : S) (inputs : List I) : IO (List O) := do
  let mut acc : Array O := #[]
  for i in inputs do
    Sim.step sim i
    let o ← Sim.read sim
    acc := acc.push o
  return acc.toList

/-- Run `n` cycles with a constant input.  Handy when the
    input is "no inputs" (a `SimInput` with no fields), since
    callers can write `sim.run 100 {}`. -/
def run (sim : S) (n : Nat) (i : I) : IO (List O) :=
  trace sim (List.replicate n i)

end Sim

end Sparkle.Core.Sim
