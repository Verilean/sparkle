
# Chapter 8b — Three ways to simulate, one interface

We've been writing Sparkle circuits and proving things about
them, but we haven't really *run* one yet.  This chapter walks
through three runtime simulation paths.

| Path        | Backend                  | When to use                                           |
|-------------|--------------------------|-------------------------------------------------------|
| Pure-Lean   | `Signal.sample`          | small circuits, < 10 K cycles, no toolchain needed    |
| Sparkle JIT | `#sim` → `JIT.evalTick`  | medium designs, ≥ 100 K cycles, no Verilog dep        |
| Verilator   | `verilator --cc --build` | golden reference, very long runs, industry-standard   |

The headline: **all three speak the same `Sim` interface**, so
once a simulator is loaded, the per-cycle loop is identical
across backends.  The only thing that changes between paths is
the constructor (`load` vs `loadVerilator` vs
`PureLean.of`).

For the running example we use the Ch 3 counter (`counter8`)
— the same recipes scale to the ALU, FSM, or a full SoC.

```lean
import Sparkle
import Sparkle.Compiler.Elab
import Display

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Core.Sim

namespace Notebooks.Ch08b

def counter8 {dom : DomainConfig} : Signal dom (BitVec 8) :=
  circuit do
    let count ← Signal.reg 0#8
    count <~ count + 1#8
    return count

```

## 8b.1 The unified `Sim` interface

`Sparkle.Core.Sim.Sim` is a Lean typeclass with five members:

```text
class Sim (S : Type) (I O : outParam Type) where
  reset   : S → IO Unit
  step    : S → I → IO Unit
  read    : S → IO O
  destroy : S → IO Unit
```

(`load` is *not* part of the class — each backend takes
different arguments at construction time.  See §8b.5 for the
shape per backend.)

Two helpers, `Sim.run` and `Sim.trace`, layer over the four
methods so you don't have to hand-roll the `for` loop:

```text
-- Run for `n` cycles with the same input each cycle:
def Sim.run    [Sim S I O] : S → Nat → I       → IO (List O)
-- Run with one input per cycle (different drives each time):
def Sim.trace  [Sim S I O] : S → List I        → IO (List O)
```

The whole point of the typeclass is that **one driver function
works against any backend**:

```lean
def driveAny {S I O : Type} [Sim S I O] [Inhabited I]
    (sim : S) (n : Nat) : IO (List O) := do
  Sim.reset sim
  let trace ← Sim.run sim n default
  Sim.destroy sim
  pure trace

```

The next three sections each construct one of the three
backends; the call-site (`driveAny` plus a print) is the same
in all three.

## 8b.2 Pure-Lean — `Sparkle.Core.Sim.PureLean.of`

The simplest path.  Pure-Lean evaluates the signal in the Lean
interpreter, no codegen and no toolchain.

```text
#eval do
  let sim ← Sparkle.Core.Sim.PureLean.of
              (counter8 (dom := defaultDomain))
  let trace ← driveAny sim 10
  IO.println (trace.map (·.toNat))
-- expected: [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
```

(The cell is `text` because pure-Lean simulation depends on
the JIT-linked C helper `evalSignalAt` that's only resolved at
xeus-lean / `lake env lean --run` time, not under headless
`lake build`.)

`I = Unit` here — pure-Lean has no per-cycle input injection.
`O` is whatever the underlying signal produces (`BitVec 8`
above).

**Pros** — zero setup, stays inside Lean.  Good for tutorials,
smoke tests, tiny property checks.

**Cons** — slow (~5 K cycles/sec) and no input drives.  Move
to the JIT as soon as the design has more than a few registers.

## 8b.3 Sparkle JIT — `#sim counter8` then `counter8.Sim.load`

The `#sim` macro takes a Signal definition and synthesises:

- a typed `SimInput` / `SimOutput` record for the design's
  ports,
- a `Simulator` wrapping a `JITHandle`,
- a `load : IO Simulator` that compiles a freshly-generated
  C++ shim into a `.so` and `dlopen`s it,
- a `Sim` instance gluing it all to the unified interface.

```text
#sim counter8

#eval do
  let sim ← counter8.Sim.load
  let trace ← driveAny sim 10
  IO.println (trace.map (·.out.toNat))
-- expected: [0, 1, 2, …, 9]
```

`I` is `counter8.Sim.SimInput` (no fields, since `counter8`
has no ports beyond `clk`/`rst`); `O` is
`counter8.Sim.SimOutput` with one field `out : BitVec 8`.
For a design with inputs, you'd pass `{ enable := true#1, … }`
in place of `default`.

The JIT runs at ~1 M cycles/sec on a laptop — ~200× faster
than pure-Lean.

## 8b.4 Verilator — `counter8.Sim.loadVerilator`

`#sim` *also* writes a Sparkle `.sv` next to the JIT `.cpp`,
and emits a second loader:

```text
#eval do
  let sim ← counter8.Sim.loadVerilator
  let getOuts ← Sim.read sim    -- read-before-step is fine; reset just ran
  let v ← getOuts 0
  Sim.destroy sim
  IO.println s!"verilator: out (cycle 0) = {v}"
```

Behind the scenes, `loadVerilator` runs

```text
verilator --cc --build --top-module Notebooks_Ch08b_counter8 \
  -CFLAGS '-O2 -fPIC' -LDFLAGS '-shared -o V<top>.so' \
  --Mdir /tmp/sparkle_verilator \
  .lake/build/gen/sim/counter8.sv \
  /tmp/sparkle_verilator/sparkle_verilator_tb.cpp
```

The `tb.cpp` is auto-generated by Sparkle to expose the
**same C ABI** the JIT uses (`jit_create / jit_eval_tick /
jit_set_input / jit_get_output`).  That means the resulting
`.so` is loaded via the *exact same* `JIT.load` FFI — no
second binding layer to maintain.

The trade-off: Verilator's I and O on this typeclass instance
are raw `(idx, value)` lists rather than typed records, because
the typed wrappers are owned by `#sim` and currently routed
through the JIT-shaped `Simulator`.  For most workloads you
either drive Verilator with one constant input or write a
small adapter; the typed-record version is on the roadmap.

```text
-- Same loop, raw I/O.  `[]` = "no input changes this cycle".
#eval do
  let sim ← counter8.Sim.loadVerilator
  Sim.reset sim
  for i in [:10] do
    Sim.step sim []
    let getOuts ← Sim.read sim
    let v ← getOuts 0
    IO.println s!"cycle {i}: out = {v}"
  Sim.destroy sim
```

Verilator is the **golden reference**: if Sparkle's JIT and
Verilator disagree on a cycle, the JIT is wrong.  CI uses this
property in `Sparkle.Verification.CoSim`.

## 8b.5 Side-by-side — same loop, different loader

```text
-- Pure-Lean
#eval do
  let sim ← Sparkle.Core.Sim.PureLean.of
              (counter8 (dom := defaultDomain))
  IO.println (← driveAny sim 10).length

-- JIT
#eval do
  let sim ← counter8.Sim.load
  IO.println (← driveAny sim 10).length

-- Verilator
#eval do
  let sim ← counter8.Sim.loadVerilator
  IO.println (← driveAny sim 10).length
```

`driveAny` is *one* function from §8b.1.  Each `#eval` differs
by exactly the loader call.

## 8b.6 Choosing between them

Rules of thumb:

- Writing a new circuit?  **Pure-Lean** for the first 10
  cycles, then **JIT** as soon as the design has more than a
  few registers.
- Long-running stress test (firmware boot, video decode)?
  **JIT** (10⁶+ cycles/sec) — fall back to **Verilator** only
  if you suspect a Sparkle codegen bug.
- Writing CI tests for IP that has to match a published
  reference?  **Verilator** — that's what other tools agree
  with.
- Need waveforms for a deep debug session?  **Verilator +
  GTKWave** (cf. Ch 8 §8.5) or **JIT + `Display.writeWdb`**
  (cf. Ch 8 §8.5b).

The bedrock take-away: thanks to the unified `Sim` interface
you can write the simulation loop *once* and switch backends
by changing one word.  Use the cheapest path that gives you
the confidence you need.

## 8b.7 What `#sim` actually emits (for the curious)

`#sim counter8` (paraphrased) produces:

```text
namespace counter8.Sim
  structure SimInput  where ...
  structure SimOutput where out : BitVec 8
  structure Simulator where handle : JITHandle

  def Simulator.step    : Simulator → SimInput → IO Unit
  def Simulator.read    : Simulator → IO SimOutput
  def Simulator.reset   : Simulator → IO Unit
  def Simulator.destroy : Simulator → IO Unit
  def load              : IO Simulator
  def loadVerilator     : IO Sparkle.Core.Sim.Verilator.Simulator

  -- Glues the wrapper to the unified interface (§8b.1).
  instance : Sparkle.Core.Sim.Sim Simulator SimInput SimOutput := …
end counter8.Sim
```

Plus two side-effects on disk:

- `.lake/build/gen/sim/counter8_jit.cpp` — the JIT C++ shim.
- `.lake/build/gen/sim/counter8.sv`     — the Verilog source
  Verilator builds against.

You usually don't read either; they're regenerated on every
`#sim` invocation.

end Notebooks.Ch08b
