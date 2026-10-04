
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
  **C** shim into a `.so` and `dlopen`s it (see §8b.6 below
  for what actually happens under `load`),
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

`#sim` *also* writes a Sparkle `.sv` next to the JIT `.c`,
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
**same `jit_vtable` accessor** the JIT-emitted `.so` exports
(see §8b.6).  That means the resulting `.so` is loaded via
the *exact same* `JIT.load` FFI — no second binding layer to
maintain.

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

## 8b.6 What `load` actually does — the CSim vtable ABI

`counter8.Sim.load` is a fairly thick call.  Understanding what
happens inside is the difference between "the JIT works by magic"
and being able to write a driver for a new IP without falling into
a Signal-cache trap.

```
counter8.Sim.load
   │
   ├─ 1.  Read the JIT-generated .c on disk (emitted at build time by
   │      `#sim`, path e.g. `.lake/build/gen/sim/counter8_jit.c`).
   │
   ├─ 2.  JIT.compile:  cc -O2 -std=gnu11 -shared -fPIC \
   │                       -fvisibility=hidden -Wl,-rpath,<host-libc> \
   │                       -o <hash>.so counter8_jit.c
   │      (cached in .lake/build/jit_cache/, keyed on source hash +
   │       host libc path — see Sparkle/Core/JIT.lean).
   │
   ├─ 3.  dlopen(<hash>.so, RTLD_NOW).
   │
   ├─ 4.  dlsym for exactly ONE symbol: `jit_vtable`.  Everything
   │      else in the .so is `static` (internal linkage).
   │
   ├─ 5.  Call `jit_vtable()` — it returns a `const JitVTable*`
   │      containing function pointers for every operation
   │      (create / destroy / reset / eval / tick / eval_tick /
   │       set_input / get_output / get_wire / set_mem / get_mem /
   │       memset_word / snapshot / restore / ...).
   │
   └─ 6.  Copy the table into a `JITHandle` struct on the host
          side.  Every subsequent `Sim.step` / `Sim.read` / etc.
          dispatches through these function pointers.
```

Two design details worth calling out:

**One symbol per `.so`.**  Every JIT `.so` exports exactly
`jit_vtable` and nothing else (`nm -D <.so> | grep ' T '`
confirms it).  That's not cosmetic — it defends against a
glibc `dlopen` handle-collapse bug (issue #70) where two
`.so` files that share every exported symbol name silently
map to the same handle, and the second `.so`'s calls dispatch
into the first `.so`'s code.  By moving all per-method
dispatch behind a single `jit_vtable` accessor, we bypass
`dlsym`'s global-namespace lookup for the hot path.

**C, not C++.**  The CSim backend (post-PR #66) emits pure
C — `struct` instead of `class`, `T[N]` instead of
`std::array<T, N>`, `calloc`/`free` instead of `new`/`delete`.
`readelf -d <.so> | grep NEEDED` shows only `libc.so.6` — no
`libstdc++` dependency, no `_ZN...` mangling.  Same performance
as the old C++ backend on the hot path (within 8% on the RV32
SoC bench), significantly simpler ABI story.

## 8b.7 Real-world sim recipes

The counter above is intentionally trivial.  Two patterns
you'll want when driving a real IP:

### Byte-stream FSM sim (memcached ASCII server)

`IP/Net/MemcachedServer.lean` defines `memcachedServer` as an
`@[hardware_module]`, and `Tests/IP/Net/MemcachedServerJITTest.lean`
shows the CI gate driver.  The shape:

```text
-- Wrap the multi-output `ServerOut` (outByte + outValid) into a
-- single-Signal top so the elaborator's sub-module-instance
-- shortcut runs only ONE copy of the FSM.
@[hardware_module] def memcachedServerTop
    (inByte : Signal D (BitVec 8)) (inValid : Signal D Bool) :
    Signal D (BitVec 9) :=
  let out := memcachedServer inByte inValid
  let vBit : Signal D (BitVec 1) :=
    Signal.mux out.outValid (Signal.pure 1#1) (Signal.pure 0#1)
  (· ++ ·) <$> vBit <*> out.outByte

#sim memcachedServerTop

-- Driver: schedule two commands, sample outputs each cycle.
def main : IO Unit := do
  let sim ← memcachedServerTop.Sim.load
  Sim.reset sim
  let mut outBytes : List UInt8 := []
  for t in [0:160] do
    let (byte, valid) := stimAt t     -- stim = ByteSched → per-cycle byte
    Sim.step sim { inByte := byte, inValid := valid }
    let out ← Sim.read sim
    if (out.out.extractLsb' 8 1).toNat == 1 then
      outBytes := outBytes ++ [(out.out.extractLsb' 0 8).toNat.toUInt8]
  Sim.destroy sim
  -- outBytes now holds "STORED\r\nVALUE k 0 16\r\n…hello\r\nEND\r\n"
```

Two things to notice:

1. **The 9-bit trick** (`vBit ++ outByte`).  Pack `(outValid,
   outByte)` into a single scalar Signal so `#sim` produces a
   single JIT output slot.  We slice it back apart on the host
   side.  This avoids the elaborator's still-fragile multi-output
   struct-projection path for IPs where a single scalar view is
   enough (see also `IP/Net/UsbWebServer.lean`).
2. **`Sim.step` + `Sim.read` per cycle** (not `Sim.run`).
   `Sim.step` drives per-cycle inputs (`stimAt t`); `Sim.read`
   pulls the output.  This is the same pattern the CI-gate
   `memcached-server-jit-test` uses.

### Multi-`.so` composition (h264 pipeline)

The h264 bitstream test loads two independent JIT `.so` files
(the encoder pipeline and the CAVLC synth engine).  Before
PR #66 this used to SIGSEGV: glibc's `dlopen` collapsed the
second `.so`'s handle onto the first (identical `extern "C"`
symbol set → identical `dlsym` dispatch table).

With the vtable ABI, each `.so`'s `jit_vtable` accessor is
resolved once at load and every subsequent call dispatches
through the table entry.  `dlopen` can still hand back the
same OS-level handle for both (it does on some glibc
versions), but the caller doesn't care — every function
pointer is baked into the private per-`.so` `JitVTable`.

```text
let cavlcSim   ← cavlcSynthModule.Sim.load     -- .so #1
let encoderSim ← encoderPipeline.Sim.load       -- .so #2

-- Both drive independently; no cross-.so aliasing.
for t in [:200] do
  Sim.step encoderSim { pixel := frame[t]! }
  let enc ← Sim.read encoderSim
  Sim.step cavlcSim { level := enc.level }
  ...
```

## 8b.8 Choosing between them

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

## 8b.9 What `#sim` actually emits (for the curious)

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

- `.lake/build/gen/sim/counter8_jit.c` — the JIT C shim.
- `.lake/build/gen/sim/counter8.sv`     — the Verilog source
  Verilator builds against.

You usually don't read either; they're regenerated on every
`#sim` invocation.

## 8b.10 Sparkle sim vs a Verilog testbench

The three backends above all differ from a hand-written Verilog
testbench in the same way: in Sparkle a simulation is **evaluating a
pure function**, not running procedural timed code. There is no clock to
wiggle, no `initial` block, and no separate `_tb` module — you ask the
`Signal` for its value at a cycle. This table is the simulation
counterpart of the syntax reference in Ch 5 §5.6:

| Task | Verilog testbench | Sparkle |
|---|---|---|
| clock | `always #5 clk = ~clk;` — generate a wiggling clock | none — the cycle index `t : Nat` **is** the clock; the domain carries it |
| advance one cycle | `@(posedge clk);` | evaluate at `t + 1` / `sim.step` then `sim.read` |
| drive an input | `a = 8'd5; #10;` (procedural, timed) | an input is a `Signal` = a function of cycle: `Signal.pure 5#8`, or `⟨fun t => …⟩` for a waveform |
| read an output | `$display("%0d", out);` | `out.val t` — a pure value |
| run N cycles | `initial begin repeat (N) @(posedge clk); … $finish; end` | `Signal.sample out N : List (BitVec …)` |
| reset | drive `rst` high for a few cycles, procedurally | the reset value is baked into `Signal.reg init` — nothing to drive |
| the testbench itself | a separate `_tb.v` with `initial` / `$finish` | none — the "testbench" is a Lean function, `#eval`, or `#sim`; you call the design directly |
| check a result | `if (out !== exp) $error(…);` at run time | a Lean `theorem` proven once for **all** cycles (Ch 6/7), or `#eval` / `decide` on `.val` |
| unknown / hi-Z | 4-state: `x` (unknown), `z` (tri-state) | 2-state: every wire is a definite `BitVec` — there is no `x` / `z` |
| races / ordering | `always` blocks can race; `blocking =` vs `non-blocking <=` matters | none — a `Signal` is a pure function of `t`; evaluation order cannot change the result |
| speed knob | compile with Verilator (C++) for long runs | `#sim` JIT-C (§8b.3), or Verilator via `loadVerilator` (§8b.4) — same `Sim` interface |

Three consequences worth internalising:

- **No testbench, no clock.** You never write stimulus procedurally over
  time; you build input `Signal`s and read output `Signal`s. "Cycle `t`"
  is an argument, not a wall-clock event.
- **Deterministic and 2-state by construction.** Because a `Signal` is a
  `Nat → value` function, a Sparkle simulation has no `x`/`z` and no
  race conditions — the two classic sources of "passes in sim, fails on
  silicon" simply cannot arise.
- **Assertions become theorems.** A Verilog testbench checks a finite set
  of traces at run time; a Sparkle property (`∀ t, …`) is proven once and
  covers every trace (Ch 6/7). `#sim` is for when you want to *watch*
  numbers go by, not to establish correctness.

end Notebooks.Ch08b
