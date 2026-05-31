
# Chapter 3 — Sequential Circuits

Combinational logic (Ch 2) reacts instantly to its inputs.
**Sequential** logic remembers state across clock edges via
flip-flops — registers in Sparkle's vocabulary.  Almost every
non-trivial design needs them: counters, FSMs, pipelines, FIFOs.

Sparkle gives you registers two ways:

1. **`circuit do`** — the imperative-feeling form we
   recommend for everyday work.  `let x ← Signal.reg init`
   declares a register; `x <~ rhs` says "the register's
   next-cycle value is `rhs`".  `return x` is the module's
   output.

2. **`Signal.loop` + `Signal.register`** — the dataflow form
   you'll see in IP code.  We show it once for comparison; the
   course uses `circuit do` for everything that follows.

Both forms produce the same Verilog.

```lean
import Sparkle
import Sparkle.Compiler.Elab
import Display

open Sparkle.Core.Domain
open Sparkle.Core.Signal

namespace Notebooks.Ch03

```
## 3.0 Anatomy of one register — four views, one circuit

Before we build anything, let's look at a single 1-bit register
from four angles at once:

1. **Sparkle source** — what you write
2. **Generated SystemVerilog** — what the synthesiser emits
3. **Block diagram** — the clock and data edges drawn out
4. **Waveform** — D (input) and Q (output) clocked on the
   rising edge

All four describe the same circuit: a D-flip-flop that
captures `d` on every rising edge of `clk` and presents the
captured value on `q`.

### View 1 — Sparkle source

```lean
def dff {dom : DomainConfig}
    (d : Signal dom Bool) : Signal dom Bool :=
  circuit do
    let q ← Signal.reg false
    q <~ d
    return q

```

`Signal.reg false` creates a 1-bit register initialised to
`false`.  `q <~ d` says "next cycle, `q` becomes whatever `d`
is this cycle".  `return q` exposes the register's *current*
value as the module's output.

### View 2 — Generated SystemVerilog

```lean
#synthesizeVerilog dff

```

You'll see something close to:

```text
module Notebooks_Ch03_dff (
    input  logic clk,
    input  logic rst,
    input  logic _gen_d,
    output logic out
);
    logic _gen_state_1;
    always_ff @(posedge clk) begin
        if (rst)  _gen_state_1 <= 1'b0;
        else      _gen_state_1 <= _gen_d;
    end
    assign out = _gen_state_1;
endmodule
```

`always_ff @(posedge clk)` says "sample on the rising edge of
`clk`".  When `rst` is high at that edge, the register clears
to 0; otherwise it captures `_gen_d`.  This is **synchronous
reset**, the Sparkle default — `defaultDomain.resetKind = .synchronous`,
and the `_gen_state_1` line is the register itself; the
`assign out = _gen_state_1` line corresponds to our `return q`.

If you want **asynchronous** reset (clear the moment `rst`
rises, independent of the clock), declare a custom domain:

```text
def asyncDom : DomainConfig :=
  { period := 10000, activeEdge := .rising,
    resetKind := .asynchronous }
```

and write the dff against it.  The same Sparkle source then
emits `always_ff @(posedge clk or posedge rst) …` instead.
Ch 10 §10.3 covers the trade-off.

### View 3 — Block diagram (clock + data)

For a one-off teaching figure you can hand-build the diagram
node by node — pick a `NodeKind` per box, lay out the columns
yourself, draw the edges:

```lean
def dffDiagram : Sparkle.Display.Diagram.Diagram := {
  nodes := [
    { id := "clk", label := "clk", kind := .clk,  col := 0, row := 1 },
    { id := "d",   label := "d",   kind := .port, col := 0, row := 0 },
    { id := "ff",  label := "DFF", kind := .reg,  col := 1, row := 0 },
    { id := "q",   label := "q",   kind := .port, col := 2, row := 0 } ],
  edges := [
    { src := "d",   dst := "ff" },
    { src := "clk", dst := "ff", kind := .clock },
    { src := "ff",  dst := "q"  } ]
}

#eval Sparkle.Display.Diagram.blockDiagram dffDiagram

```

Two kinds of edge: a *data* edge (`d → DFF`, solid arrow) and a
*clock* edge (`clk → DFF`, dashed orange with a triangle pin at
the destination).  Beginners often miss this distinction in
textbooks — the clock is itself just another wire, but it
triggers state changes rather than carrying values.

#### Auto-generated from the design

Hand-built diagrams are useful for textbook figures, but for an
actual Sparkle design we don't want to maintain a parallel
description by hand: the diagram should *follow* the source.

`#showDiagram <ident>` does that in one line — it runs the same
synthesiser as `#synthesizeVerilog`, lifts the resulting
`IR.AST.Module` into a `Diagram` (every `Stmt.register` becomes
a `reg` box, every `Stmt.assign` whose RHS is a primitive
becomes the matching gate, clock / reset wires get the `clock`
edge style), and emits the inline SVG.

```lean
-- `dff` is the same definition we introduced at the top of the
-- chapter; `#showDiagram` runs the synthesiser and renders the
-- resulting `IR.AST.Module` as SVG in one step.
#showDiagram dff

```

The auto-generated picture has the same shape as the hand-built
one — `d` and `clk` on the left, `q` on the right — but it's
regenerated every time the design changes.  Edit the body of
`dff` (e.g. add an enable, change the reset value), re-run the
cell, and the new nodes and edges show up without any extra
work.

For hierarchical designs (multiple `@[hardware_module]`
children) use `#showDesign <ident>` instead — it draws the
parent and every transitive child stacked vertically in the
cell.  A pure `#showDiagram` only shows the top module.

### View 4 — Waveform

A short trace showing `d` flipping freely and `q` only
following on the rising edge of `clk`:

```lean
-- 32 ticks; one full clock period = 4 ticks (high-low-high-low).
def CLKP : Nat := 4

-- Synthetic input pattern: arbitrary edges.
def dPat : List Bool :=
  [false, false, true,  true,  true,  false, false, true,
   true,  false, false, true,  true,  true,  true,  false,
   false, false, true,  false, true,  true,  false, false,
   true,  true,  true,  true,  false, false, false, true]

def clkSample (t : Nat) : Bool := (t % CLKP) < (CLKP / 2)
def dSample   (t : Nat) : Bool := (dPat[t]?).getD false

-- Q is D delayed until the next rising edge of clk.
-- Rising edge happens at t such that clkSample (t-1) = false
-- and clkSample t = true, i.e. t % CLKP == 0 for t ≥ 1.
def qSample : Nat → Bool
  | 0       => false
  | t + 1   =>
    if (t + 1) % CLKP == 0 then dSample t   -- captured at this rising edge
    else qSample t

def clkLane : List Bool := (List.range 32).map clkSample
def dLane   : List Bool := (List.range 32).map dSample
def qLane   : List Bool := (List.range 32).map qSample

#eval Display.boolWave
  [("clk", clkLane), ("d", dLane), ("q", qLane)] 28 30

```

Read the SVG bottom-up: every time `clk` rises, look at `d`
*just before* the edge — that's the value that appears on `q`
*just after*.  Between edges, `d` can wiggle as much as it
likes; `q` stays put.

This is the whole game.  The rest of the chapter is just
about wiring up registers in interesting patterns.

## 3.1 An 8-bit counter (`circuit do` form)

The simplest sequential circuit: a register that increments
itself every cycle.  Read it top-down — that's the point.

```lean
def counter8 {dom : DomainConfig} : Signal dom (BitVec 8) :=
  circuit do
    let count ← Signal.reg 0#8
    count <~ count + 1#8
    return count

```
### Same circuit, the dataflow form

Just for comparison — `Signal.loop` takes a function whose
argument is the previous-cycle output (a "feedback wire") and
whose body returns the new value.  We feed `count + 1#8`
into a `Signal.register` initialised to 0.  This is what
`circuit do` desugars to under the hood.

```lean
def counter8' {dom : DomainConfig} : Signal dom (BitVec 8) :=
  Signal.loop fun count =>
    Signal.register 0#8 (count + 1#8)
```

You'll see this style in real IP code (look at `IP/RV32/SoC.lean`).
For learning, the `circuit do` form is what we'll use.

## 3.2 Counter with enable

A common pattern: only count when `en` is high.  We build the
next-state expression with `Signal.mux` and pipe it into the
register's `<~`.

Note: `if en then count + 1#8 else count` would not synthesise
because `en : Signal dom Bool` and `if` doesn't accept Signal
conditions — see Ch 2 §2.3.

```lean
def counterEn {dom : DomainConfig}
    (en : Signal dom Bool) : Signal dom (BitVec 8) :=
  circuit do
    let count ← Signal.reg 0#8
    let next := Signal.mux en (count + 1#8) count;
    count <~ next
    return count

```
## 3.3 Shift register

Three flip-flops chained in series.  An input bit takes 3
cycles to reach the output.  This is the canonical "deepen the
pipeline" operation.

```lean
def shift3 {dom : DomainConfig}
    (input : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  circuit do
    let s0 ← Signal.reg 0#8
    let s1 ← Signal.reg 0#8
    let s2 ← Signal.reg 0#8
    s0 <~ input
    s1 <~ s0
    s2 <~ s1
    return s2

```
## 3.4 A 3-state FSM (idle / run / done)

States are encoded as `BitVec 2` constants.  Transitions are
driven by an input strobe `start`.  The `Signal.mux` chain
computes the next state; `count` separately measures how long
we've been in `run`.

```text
     start                count == 255
  idle ───→ run ────────→ done ───┐
   ↑                              │
   └──────────────────────────────┘
```

```lean
-- State encoding: 00 = idle, 01 = run, 10 = done.
def IDLE : BitVec 2 := 0#2
def RUN  : BitVec 2 := 1#2
def DONE : BitVec 2 := 2#2

def fsm {dom : DomainConfig}
    (start : Signal dom Bool) : Signal dom (BitVec 2) :=
  circuit do
    let state ← Signal.reg IDLE
    let count ← Signal.reg 0#8
    let isIdle := state === IDLE;
    let isRun  := state === RUN;
    let isDone := state === DONE;
    -- Next-state logic: idle → run on `start`; run → done when
    -- count saturates; done loops back to idle for the next
    -- launch.
    let nextState :=
      Signal.mux (isIdle &&& start) RUN
        (Signal.mux (isRun &&& (count === 255#8)) DONE
          (Signal.mux isDone IDLE state));
    state <~ nextState
    -- Count up while in `run`, otherwise reset to 0.
    count <~ Signal.mux isRun (count + 1#8) 0#8
    return state

```
## 3.5 Verilog generation

Each circuit above synthesises to clean SystemVerilog.  Watch
the `always_ff @(posedge clk)` blocks — that's where each
`<~` lands.

```lean
#synthesizeVerilog counter8

```
```lean
#synthesizeVerilog counterEn

```
```lean
#synthesizeVerilog shift3

```
```lean
#synthesizeVerilog fsm

```
## 3.5b Visualising the counter as a waveform

`Display.waveform` from xeus-lean (with our shim as the offline
fallback) renders a list of `Nat` values as inline SVG.  We
sample `counter8` for 16 ticks and pipe it in.

```lean
-- Sample the counter as a plain `Nat → Nat`.  Sparkle's
-- `Signal.val` evaluator uses a JIT-linked C helper, so the
-- next cell only really runs in xeus-lean — under headless
-- `lake build` we just typecheck the shape.
def counter8Trace : List Nat :=
  let rec sample (count : BitVec 8) (n : Nat) (acc : List Nat) : List Nat :=
    match n with
    | 0     => acc.reverse
    | n + 1 => sample (count + 1#8) n (count.toNat :: acc)
  sample 0#8 16 []
```

```lean
#eval Display.waveform "cnt[7:0]" counter8Trace 8 28 60
```

In the kernel this renders as a stair-step trace; in `lake
build` the cell typechecks but emits a MIME marker on stdout
(harmless).

## 3.5c A real protocol — I²C master, two lanes on one trace

Here we put both *clock* and *data* on the same plot and watch a
small I²C master write the 7-bit address `0x21` (with R/W = 0,
so the byte on the bus is `0x42`).  Each bit period is `TPB = 8`
simulation ticks; SCL toggles at the half-period.

| bit period | what's happening                              |
|------------|-----------------------------------------------|
| 0          | START — SDA falls while SCL is high           |
| 1..8       | data bits, MSB first (`0x42 = 0100_0010`)     |
| 9          | ACK — slave pulls SDA low                     |
| 10         | STOP — SDA rises while SCL is high            |

We build SCL and SDA as ordinary `Nat → Bool` functions (a
plain Lean view of what the design's signals would compute) and
hand them to `Display.boolWave`.

```lean
def TPH : Nat := 4
def TPB : Nat := 2 * TPH
def addrByte : BitVec 8 := 0x42#8

def sclSample (t : Nat) : Bool :=
  let bit := t / TPB
  let off := t % TPB
  if bit == 0 then true                            -- START framing
  else if bit ≥ 1 ∧ bit ≤ 9 then off ≥ TPH         -- data + ACK clocking
  else true                                         -- STOP framing

def sdaSample (t : Nat) : Bool :=
  let bit := t / TPB
  let off := t % TPB
  if bit == 0 then off < TPH                       -- START: high then low
  else if bit ≥ 1 ∧ bit ≤ 8 then
    addrByte.getLsbD (7 - (bit - 1))               -- MSB first
  else if bit == 9 then false                      -- slave ACK
  else if bit == 10 then off < TPH                 -- STOP: low then high
  else false

def sclSamples : List Bool := (List.range 88).map sclSample
def sdaSamples : List Bool := (List.range 88).map sdaSample
```

```lean
#eval Display.boolWave [("SCL", sclSamples), ("SDA", sdaSamples)] 28 30
```

## 3.5d Persisting a trace — `wdb` waveform database

`Display.waveform` and `Display.boolWave` render an *inline* SVG
into the cell — convenient for short traces, but at a few
thousand transitions per signal the SVG payload starts to bloat
the notebook file (each notebook cell is checked into git, so
its size matters).  For longer simulations, write the trace to a
**`.wdb` file** (Sparkle's compact waveform database) and let
the kernel render it interactively.

```text
                         in-memory             on disk
   List Bool ──Display.writeWdb──▶  signal.wdb (zstd-compressed
                                                 transition lists)

   signal.wdb ──Display.waveformFromWdb──▶  interactive viewer
                                            (zoom / pan / lane toggle)
```

The `wdb` format stores per-signal transition lists (timestamp +
new value) instead of one sample per tick, then zstd-compresses
the whole thing.  A 1 G-tick trace with O(M) transitions
typically lands at a few MB on disk — far below the ~MB raw
sample budget.

Run the next cell *inside JupyterLab* — it shells out to the
kernel's real `writeWdb` which zstd-compresses the trace and
drops it on disk.  Plain `lake build` only runs the offline
shim (no-op); the saved file would be empty.  The lane data is
the same shape as `boolWave`'s, so the I²C trace from §3.5c
can be re-used directly.

```lean
#eval Display.writeWdb "/tmp/i2c.wdb"
        [{ name := "SCL", sample := fun t => sclSample t },
         { name := "SDA", sample := fun t => sdaSample t }]
        /- totalTicks -/ 88
```

Open the saved `.wdb` in a fresh interactive viewer:

```lean
#eval Display.waveformFromWdb "i2c-session" "/tmp/i2c.wdb"
```

The viewer JS opens a Jupyter `comm` channel back to the kernel
(target name `xlean`, session id from the `#eval` argument).
Scroll-wheel zooms; horizontal-drag pans; the level-of-detail
adapts so the displayed bit count never exceeds the canvas pixel
width.  The lane list can be edited at runtime via
`Display.WaveformSession.{addLane, removeLane}` — useful when a
debugging session reveals you want to look at one more signal
without re-running the whole simulation.

> **Note.** Today `Display.writeWdb` and `waveformFromWdb` live
> in xeus-lean; the `wdb` codec is being migrated to
> `Sparkle.Display.Wdb` (see `docs/Display_Migration_Plan.md`)
> so a Sparkle-only `lake build` will eventually be able to
> produce / consume the same files without the kernel.
>
> **Build note.** These cells print a `(shim — open in xeus-lean
> for the full viewer)` line when run via plain `lake build` /
> `lake env lean` — that's the offline fallback in
> `docs/tutorial/Display.lean`.  Inside the tutorial Docker
> image the kernel resolves `Display` to xeus-lean's real
> implementation and the cells render properly.

## 3.6 Theorem — the counter wraps at 256

An 8-bit register that increments every cycle wraps to zero
after 256 ticks.  We can prove this *behaviourally* on the
recurrence — no need to simulate.

```lean
-- Behavioural recurrence: count_(n+1) = count_n + 1, all in
-- BitVec 8 (so wrap is automatic).
def behaviouralCount : Nat → BitVec 8
  | 0     => 0#8
  | n + 1 => behaviouralCount n + 1#8

-- After 256 cycles the value is 0 again.
example : behaviouralCount 256 = 0#8 := by native_decide

-- After 255 cycles it's at 0xFF.
example : behaviouralCount 255 = 0xFF#8 := by native_decide

```
## 3.7 Exercise — traffic-light FSM

Build an FSM with three states (`green`, `yellow`, `red`), a
timer that holds each state for a fixed number of cycles, and
an output `lights : Signal dom (BitVec 3)` (one bit per
light).

Suggested durations: green = 8 cycles, yellow = 2, red = 6.
One-hot encode the output: `green → 100`, `yellow → 010`,
`red → 001`.

Stub below; reference solution in `Solutions/Ch03.lean`.

```lean
-- TODO: implement `trafficLight` here.
-- def trafficLight {dom : DomainConfig} : Signal dom (BitVec 3) :=
--   sorry

end Notebooks.Ch03
```
