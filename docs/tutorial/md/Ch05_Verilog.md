
# Chapter 5 — Verilog Generation

Up to here we've been using `#synthesizeVerilog` as a smoke
test: did the design synthesise without error?  This chapter
looks at the actual output — what Lean → SystemVerilog produces
— so you can read it, debug it, and hand it to downstream
tools.

```lean
import Sparkle
import Sparkle.Compiler.Elab
import Display
import Tools.SVParser
import Tools.SVParser.Macro
import Tools.SVParser.SimMacro

open Sparkle.Core.Domain
open Sparkle.Core.Signal

namespace Notebooks.Ch05

```
## 5.1 The smallest possible module

An identity wire, just to see the module skeleton.

```lean
def passthrough {dom : DomainConfig}
    (input : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  input

```
```lean
#synthesizeVerilog passthrough

```
The output is a SystemVerilog module with one input port,
one output port, and a single `assign` connecting them.
Unfussy — exactly what you'd write by hand.

## 5.2 A combinational ALU op (revisited from Ch 4)

The interesting parts of the generated Verilog:

- **Module name** — comes from the Lean `def` name.  Pick
  readable names; they survive into your synthesis logs.
- **Port list** — Sparkle uses SystemVerilog's `logic` type
  throughout; widths come from the `BitVec n` index.
- **Wire declarations** — `_gen_<name>` for `let`-bindings
  that need named storage; `_tmp_<n>` for compiler-internal
  wires the user didn't name.  Use named `let`s if you want
  readable waveforms.
- **`assign`** — every combinational expression compiles into a
  pure-comb `assign`.  Multiplexers (`Signal.mux`) become
  `?:` ternaries.

```lean
def addOrSub {dom : DomainConfig}
    (sub : Signal dom Bool) (a b : Signal dom (BitVec 8))
    : Signal dom (BitVec 8) :=
  Signal.mux sub (a - b) (a + b)

```
```lean
#synthesizeVerilog addOrSub

```
## 5.3 A registered design — `always_ff`

Sequential cells use `always_ff`.  Each `Signal.reg` / `<~`
pair generates one `always_ff` block.

Reset semantics depend on the domain's `resetKind`:

- **synchronous** (the default — `defaultDomain.resetKind =
  .synchronous`) → `always_ff @(posedge clk) begin if (rst) … end`
- **asynchronous** (`asyncDom : DomainConfig := { …, resetKind
  := .asynchronous }`) → `always_ff @(posedge clk or posedge rst)
  begin if (rst) … end`

Switching is a one-line edit in your `DomainConfig`; Ch 10 §10.3
goes deeper.

```lean
def regCounter {dom : DomainConfig} : Signal dom (BitVec 8) :=
  circuit do
    let count ← Signal.reg 0#8
    count <~ count + 1#8
    return count

```
```lean
#synthesizeVerilog regCounter

```
## 5.4 Wire-name hygiene

A common gotcha: combinational outputs without a `let` get
compiler-assigned names.  Compare:

```lean
-- Anonymous: the inner expression has no Lean-level name, so
-- the Verilog wire gets `_tmp_NN`.
def anonAdder {dom : DomainConfig}
    (a b : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  (a + b) &&& 0xFF#8

-- Named: the `let` binding `sum` becomes `_gen_sum` in Verilog.
def namedAdder {dom : DomainConfig}
    (a b : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  let sum := a + b
  sum &&& 0xFF#8

```
```lean
#synthesizeVerilog anonAdder

```
```lean
#synthesizeVerilog namedAdder

```
Look at the wire names in the two outputs.  When you start
debugging on a waveform, the named version saves time — you
can scope-search for `_gen_sum` directly.

## 5.5 Module composition and the hierarchy default

When one Sparkle `def` calls another, the generated Verilog
**inlines** the callee's body into the caller by default — no
sub-module per alias-style helper, no `inst_*` instance unless
you ask for one.  Ch 4 §4.6b walks through why, with both
output shapes side-by-side.  Two notes for this chapter:

1. **Default is inline.**  `def doubleThrough x := passthrough
   (passthrough x)` produces a single Verilog module
   (`doubleThrough`) with the body of `passthrough` expanded
   twice — no separate `module passthrough` block, no
   `inst_passthrough_*` instances.
2. **Opt INTO a real Verilog module** with
   `@[hardware_module]` for components you'll re-use, want to
   floorplan, or feed into out-of-context synthesis.  Use
   `#synthesizeVerilogDesign` to see the parent + every
   `@[hardware_module]`-tagged child in one printout.

```lean
def doubleThrough {dom : DomainConfig}
    (input : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  passthrough (passthrough input)

```
```lean
-- `passthrough` is untagged → its body is inlined into
-- `doubleThrough`.  Both prints show the same single-module
-- output with no `inst_*` lines.
#synthesizeVerilog doubleThrough

```
```lean
-- `synthesizeVerilogDesign` gives the same flat output here —
-- there are no `@[hardware_module]` children in this graph.
-- Add the attribute to `passthrough` to see it become an
-- explicit sub-module.
#synthesizeVerilogDesign doubleThrough

```
## 5.5b Picking the right Verilog command

Sparkle ships several elaborator commands for getting Verilog
out of a Lean design.  They all run the same synthesis
internally; the difference is where the output ends up:

| Command | Output | Use it when |
|---|---|---|
| `#synthesizeVerilog id` | plain text on the cell / terminal | quick smoke test; CI builds; when you don't care about the colour of keywords |
| `#synthesizeVerilogDesign id` | plain text, **all** modules in the design | hierarchical designs where you want to see every module, not just the top |
| `#showVerilog id` | syntax-highlighted HTML (in JupyterLab) | reading the SV inline in a notebook cell — keywords / wires / blocks get coloured by highlight.js |
| `#writeVerilogDesign id "out/foo.sv"` | a `.sv` file on disk | the output you'll actually feed to Yosys / Vivado / Verilator |
| `#writeDesign id "out/foo.sv" "out/foo_cppsim.h"` | `.sv` + a CppSim header | when you also want a JIT-friendly C++ surface (used by `lake exe …` benches) |

`#showVerilog` is the JupyterLab-native version of
`#synthesizeVerilog`: it wraps the SystemVerilog in a
highlight.js-tagged HTML block and ships it through xeus-lean's
`text/html` MIME channel, so the kernel paints the source
inline.  In headless `lake build` it still elaborates the design
(useful for typechecking) — the MIME marker bytes are emitted
but invisible in a terminal.

```lean
-- Plain text: works everywhere, no colour.
#synthesizeVerilog passthrough
```

```lean
-- Highlighted view: keywords coloured inside JupyterLab,
-- still typechecks in CI / `lake build`.
#showVerilog passthrough
```

## 5.5c Writing Verilog to a file

`#writeVerilogDesign` is the one you'll actually use in a real
project — it materialises the SV on disk where Yosys, Vivado,
or Verilator can pick it up:

```lean
-- Drops `Notebooks_Ch05_addOrSub.sv` into the build cache
-- (relative paths are resolved against Lake's project root).
#writeVerilogDesign addOrSub ".lake/build/gen/addOrSub.sv"
```

For designs that also need a CppSim wrapper (the JIT-friendly
C++ surface used by `Sparkle.Core.JIT.compileAndLoad`), use the
two-string form:

```lean
#writeDesign addOrSub
  ".lake/build/gen/addOrSub.sv"
  ".lake/build/gen/addOrSub_cppsim.h"
```

The output file paths are written relative to the directory
`lake build` was invoked from.  Inside JupyterLab that's the
notebook server's CWD — usually
`/workspace/sparkle/docs/tutorial/Notebooks/Gen/notebooks` in
the bundled tutorial image.  Use absolute paths
(`"/tmp/foo.sv"`) if you want output somewhere predictable.

## 5.5d Reading existing Verilog into Sparkle

Going the other way — pulling a `.sv` / `.v` file written by
hand or by another tool back into Sparkle — there are **two
distinct paths**, and which one you want depends on whether the
Verilog is fixed at edit time or only known at runtime.

### Path A — inline (elaboration time): `verilog!` / `sim!`

When the Verilog source is a literal string in your Lean file
(or copy-pasted into a notebook cell), use the `verilog!` /
`sim!` macros.  They run the parser **at elaboration time** and
materialise typed Lean definitions you can use immediately:

| Macro | What it generates |
|---|---|
| `verilog! "module … endmodule"` | `State`, `Input`, `nextState`; targets formal verification (theorems / proofs against the cycle function) |
| `sim! "module … endmodule"` | `SimInput`, `SimOutput`, `Simulator`, `load`, `toEndpoint`; targets fast JIT simulation |

```lean
verilog! "
module half_adder (input logic a, input logic b,
                   output logic sum, output logic cout);
  assign sum  = a ^ b;
  assign cout = a & b;
endmodule
"

-- The macro generated `half_adder.Verify.{State, Input, nextState}`.
-- `Input` is a structure with `a : Bool` / `b : Bool`; we can poke
-- it from a `#check` to confirm the shape and write proofs against
-- `nextState` from there (see Ch 6 / Ch 7 for the proof patterns).
#check @half_adder.Verify.Input
#check @half_adder.Verify.nextState
```

```lean
sim! "
module clk_counter (input clk, input rst, output [7:0] count);
  reg [7:0] c;
  assign count = c;
  always @(posedge clk)
    if (rst) c <= 8'h00; else c <= c + 8'h01;
endmodule
"

#check clk_counter.Sim.Simulator
-- Now `clk_counter.Sim.load`, `.step`, `.read`, `.reset`, `.destroy`
-- are all available — see Ch 8b for the simulation walk-through.
```

Because the parsing + lowering happens during `lake build`, a
broken Verilog string is a **compile-time error** with a useful
location, not a runtime failure.

### Path B — file (runtime): `Tools.SVParser.Parser.parse`

When the path is only known at runtime — a CLI argument, a
file dropped into `/tmp`, the output of an earlier
`#writeVerilogDesign` — read it with `IO.FS.readFile` and feed
the contents through `Tools.SVParser.Parser.parse` (or
`Tools.SVParser.Lower.parseAndLower` if you want a Sparkle IR
`Design` instead of the raw SystemVerilog AST):

```lean
def loadAndSummarise (path : System.FilePath) : IO Unit := do
  let src ← IO.FS.readFile path
  match Tools.SVParser.Parser.parse src with
  | .ok design =>
      IO.println s!"{path}: {design.modules.length} module(s)"
      for m in design.modules do
        IO.println s!"  - {m.name} ({m.items.length} items)"
  | .error e => IO.println s!"{path}: parse failed: {e}"

-- (Notebook only; uncomment after writing a file with
-- `#writeVerilogDesign` in an earlier cell.)
-- #eval loadAndSummarise "/tmp/addOrSub.sv"
```

The same `parse` returns a `Tools.SVParser.AST.Design` value
that you can inspect (count modules, read item lists) or feed
into `Tools.SVParser.parseAndLower` to get a Sparkle `Design`
for the JIT.  See `Tests/SVParser/ParserTest.lean` Tests 7–8
for a PicoRV32 end-to-end: read `/tmp/picorv32.v`, lower to
Sparkle IR, JIT-compile, run.

### Which one do I want?

- **`verilog!` / `sim!`** — your design's Verilog source is
  fixed at edit time and you want type-checked Lean wrappers
  (proofs, typed simulator, IDE autocomplete on inputs /
  outputs).  Source code lives in your `.lean` file.
- **`parse`** — the file path is dynamic, the contents change
  between runs, or you're writing a tool that processes
  user-supplied Verilog.  Source stays on disk.

## 5.5e Worked example — read Verilog, then prove it

`verilog!` doesn't just parse: it materialises a `nextState : State
→ Input → State` function we can reason about directly with Lean's
proof tactics.  Below is a one-register synchronous XOR — a single
flop that captures `a ^ b` every cycle, with a synchronous reset
that clears it back to zero — followed by three theorems that pin
down its behaviour for every input.

```lean
verilog! "
module sum_reg(input logic clk, input logic rst,
               input logic a, input logic b,
               output logic [0:0] result);
  always @(posedge clk)
    if (rst) result <= 1'b0;
    else     result <= a ^ b;
endmodule
"

```
`verilog!` inferred the I/O record from the port list (`clk` is
recognised as the clock and dropped from `Input`) and turned the
single `always` block into a `nextState` step function:

```lean
#check @sum_reg.Verify.Input       -- { rst, a, b : BitVec 1 }
#check @sum_reg.Verify.State       -- { _reg_result : BitVec 1 }
#check @sum_reg.Verify.nextState
-- sum_reg.Verify.State → sum_reg.Verify.Input → sum_reg.Verify.State

```
Now the three properties.  Each one unfolds `nextState` with `simp`
and discharges the residual `BitVec`-level goal with `bv_decide`
(SAT-backed bit-blasting) — no induction, no clock-counting:

```lean
-- (1) Reset always wins: asserting `rst` clears the register to 0
--     no matter what `a`, `b`, or the prior state were.
theorem sum_reg_reset (s : sum_reg.Verify.State) (a b : BitVec 1) :
    (sum_reg.Verify.nextState s { rst := 1, a := a, b := b })._reg_result
      = 0#1 := by
  simp [sum_reg.Verify.nextState]

-- (2) When reset is deasserted, the register captures a XOR b
--     on the next clock.
theorem sum_reg_xor (s : sum_reg.Verify.State) (a b : BitVec 1) :
    (sum_reg.Verify.nextState s { rst := 0, a := a, b := b })._reg_result
      = a ^^^ b := by
  simp [sum_reg.Verify.nextState]

-- (3) Both branches at once — a full behavioural spec, ∀-quantified
--     over every input the parser admitted.
theorem sum_reg_spec (s : sum_reg.Verify.State) (i : sum_reg.Verify.Input) :
    (sum_reg.Verify.nextState s i)._reg_result =
      (if i.rst = 0 then i.a ^^^ i.b else 0) := by
  simp [sum_reg.Verify.nextState]
  bv_decide

```
The same pattern scales: drop in any Verilog module via `verilog!`,
`simp [<module>.Verify.nextState]` to unfold the step function, and
let `bv_decide` (or `decide` on small finite types) finish off the
residual bit-vector goal.  Ch 6 takes this further with
temporal-logic invariants over multi-cycle behaviour.

## 5.6 Where to go next

- **Ch 6 — Proofs (LTL)**: prove invariants on the design
  you just synthesised.
- **Ch 7 — Equivalence checking**: prove two designs match.
- **Ch 8 — Yosys**: take the SystemVerilog output and run it
  through Yosys for netlist + LUT-count analysis.
- **`docs/reference/Troubleshooting_Synthesis.md`** — the
  reference manual for what compiles to Verilog and what
  doesn't.

end Notebooks.Ch05
