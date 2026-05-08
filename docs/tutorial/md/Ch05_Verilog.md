
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
  Signal.circuit do
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

## 5.5 Module composition becomes Verilog instantiation

When one Sparkle `def` calls another, the generated Verilog
emits a module instance — not inlined logic.  This keeps the
Verilog hierarchy aligned with the Lean code, which is huge
for tool-chain diff readability.

(Compose two passthroughs as a sanity demo.)

```lean
def doubleThrough {dom : DomainConfig}
    (input : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  passthrough (passthrough input)

```
```lean
#synthesizeVerilog doubleThrough

```
## 5.5b Reading the Verilog inside the notebook

`#synthesizeVerilog` prints the generated SystemVerilog to the
log.  Inside JupyterLab you can do better: `Display.verilog`
wraps a string in a Highlight.js code block so the kernel shows
keywords (`module`, `input`, `assign`, `always_ff`) coloured
inline.

In headless `lake build` the call is a no-op (the shim emits a
MIME marker that JupyterLab would render and the terminal
ignores), so the chapter typechecks the same way under both
runtimes.

```lean
def alu1 : String :=
  "module alu1 (input  logic [3:0] a,\n" ++
  "             input  logic [3:0] b,\n" ++
  "             input  logic       sub,\n" ++
  "             output logic [3:0] y);\n" ++
  "  assign y = sub ? (a - b) : (a + b);\n" ++
  "endmodule\n"

#eval Display.verilog alu1
```

In a real workflow you'd capture `#synthesizeVerilog` output to
a string (via `IO.FS.writeFile` + `IO.FS.readFile`) and feed it
to `Display.verilog`; here we hand-write a small example so the
chapter has no file-system dependency.

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
