
# Chapter 2 — Combinational Circuits

A **combinational** circuit produces its output as a pure
function of its inputs — no clock edges, no flip-flops, no
memory.  In Sparkle, every wire is a `Signal dom α` (a value
changing over discrete cycles), and combinational logic is just
pointwise computation on those signals.

This chapter covers the basic gates (AND/OR/NOT/XOR), the
multiplexer, and a half-adder, and at the end we look at the
generated Verilog side-by-side.

```lean
import Sparkle
import Sparkle.Compiler.Elab
import Display

open Sparkle.Core.Domain
open Sparkle.Core.Signal

namespace Notebooks.Ch02

```
## 2.1 Bool wires and basic gates

A single-bit wire has type `Signal dom Bool`.  Sparkle's
operators `&&&` (AND), `|||` (OR), `^^^` (XOR), `~~~` (NOT)
work directly on signal pairs — no `Signal.pure`, no `<$>`.

```lean
def myAnd {dom : DomainConfig}
    (a b : Signal dom Bool) : Signal dom Bool :=
  a &&& b

def myOr {dom : DomainConfig}
    (a b : Signal dom Bool) : Signal dom Bool :=
  a ||| b

def myXor {dom : DomainConfig}
    (a b : Signal dom Bool) : Signal dom Bool :=
  a ^^^ b

def myNot {dom : DomainConfig}
    (a : Signal dom Bool) : Signal dom Bool :=
  ~~~a

```
## 2.2 BitVec wires and bitwise operators

A multi-bit bus is `Signal dom (BitVec n)`.  The same operators
work on buses (mixed with literals via Sparkle's
`HAdd`/`HAnd`/etc. instances).  No domain juggling, no `pure`.

```lean
def maskByte {dom : DomainConfig}
    (data : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  data &&& 0x000000FF#32

def setMSB {dom : DomainConfig}
    (data : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  data ||| 0x80#8

def addOneByte {dom : DomainConfig}
    (data : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  data + 1#8

```
## 2.3 Multiplexer

An `if … then … else` works on plain `Bool`, but **not** on
`Signal dom Bool` — Lean compiles `if` to `Decidable.rec`,
which the synthesis backend can't handle.  Use `Signal.mux`.

```text
  sel ──┐
        │
  a ────┼── ╲
        │   │── out = sel ? a : b
  b ────┼── ╱
```

(We'll render this as an SVG block diagram further down.)

```lean
def myMux {dom : DomainConfig}
    (sel : Signal dom Bool) (a b : Signal dom (BitVec 8))
    : Signal dom (BitVec 8) :=
  Signal.mux sel a b

```
## 2.4 Half-adder

A half-adder takes two single-bit inputs and produces a sum bit
(XOR) and a carry bit (AND).  Multi-output: we'll learn the
proper `declare_signal_state` named-record idiom in Chapter 4;
for now, a tuple is fine.

```lean
def halfAdder {dom : DomainConfig}
    (a b : Signal dom Bool) : Signal dom Bool × Signal dom Bool :=
  (a ^^^ b, a &&& b)

```
## 2.5 Visualising — the truth-table sweep

We can verify the half-adder behaves like a behavioural spec
by exhaustively enumerating its inputs.  `BitVec 1` has two
values, so a 2-input gate has 4 cases.

```lean
-- Behavioural spec: ordinary Lean function on plain Bools.
-- (Plain `Bool` uses `xor` / `&&`; `^^^` is for `BitVec n` and
-- for the Sparkle Signal-Bool instance.)
def halfAdderSpec (a b : Bool) : Bool × Bool :=
  (xor a b, a && b)

-- A small fixture array so the test is decidable.
def halfAdderTable : List ((Bool × Bool) × (Bool × Bool)) :=
  [((false, false), halfAdderSpec false false),
   ((false, true ), halfAdderSpec false true ),
   ((true , false), halfAdderSpec true  false),
   ((true , true ), halfAdderSpec true  true )]

example : halfAdderTable =
  [((false, false), (false, false)),
   ((false, true ), (true , false)),
   ((true , false), (true , false)),
   ((true , true ), (false, true ))] := by
  native_decide

```
## 2.6 Block diagram

A simple Mermaid sketch of the half-adder.  In a notebook this
renders as a real diagram; under plain `lake build` it compiles
but the diagram is just emitted as MIME text on stdout.

```lean
-- (Notebook only.  Comment toggled off for headless `lake build`.)
-- #eval Display.blockDiagram "
--   flowchart LR
--     a((a))
--     b((b))
--     a --> X[XOR]
--     b --> X
--     a --> A[AND]
--     b --> A
--     X --> sum((sum))
--     A --> carry((carry))"

```
## 2.7 Verilog generation

The whole point of writing in a synthesis-safe subset is that
we can hand the design to `#synthesizeVerilog` and get
SystemVerilog out.  The macro is in `Sparkle.Compiler.Elab`.

Below we emit Verilog for our 8-bit `myMux`.  Read the output
alongside the Lean source: the structure should be obvious — a
`case`/`assign` controlled by `sel`.

```lean
#synthesizeVerilog myMux

```
## 2.8 Exercise — 4:1 mux from 2:1 muxes

Build a 4:1 mux (`sel : BitVec 2`, four data inputs `a, b, c, d`)
using **only** `Signal.mux` and the bit-extraction operator
`Signal.bitVecAt` (or projections).  Hint: `sel.fst` /
`sel.snd` if you split into two single-bit signals, or
`sel === 0#2` etc.

The reference solution lives in
`Notebooks/Solutions/Ch02.lean` and is build-checked to match a
behavioural spec.  Try yours first; if you get stuck, peek there.

```lean
-- TODO: implement `mux4` here.
-- def mux4 {dom : DomainConfig}
--     (sel : Signal dom (BitVec 2))
--     (a b c d : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
--   sorry

end Notebooks.Ch02
```
