# Chapter 6b — Automatic checks with an SMT solver

Chapter 6 proved temporal properties by hand, in Lean. This chapter
hands the search to a solver instead: you state a property, and z3
either finds a concrete trace that breaks it or reports that none
exists. It is the fastest way to find out that a design is wrong, and
often enough to show that it is right.

The commands need `z3` on `PATH` (or `SPARKLE_Z3=/path/to/z3`). Without
it they still build: they write the query and warn that nothing was
checked.

```lean
import Sparkle
import Sparkle.Compiler.Elab

open Sparkle.Core.Domain
open Sparkle.Core.Signal

namespace Notebooks.Ch06b

```
## 6b.1 A property is a circuit

There is no separate assertion language. A property is an ordinary
circuit that returns `Signal dom Bool`: a *monitor* that contains the
design, watches it, and outputs `true` while everything is fine. Its
inputs are the free inputs of the check — the solver picks them.

The design: a counter that counts 0..9 while `en` is high.

```lean
def counter10 (en : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 4) :=
  Signal.loop fun c =>
    let next := Signal.mux (c === Signal.pure 9#4) (Signal.pure 0#4) (c + 1#4)
    Signal.register 0#4 (Signal.mux en next c)

/-- The count is always below 10. -/
def countBelow10 (en : Signal defaultDomain Bool) : Signal defaultDomain Bool :=
  Signal.ultC (counter10 en) 10#4

```
## 6b.2 Bounded model checking — `#bmc`

`#bmc f k` asks: starting from reset, is there any choice of inputs for
which `f` is false in one of the cycles 0..k?

```lean
#bmc countBelow10 20

```
Now a property that is wrong:

```lean
/-- Wrong: the count does reach 9. -/
def countBelow9 (en : Signal defaultDomain Bool) : Signal defaultDomain Bool :=
  Signal.ultC (counter10 en) 9#4

#bmc countBelow9 20 expect violation

```
Without `expect violation` this is a build error. Either way the
message shows the shortest trace that breaks the property — one column
per cycle, inputs, registers and outputs in hexadecimal — and the path
of a VCD file with every signal, for a waveform viewer:

```text
#bmc countBelow9: violated at cycle 9
  cycle        0 1 2 3 4 5 6 7 8 9
  en (in)      1 1 1 1 1 1 1 1 1 0
  next         1 2 3 4 5 6 7 8 9 0
  … (reg)      0 1 2 3 4 5 6 7 8 9
  out (out)    1 1 1 1 1 1 1 1 1 0
  waveform: .lake/build/gen/smt/…countBelow9.cex.vcd
```

`#bmc` is a bounded check: "no violation in cycles 0..20" says nothing
about cycle 21.

## 6b.3 Every cycle — `#kinduction`

`#kinduction f k` closes that gap with induction over time:

- **base**: no violation in cycles 0..k-1 from reset (a `#bmc`);
- **step**: from *any* state, k consecutive good cycles are followed by
  a good one.

If both hold, the property holds in every reachable cycle.

```lean
#kinduction countBelow10 1

```
The step starts from any state, including ones the design can never
reach. That is why a true property can fail it:

```lean
/-- True from reset — the counter only visits 0..9 — but not inductive. -/
def countNot12 (en : Signal defaultDomain Bool) : Signal defaultDomain Bool :=
  Signal.mux (counter10 en === Signal.pure 12#4) (Signal.pure false) (Signal.pure true)

#kinduction countNot12 3 expect failure

```
The reported trace starts with the counter at 10 or 11 — unreachable,
but allowed by "not 12" — and walks into 12. Raising `k` does not help
here (the counter can sit at 11 for as long as `en` is low). The fix is
to *strengthen* the property until it excludes the bad states:
`countBelow10` is that strengthening, and it implies `countNot12`.

## 6b.4 Assumptions and history

A monitor can keep its own state, so a property can talk about the past.
"While `en` has never been high, the count is 0" needs one register that
remembers whether `en` was ever high:

```lean
def zeroUntilEnabled (en : Signal defaultDomain Bool) : Signal defaultDomain Bool :=
  let seen : Signal defaultDomain Bool :=
    Signal.loop fun s => Signal.register false (Signal.mux en (Signal.pure true) s)
  let isZero := counter10 en === Signal.pure 0#4
  Signal.mux seen (Signal.pure true) isZero        -- seen ∨ isZero

#kinduction zeroUntilEnabled 1

```
The same pattern expresses an assumption about the environment: compute
"the inputs have obeyed the protocol so far" in the monitor, and output
`true` whenever that flag is false.

## 6b.5 Taking the property elsewhere — `#writeSvaChecker`

The monitor is a circuit, so it synthesizes. `#writeSvaChecker` writes
it as a SystemVerilog module with a concurrent assertion on its output,
for use in another simulator or formal tool:

```lean
#writeSvaChecker countBelow10 ".lake/build/gen/smt/count_below_10.sv"

```
```text
    assert property (@(posedge clk) disable iff (rst) out)
      else $error("…countBelow10: property violated");
```

## 6b.6 What the answers mean

| Answer | Meaning | Rests on |
|--------|---------|----------|
| `#bmc`: violated | a real trace from reset breaks the property | the trace itself — you can simulate it |
| `#bmc`: no violation | none within k cycles | z3 and the SMT translation |
| `#kinduction`: holds | none in any cycle | z3 and the SMT translation |
| `#kinduction`: not inductive | undecided — strengthen the property or raise k | — |

A "holds" answer is not a Lean proof: nothing is checked by the kernel.
For a kernel-checked statement, prove it as in Chapter 6; use the solver
to find the bugs first and to discover which invariant is inductive.

The checks cover flat designs (no `@[hardware_module]` instances) with
registers and single-port memories. Liveness ("eventually") is out of
scope.

```lean
end Notebooks.Ch06b
```
