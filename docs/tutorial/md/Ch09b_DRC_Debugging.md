# Chapter 9b — Design Rule Checks and Debugging Synthesis

Chapter 9 took a finished design to a board. This chapter is about
the minutes *before* that: catching mistakes while the design is still
Lean source, and reading the messages Sparkle gives when a definition
simulates but does not synthesize. Everything here runs in the editor —
no FPGA toolchain is needed.

```lean
import Sparkle
import Sparkle.Compiler.Elab
import Sparkle.Compiler.SynthesizableLint

open Sparkle.Core.Domain
open Sparkle.Core.Signal

namespace Notebooks.Ch09b

```
## 9b.1 What the DRC checks

Every synthesis command (`#synthesizeVerilog`, `#showVerilog`,
`#writeVerilogDesign`, `#writeDesign`, `#writeCppSimDesign`,
`#writeCudaDesign`, …) runs a **design rule check** on the synthesized
IR before any backend sees it. Findings are printed as
`[DRC <rule> <severity>] <message>` followed by a `fix:` line.

| Rule | Severity | Finding |
|------|----------|---------|
| DRC001 | error | combinational loop through `assign`s |
| DRC002 | error | a name driven by more than one statement |
| DRC003 | error | an output, or a wire that is read, that nothing drives |
| DRC004 | error | a reference to a name that is neither declared nor driven |
| DRC005 | error | a register whose clock/reset is not declared |
| DRC010 | warning | an output driven by logic rather than directly by a register |
| DRC011 | warning | an assignment that silently drops upper bits |
| DRC012 | warning | an input that is never read |
| DRC013 | warning | a zero-width port |

The error-class rules describe RTL that is wrong or that tools reject;
the warning-class rules describe legal RTL that is usually a mistake or
a timing hazard. DRC never changes the design — the Verilog is the same
with or without it.

## 9b.2 DRC in action

In a sequential module, an output that passes through logic after the
last register gets a DRC010 warning: the path from the register through
that logic to the pin counts against the next module's clock budget.
(Purely combinational blocks are not flagged — their outputs are
combinational by construction.)

```lean
def regThenAdd (a : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  let r := Signal.register 0#8 a
  r + a

#synthesizeVerilog regThenAdd
```

Registering the sum instead makes the warning go away:

```lean
def regAdd (a b : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  Signal.register 0#8 (a + b)

#synthesizeVerilog regAdd
```

An argument you keep on purpose but do not read (a port reserved for a
later revision, say) is reported by DRC012 unless its name starts with
`_`:

```lean
def keepsSpare (a _spare : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  Signal.register 0#8 a

#synthesizeVerilog keepsSpare
```

## 9b.3 Strict mode for CI

By default every finding is a warning, so exploration in the editor is
never blocked. In a project's CI — or right before generating a
bitstream — turn the error-class rules into build failures:

```text
set_option sparkle.drc.strict true
```

With strict mode on, a DRC001–DRC005 finding fails the command
(`DRC failed with N error(s)`), so `lake build` exits non-zero before a
broken netlist reaches yosys.

## 9b.4 Reading "does not synthesize" errors

Everything in `Signal` simulates, but only part of it has a hardware
meaning. When synthesis refuses a definition, the message names the
construct and the fix. Two common cases:

**A container as an output.** A `Signal` of `Vector` has no port
layout:

```text
def vecOut (a : Signal defaultDomain (BitVec 8)) :
    Signal defaultDomain (Vector (BitVec 8) 2) := …
#synthesizeVerilog vecOut
-- error: Cannot synthesize vecOut: its output is a Signal of `Vector`
--   (Vector (BitVec 8) 2), which has no hardware port layout.
--   fix: return one Signal per element as a tuple or a structure of
--   Signals (one output port each), or pack the elements into one
--   BitVec with `++`.
```

Returning a tuple works — each component becomes part of the output:

```lean
def pairOut (a b : Signal defaultDomain (BitVec 8)) :
    Signal defaultDomain (BitVec 8 × BitVec 8) :=
  bundle2 (a + b) (a - b)

#synthesizeVerilog pairOut
```

**A constant lifted with `map`.** `a.map (fun _ => true)` simulates,
but the synthesizer has no rule for a lifted `Bool` constant. The error
names the culprit and only the matching fix:

```text
-- error: Cannot synthesise Sparkle.Core.Signal.Signal.map: not inlinable …
-- Inline expansion failed with:
-- Cannot instantiate Bool.true: not a hardware module definition
-- Likely cause:
--   · `sig.map (fun _ => true)` / `(fun _ => false)` lifts a Bool constant …
--     use `Signal.pure true`, or drop the redundant `&& true`.
```

```lean
def alwaysOn : Signal defaultDomain Bool := Signal.pure true

#synthesizeVerilog alwaysOn
```

## 9b.5 Linting before synthesizing

`#check_synthesizable` scans a definition for the patterns that
simulate but do not synthesize (`Id.run`/`let mut`, a `match` on a
non-hardware type, a pure `if` on a `Signal`, `Signal.val` in the
synthesis path) without running synthesis:

```lean
#check_synthesizable regAdd
```

The full catalogue, with a fix for each pattern, is in
`docs/known-issues/KnownIssues.md`.

## 9b.6 When synthesis is slow

Set `SPARKLE_PROFILE=1` in the environment before `lake build` or
`lake env lean`. Each synthesis command then prints its phase timings
(and appends them to `/tmp/sparkle-profile.log`), which tells you
whether the time goes into translating the Lean term or into the IR
passes. `docs/reference/Compiler_Performance.md` explains how to read
the log.

## 9b.7 Checklist before the board

Before running the Chapter 9 flow on a new design:

1. **DRC is clean** with `set_option sparkle.drc.strict true`, and the
   remaining DRC010 warnings are on outputs you know are combinational.
2. **It simulates** against a reference (Chapter 8b).
3. **It fits**: `#verify_fpga <design> tangNano20K` (Chapter 9.7).
4. **The top wrapper** maps every port to a pin in the `.cst` file, and
   the reset polarity matches the board's button (Chapter 9).
5. **Clock budget**: registered outputs at every module boundary that
   crosses a pin or a long route (DRC010).

```lean
end Notebooks.Ch09b
```
