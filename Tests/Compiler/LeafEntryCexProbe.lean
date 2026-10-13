import Lean.Elab.Command
import Sparkle.IR.RefineCheck

/-! # Two probe modules for the leaf entry's missing compiler facts (G-reg, G-opt; round par/a-24)

LOG ONLY: this file asserts nothing and proves nothing. It evaluates the
compiler's own functions on two hand-written IR modules and logs the results,
so that two PREDICTIONS made by reading (`docs/parallel/A-leaf-entry-2.md`
§1, §3) become measurements. Neither module is the output of the elaborator;
each is the smallest IR module found by reading.

## `mergeCex` — G-reg is false as a statement about all modules

    m.body.all isAssign = false → (mergeChecked m).body.all isAssign = false

Predicted FALSE on `mergeCex`: a register `n` and an assignment `n := 5`
share the name `n`; an earlier assignment `a := 5` has the assignment's
signature. `mergeDuplicatesParts` keys its classes by NAME; the class of `n`
is the class of the LAST statement defining `n` (the assignment), whose
first member is `a`; EVERY statement defining `n` — the register too —
becomes `n := a`. The merged body is assignments only. `refineCheck m r`
pairs the registers of `r` (none) into those of `m` and has no count
conjunct; `masksKept` and `printOk` do not look at registers.

Predicted log: `isAssign-all of m = false`, `refineCheck = true`,
`masksKept = true`, `printOk = true`, `isAssign-all of mergeChecked m = true`.

(The module is multiply driven: not a module the elaborator emits. It refutes
the unrestricted statement, not the merge of a well-formed module.)

## `optCex` — G-opt is false for the optimizer

    simpleBody m = false → m.body.all seqStmtOk = true →
      checkedOptimize m = m ∨ printOk (checkedOptimize m) = true

Predicted FALSE on `optCex`: a 32-bit register `r` with next value
`u := t + 1`, `t := r << 2` (literal amount). `printOk optCex = true` (a
literal-amount shift is in the fragment as the whole right-hand side of an
assignment). `optimizeModule` inlines the single-use wire `t` into `u`
(Phase 3; `u` is protected as a register-input wire; a 32-bit wire gets no
`& mask`): `u := (r << 2) + 1`. `refineCheck` normalises wires away and
accepts. `sf4` refuses a literal-amount shift as an operand of `+`
(`notShl`): `printOk` of the accepted candidate is false.

Predicted log: `simpleBody = false`, `printOk m = true`,
`refineCheck m o = true`, `printOk o = false`, `checkedOptimize m == m` false,
`printOk (checkedOptimize m) = false`.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tests.Compiler.LeafEntryCexProbe
open Sparkle.IR.AST

/-- A register and an assignment share the name `n`. -/
def mergeCex : Module :=
  { name := "mergeCex"
    inputs := [{ name := "clk", ty := .bit }, { name := "rst", ty := .bit }]
    outputs := []
    wires := [{ name := "a", ty := .bitVector 8 }, { name := "n", ty := .bitVector 8 }]
    body :=
      [ .assign "a" (.const 5 8)
      , .register "n" "clk" ("rst", .synchronous) (.const 0 8) 0
      , .assign "n" (.const 5 8) ] }

/-- A 32-bit register whose next value adds to a single-use literal-amount
left shift. -/
def optCex : Module :=
  { name := "optCex"
    inputs := [{ name := "clk", ty := .bit }, { name := "rst", ty := .bit }]
    outputs := [{ name := "out", ty := .bitVector 32 }]
    wires := [{ name := "r", ty := .bitVector 32 }, { name := "t", ty := .bitVector 32 },
      { name := "u", ty := .bitVector 32 }]
    body :=
      [ .assign "t" (.op .shl [.ref "r", .const 2 32])
      , .assign "u" (.op .add [.ref "t", .const 1 32])
      , .register "r" "clk" ("rst", .synchronous) (.ref "u") 0
      , .assign "out" (.ref "r") ] }

run_cmd do
  let m := mergeCex
  let r := Sparkle.IR.RegDedup.mergeDuplicates m
  let k := Sparkle.IR.RefineCheck.mergeChecked m
  let a0 : Bool := m.body.all Sparkle.IR.RegDedup.isAssign
  let a1 : Bool := k.body.all Sparkle.IR.RegDedup.isAssign
  let g1 : Bool := Sparkle.IR.RefineCheck.refineCheck m r
  let g2 : Bool := Sparkle.IR.RefineCheck.masksKept m r
  let g3 : Bool := Sparkle.IR.PrintGuard.printOk r
  Lean.logInfo s!"LEAFCEX MERGE mergeCex: isAssign-all of m = {a0}; mergeDuplicates body = {repr r.body}; refineCheck m r = {g1}; masksKept m r = {g2}; printOk r = {g3}; mergeChecked body = {repr k.body}; isAssign-all of mergeChecked m = {a1}"
  let verdict : String :=
    if !a0 && a1 then "PREDICTION CONFIRMED — 'm.body.all isAssign = false → (mergeChecked m).body.all isAssign = false' is FALSE on mergeCex"
    else "PREDICTION REFUTED — the statement holds on mergeCex (the reading of mergeDuplicatesParts / the guard in docs/parallel/A-leaf-entry-2.md §1 is wrong somewhere: see the values above)"
  Lean.logInfo s!"LEAFCEX MERGE VERDICT: {verdict}"

run_cmd do
  let m := optCex
  let o := Sparkle.IR.Optimize.optimizeModule m
  let k := Sparkle.IR.OptCheck.checkedOptimize m
  let sb : Bool := Sparkle.IR.OptCheck.simpleBody m
  let sq : Bool := m.body.all Sparkle.IR.OptCheck.seqStmtOk
  let p0 : Bool := Sparkle.IR.PrintGuard.printOk m
  let rc : Bool := Sparkle.IR.RefineCheck.refineCheck m o
  let p1 : Bool := Sparkle.IR.PrintGuard.printOk o
  let same : Bool := k == m
  let p2 : Bool := Sparkle.IR.PrintGuard.printOk k
  Lean.logInfo s!"LEAFCEX OPT optCex: simpleBody m = {sb}; seqStmtOk-all = {sq}; printOk m = {p0}; optimizeModule body = {repr o.body}; wires = {o.wires.map (·.name)}; refineCheck m o = {rc}; printOk o = {p1}; checkedOptimize m == m: {same}; printOk (checkedOptimize m) = {p2}"
  let verdict : String :=
    if !sb && sq && p0 && !same && !p2 then "PREDICTION CONFIRMED — 'checkedOptimize m = m ∨ printOk (checkedOptimize m) = true' is FALSE on optCex although printOk optCex = true"
    else "PREDICTION REFUTED — see the values above (docs/parallel/A-leaf-entry-2.md §3)"
  Lean.logInfo s!"LEAFCEX OPT VERDICT: {verdict}"

end Tests.Compiler.LeafEntryCexProbe
