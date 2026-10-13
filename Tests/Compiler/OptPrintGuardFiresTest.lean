import Lean.Elab.Command
import Tests.Compiler.LeafEntryCexProbe
import Tests.Compiler.OptPrintSourceTest
import Tools.ShippingGuardsLeaf

/-! # The two guards FIRE, with their guarantee (candidate branch `fix/opt-print-guard`)

The ruling on guards: a guard needs a minimal firing counterexample together
with the guarantee it buys. This file asserts both, for the two guards this
branch adds to `Sparkle/IR/RefineCheck.lean`.

## The guarantees (theorems, restated here; standard axioms asserted)

* `opt_guard_guarantee`: `simpleBody m = false → m.body.all seqStmtOk = true →
  checkedOptimize m = m ∨ printOk (checkedOptimize m) = true`;
* `merge_guard_guarantee`: `m.body.all isAssign = false →
  (mergeChecked m).body.all isAssign = false`.

## The firing modules (evaluated; an error when a value is not as stated)

* `optCex` (`Tests/Compiler/LeafEntryCexProbe.lean`, hand-written IR): the
  hypotheses of the guarantee hold, `printOk optCex`, `refineCheck` accepts
  the optimizer's candidate, `printOk` of the candidate is FALSE — the new
  conjunct is the one that fails — and `checkedOptimize optCex == optCex`
  (the fallback), whose `printOk` is true.
* `mergeCex` (same file, hand-written IR, multiply driven): the body is not
  assignment-only, `refineCheck`, `masksKept`, `printOk` accept the merge,
  the merged body IS assignment-only — the new conjunct is the one that
  fails — and `mergeChecked mergeCex == mergeCex`, still not
  assignment-only.
* `shlAdd32` (`Tests/Compiler/OptPrintSourceTest.lean`, a REAL source): the
  full entry's module takes the assign + register branch, the candidate is
  accepted by `refineCheck` and is outside the print fragment; the shipped
  top `checkedOptimize b` is `b` and passes `printOk`. (On poc the same
  module is shipped with `printOk` false.)

Also asserted: on the three modules the compiler's functions now equal the
candidates computed in test code on poc
(`OptPrintGuardDefs.guardedOptimize`, `mergeGuarded`).

Nothing here is a statement about emitted text being right or wrong:
`printOk` says the text is inside the fragment for which text meaning = IR
meaning is proved.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tests.Compiler.OptPrintGuardFiresTest
open Lean Meta
open Sparkle.Compiler.Elab
open Tests.Compiler.CallWidthHuntTest (resetRefs)
open Tests.Compiler.OptPrintGuardDefs (tf)

/-- The guarantee of the optimizer's print guard. -/
theorem opt_guard_guarantee (m : Sparkle.IR.AST.Module)
    (hs : Sparkle.IR.OptCheck.simpleBody m = false)
    (hok : m.body.all Sparkle.IR.OptCheck.seqStmtOk = true) :
    Sparkle.IR.OptCheck.checkedOptimize m = m ∨
      Sparkle.IR.PrintGuard.printOk (Sparkle.IR.OptCheck.checkedOptimize m) = true :=
  Tools.ShippingGuardsLeaf.checkedOptimize_instFree_print hs hok

/-- The guarantee of the merge's non-assignment guard. -/
theorem merge_guard_guarantee (m : Sparkle.IR.AST.Module)
    (h : m.body.all Sparkle.IR.RegDedup.isAssign = false) :
    (Sparkle.IR.RefineCheck.mergeChecked m).body.all Sparkle.IR.RegDedup.isAssign = false :=
  Tools.ShippingGuardsLeaf.mergeChecked_keeps_nonAssign h

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in [``opt_guard_guarantee, ``merge_guard_guarantee] do
    for ax in ← Lean.collectAxioms n do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{n} uses a non-standard axiom: {ax}"
  logInfo m!"GUARDFIRES GUARANTEES: opt_guard_guarantee, merge_guard_guarantee — standard axioms"

/-! ## `optCex`: the optimizer's print guard fires -/

run_cmd do
  let m := Tests.Compiler.LeafEntryCexProbe.optCex
  let o := Sparkle.IR.Optimize.optimizeModule m
  let k := Sparkle.IR.OptCheck.checkedOptimize m
  let sb : Bool := Sparkle.IR.OptCheck.simpleBody m
  let sq : Bool := m.body.all Sparkle.IR.OptCheck.seqStmtOk
  let p0 : Bool := Sparkle.IR.PrintGuard.printOk m
  let rc : Bool := Sparkle.IR.RefineCheck.refineCheck m o
  let p1 : Bool := Sparkle.IR.PrintGuard.printOk o
  let same : Bool := k == m
  let p2 : Bool := Sparkle.IR.PrintGuard.printOk k
  let cand : Bool := Tests.Compiler.OptPrintGuardDefs.guardedOptimize m == k
  Lean.logInfo s!"GUARDFIRES OPT optCex: simpleBody m = {sb}; seqStmtOk-all = {sq}; printOk m = {p0}; refineCheck m o = {rc}; printOk o = {p1}; checkedOptimize m == m: {same}; printOk (checkedOptimize m) = {p2}; equals the test-code candidate guardedOptimize: {cand}"
  if sb then throwError "optCex: simpleBody is true — not the guarded branch"
  unless sq do throwError "optCex: not an assign + register body — not the guarded branch"
  unless p0 do throwError "optCex: printOk of the module itself is false"
  unless rc do throwError "optCex: refineCheck refuses the candidate — the print guard is not the conjunct that fails"
  if p1 then throwError "optCex: printOk of the candidate is true — the guard does not fire"
  unless same do throwError "optCex: checkedOptimize did not return the input module"
  unless p2 do throwError "optCex: printOk of the shipped module is false"
  unless cand do throwError "optCex: checkedOptimize differs from guardedOptimize"
  Lean.logInfo "GUARDFIRES OPT VERDICT: the print guard FIRES on optCex (candidate accepted by refineCheck, outside the print fragment); the input module is shipped and passes printOk — the disjunction of opt_guard_guarantee holds by BOTH disjuncts here"

/-! ## `mergeCex`: the merge's non-assignment guard fires -/

run_cmd do
  let m := Tests.Compiler.LeafEntryCexProbe.mergeCex
  let r := Sparkle.IR.RegDedup.mergeDuplicates m
  let k := Sparkle.IR.RefineCheck.mergeChecked m
  let a0 : Bool := m.body.all Sparkle.IR.RegDedup.isAssign
  let ar : Bool := r.body.all Sparkle.IR.RegDedup.isAssign
  let a1 : Bool := k.body.all Sparkle.IR.RegDedup.isAssign
  let g1 : Bool := Sparkle.IR.RefineCheck.refineCheck m r
  let g2 : Bool := Sparkle.IR.RefineCheck.masksKept m r
  let g3 : Bool := Sparkle.IR.PrintGuard.printOk r
  let same : Bool := k == m
  let cand : Bool := Tests.Compiler.OptPrintGuardDefs.mergeGuarded m == k
  Lean.logInfo s!"GUARDFIRES MERGE mergeCex: isAssign-all of m = {a0}; refineCheck m r = {g1}; masksKept m r = {g2}; printOk r = {g3}; isAssign-all of mergeDuplicates m = {ar}; mergeChecked m == m: {same}; isAssign-all of mergeChecked m = {a1}; equals the test-code candidate mergeGuarded: {cand}"
  if a0 then throwError "mergeCex: the body is assignment-only — not the guarded branch"
  unless g1 && g2 && g3 do
    throwError "mergeCex: an older conjunct refuses the merge — the non-assignment guard (a non-assignment statement must remain) is not the conjunct that fails"
  unless ar do throwError "mergeCex: the merged body is not assignment-only — the guard does not fire"
  unless same do throwError "mergeCex: mergeChecked did not return the input module"
  if a1 then throwError "mergeCex: the kept body is assignment-only"
  unless cand do throwError "mergeCex: mergeChecked differs from mergeGuarded"
  Lean.logInfo "GUARDFIRES MERGE VERDICT: the non-assignment guard (a non-assignment statement must remain) FIRES on mergeCex (merge accepted by refineCheck, masksKept and printOk, merged body assignment-only); the input module is kept and is not assignment-only — the conclusion of merge_guard_guarantee"

/-! ## `shlAdd32`: a real source whose shipped top is now inside the print fragment -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let n : Name := ``Tests.Compiler.OptPrintSourceTest.shlAdd32
  let res ← Tests.Compiler.OptPrintSourceTest.runBoth n
  (sparkleSynthDepth.set 0 : IO Unit)
  resetRefs
  let route : String := res.1
  let b : Sparkle.IR.AST.Module := res.2.1
  let d : Sparkle.IR.AST.Design := res.2.2
  let o := Sparkle.IR.Optimize.optimizeModule b
  let k := Sparkle.IR.OptCheck.checkedOptimize b
  let sb : Bool := Sparkle.IR.OptCheck.simpleBody b
  let sq : Bool := b.body.all Sparkle.IR.OptCheck.seqStmtOk
  let p0 : Bool := Sparkle.IR.PrintGuard.printOk b
  let rc : Bool := Sparkle.IR.RefineCheck.refineCheck b o
  let p1 : Bool := Sparkle.IR.PrintGuard.printOk o
  let same : Bool := k == b
  let p2 : Bool := Sparkle.IR.PrintGuard.printOk k
  let cand : Bool := Tests.Compiler.OptPrintGuardDefs.guardedOptimize b == k
  -- the writer's artifact of the returned design: the modules named as `b`
  let tops : List Sparkle.IR.AST.Module :=
    (Sparkle.Backend.Verilog.designArtifact d).filter (fun x => x.name == b.name)
  let topIsB : Bool := d.topModule == b.name
  let topsOk : Bool := tops.all Sparkle.IR.PrintGuard.printOk
  logInfo m!"GUARDFIRES SRC {n}: route={route} simpleBody b = {tf sb}; seqStmtOk-all = {tf sq}; stmts={b.body.length}; printOk b = {tf p0}; refineCheck b (opt b) = {tf rc}; printOk (opt b) = {tf p1}; checkedOptimize b == b: {tf same}; printOk (checkedOptimize b) = {tf p2}; equals guardedOptimize: {tf cand}. The returned design: topModule field = b's name: {tf topIsB}; modules of the writer's artifact named as b: {tops.length}, all printOk: {tf topsOk}"
  if sb then throwError "{n}: simpleBody is true — not the guarded branch"
  unless sq do throwError "{n}: not an assign + register body — not the guarded branch"
  unless p0 do throwError "{n}: printOk of the full entry's module is false"
  unless rc do throwError "{n}: refineCheck refuses the candidate — the print guard is not the conjunct that fails"
  if p1 then throwError "{n}: printOk of the candidate is true — the guard does not fire on this source"
  unless same do throwError "{n}: checkedOptimize did not return the input module"
  unless p2 do throwError "{n}: the shipped top does not pass printOk"
  unless cand do throwError "{n}: checkedOptimize differs from guardedOptimize"
  if topIsB && !tops.isEmpty && !topsOk then
    throwError "{n}: the writer's artifact has a top module that does not pass printOk"
  logInfo m!"GUARDFIRES SRC VERDICT: on the real source {n} the print guard FIRES; the shipped top is the unoptimised module of the full entry and passes printOk (on poc: the optimised module, printOk false). Whether the text equals the source is measured by scripts/shipping-coverage/optprint_sim.sh, not here"

end Tests.Compiler.OptPrintGuardFiresTest
