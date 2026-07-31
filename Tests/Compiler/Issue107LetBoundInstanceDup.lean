/-
  Regression test for Issue #107: a stateful `@[hardware_module]`
  bound with `let` inside a `circuit do` body was emitted once per
  elaboration pass — E = I · (D + 1) instances (I = let-bound
  instances, D = distinct register next-state expressions) instead
  of I.  Named translations bypass the structural `exprCache`, and
  the single-output instance path had no idempotency guard (the
  Issue #71 guard only covers the multi-output projection path).

  Fixed by `sparkleSingleOutInstanceCache` in
  `Sparkle/Compiler/Elab.lean`, keyed on parent module + child
  module + input connections.

  The three cases mirror the issue's minimal repro:
  - `oneInstance`    — 1 let-bound toggle:  was 2 instances, must be 1
  - `threeInstances` — 3 let-bound toggles: was 12 instances, must be 3
    (also guards the key granularity: folding `toggle e0/e1/e2`
    into fewer than 3 instances would be a miscompile)
  - `controlInline`  — inlined call, always worked: must stay 1
-/
import Sparkle
import Sparkle.Compiler.Elab

namespace Sparkle.Tests.Compiler.Issue107LetBoundInstanceDup

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-- Stateful sub-module: a 1-bit register that flips when `en` is high. -/
@[hardware_module]
def toggle {dom : DomainConfig} (en : Signal dom Bool) : Signal dom Bool :=
  Signal.loop fun (s : Signal dom Bool) =>
    Signal.register false (Signal.mux en (~~~s) s)

/-- One let-bound instantiation. -/
@[hardware_module]
def oneInstance {dom : DomainConfig} (en : Signal dom Bool) : Signal dom Bool := circuit do
  let r0 ← Signal.reg false
  let t := toggle en
  r0 <~ t
  return (r0 : Signal dom Bool)

/-- Three distinct let-bound instantiations (distinct args — must NOT fold). -/
@[hardware_module]
def threeInstances {dom : DomainConfig} (e0 e1 e2 : Signal dom Bool) : Signal dom Bool := circuit do
  let r0 ← Signal.reg false
  let r1 ← Signal.reg false
  let r2 ← Signal.reg false
  let a := toggle e0
  let b := toggle e1
  let c := toggle e2
  r0 <~ a
  r1 <~ b
  r2 <~ c
  return ((r0 : Signal dom Bool) &&& (r1 : Signal dom Bool) &&& (r2 : Signal dom Bool))

/-- Control — same as `oneInstance` but the call is inlined, not let-bound. -/
@[hardware_module]
def controlInline {dom : DomainConfig} (en : Signal dom Bool) : Signal dom Bool := circuit do
  let r0 ← Signal.reg false
  r0 <~ toggle en
  return (r0 : Signal dom Bool)

/-- Router variant (the NoC `router5` shape): the sub-module call's
    argument goes through a `let` whose value reads register state.
    Each elaboration re-walk then materialises the argument cone under
    fresh fvars, so the elaborator-side instance guard cannot fire
    (the connections differ textually per walk) — only the IR-level
    CSE + instance-merge pass folds these. -/
@[hardware_module]
def stateArg {dom : DomainConfig} (en : Signal dom Bool) : Signal dom Bool := circuit do
  let r0 ← Signal.reg false
  let r1 ← Signal.reg false
  let g := (r0 : Signal dom Bool) &&& en
  let t := toggle g
  r1 <~ t
  r0 <~ en
  return (r1 : Signal dom Bool)

/-- Two-input stateful sub-module (uses BOTH inputs). -/
@[hardware_module]
def stage {dom : DomainConfig} (ctrl data : Signal dom Bool) : Signal dom Bool :=
  Signal.loop fun (s : Signal dom Bool) =>
    Signal.register false (Signal.mux ctrl (data ^^^ s) s)

/-- Chained instances — the case the duplicate-instance merge must NOT
    fold.  Two `stage` instances share `ctrl = en` but take their `data`
    from two DIFFERENT upstream `toggle` instances (`u0`/`u1`), i.e. the
    differing input is *instance-driven*.  The merge's driven-elsewhere
    heuristic misclassifies that input as an output and drops it from the
    key, so without the chain-safety gate the two distinct `stage`s fold
    into one — a miscompile (`r1` would then read `u0`'s data instead of
    `u1`'s).  Correct optimized count: 2 stage + 2 toggle. -/
@[hardware_module]
def chainedStages {dom : DomainConfig} (e0 e1 en : Signal dom Bool) : Signal dom Bool := circuit do
  let u0 := toggle e0
  let u1 := toggle e1
  let b0 := stage en u0
  let b1 := stage en u1
  let r0 ← Signal.reg false
  let r1 ← Signal.reg false
  r0 <~ b0
  r1 <~ b1
  return ((r0 : Signal dom Bool) &&& (r1 : Signal dom Bool))

open Lean Elab Command in
/-- Synthesize `id` and assert its module body contains exactly `n`
    sub-module instantiations.  Fails elaboration (and hence the
    build) on mismatch. -/
elab "#assertInstCount" id:ident n:num : command => do
  let declName ← liftCoreM (Lean.resolveGlobalConstNoOverload id)
  liftTermElabM do
    let (module, _) ← Sparkle.Compiler.Elab.synthesizeCombinational declName
    let count := module.body.filter (fun s => match s with
      | Sparkle.IR.AST.Stmt.inst .. => true
      | _ => false) |>.length
    unless count == n.getNat do
      throwError "Issue #107 regression: expected {n.getNat} sub-module instance(s) in {declName}, found {count}"

open Lean Elab Command in
/-- Like `#assertInstCount`, but counts instances AFTER the IR
    optimizer (what actually reaches the emitted Verilog) — this is
    what exercises the CSE + duplicate-instance-merge pass. -/
elab "#assertInstCountOptimized" id:ident n:num : command => do
  let declName ← liftCoreM (Lean.resolveGlobalConstNoOverload id)
  liftTermElabM do
    let (module, _) ← Sparkle.Compiler.Elab.synthesizeCombinational declName
    let optimized := Sparkle.IR.Optimize.optimizeModule module
    let count := optimized.body.filter (fun s => match s with
      | Sparkle.IR.AST.Stmt.inst .. => true
      | _ => false) |>.length
    unless count == n.getNat do
      throwError "Issue #107 regression: expected {n.getNat} optimized sub-module instance(s) in {declName}, found {count}"

-- Elaborator-side guard (pre-optimizer): pass-stable connections
-- must dedupe during elaboration.
#assertInstCount oneInstance 1
#assertInstCount threeInstances 3
#assertInstCount controlInline 1

-- Netlist contract (post-optimizer): what ships to Verilog.  The
-- threeInstances case also guards against over-merging — its three
-- calls take distinct arguments and must all survive.
#assertInstCountOptimized oneInstance 1
#assertInstCountOptimized threeInstances 3
#assertInstCountOptimized controlInline 1
#assertInstCountOptimized stateArg 1
-- Soundness guard: chained instances whose only differing input is
-- driven by another instance must NOT be merged (2 distinct stages,
-- plus the 2 distinct upstream toggles = 4 instances).
#assertInstCountOptimized chainedStages 4

def main : IO Unit := do
  IO.println "Issue107LetBoundInstanceDup: build-only regression test."
  IO.println "  ✓ oneInstance    emits exactly 1 toggle instance (was 2)"
  IO.println "  ✓ threeInstances emits exactly 3 toggle instances (was 12)"
  IO.println "  ✓ controlInline  emits exactly 1 toggle instance"
  IO.println "  ✓ stateArg       optimizes to exactly 1 toggle instance (router variant)"
  IO.println "  ✓ chainedStages  keeps 4 instances (2 stage + 2 toggle) — chain not mis-merged"

end Sparkle.Tests.Compiler.Issue107LetBoundInstanceDup
