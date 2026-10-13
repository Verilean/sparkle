import Tests.Compiler.LegacyCacheRollbackTest

/-! # Acceptance scenarios for the cache fix (variant A: snapshot / restore)

To be run on the branch that applies `docs/parallel/G2-cache-fix.patch`
(variant A: `Rec.tryInlineUnfold` snapshots the wire-naming `IO.Ref` caches
before its attempt and restores them in both `catch` branches). On the
unfixed compiler the same file runs and reports the defect; it never throws.

Each scenario is the real entry (`synthesizeCombinationalCoreWith`, legacy
front end) with the real step, a fault injected AFTER chosen translation
calls (`injectAt`), and the emitted module checked as in
`LegacyCacheRollbackTest` (declared / driven / driven once; `out` evaluated
against the source function where the module is combinational and flat).
A line starts with `PASS` (compiled, well formed, the source's function) or
`FAIL`.

1. **Retry, argument used twice** (`parentRetry`) and
2. **retry, then a later operand allocated** (`parentRealloc`): the two
   injected scenarios that reproduce the defect today. After the fix: PASS.
3. **Sub-module after a failed attempt** (`parentSub`): today rejected by
   `instLinkCheck` (a stale, undeclared argument wire). After the fix: PASS
   (structure only: the instance is not evaluated).
4. **Nested attempts, the inner one fails late** (`parentNested`): an inline
   attempt inside an inline attempt; the inner attempt's translation fails
   after its sub-translations, its retry succeeds, the outer attempt goes on
   and reads the cache.
5. **Nested attempts, both fail late**: the inner fails and recovers, then
   the outer fails after everything and recovers — two restores, the outer
   one to a snapshot OLDER than the inner one's.
6. **A child synthesis between snapshot and restore** (`parentChild`): the
   failed attempt contains a call of a tagged child, so the child's entry
   runs inside it. What the nested entry writes, from
   `synthesizeCombinationalCoreWith`:
   * `sparkleChildCache`, `sparkleSubModuleCache` (the child's result):
     NOT among the restored refs — the child stays compiled; the retry's
     call is a cache hit of the entry;
   * `sparkleFvarValueMap`, `sparkleWireWidthCache`: set to `{}` on entry
     and put back by the entry's own `finally` — net effect none;
   * `sparkleLetWireCache`, `sparkleLoopWireCache`, `sparkleWireCanon`: set
     to `{}` on entry and NOT put back. So today a child's synthesis already
     empties the parent's let / loop / canon caches for the rest of the
     parent's module. The restore puts back the entries of the snapshot —
     entries that name wires of the parent as it was at the snapshot, which
     is the builder state the `catch` returns to. This IS observable in
     principle: after a recovered failure that contained a child synthesis,
     a later `let` or loop of the parent equal to an earlier one is shared
     again where today it is lowered a second time. It is the pre-attempt
     state restored, not a new behaviour; but the emitted text of such a
     compile can differ from today's;
   * `sparkleSingleOutInstanceCache`, `sparkleSubInstanceOutputs`: entries
     keyed by the CHILD's module name / call keys of the child's own
     instances; the restore drops the ones written during the attempt. The
     child is not walked again (its result is cached), so nothing reads them.
   The scenario checks the compile and the module's structure.
7. **The zeta mark** (`sparkleFvarZetaVisited`): the body's zeta arm marks a
   variable, translates its value and erases the mark — with no `finally`.
   The scenario runs the REAL arm on a let-bound variable with a translator
   that throws, inside the REAL `Rec.tryInlineUnfold` (whose retry then
   succeeds), and reads the ref: today the mark is still there (every later
   reference to that variable throws "circular zeta-reduction"; the ref is
   never cleared, not even at the start of the next top-level synthesis);
   after the fix the restore removed it. The test erases the mark itself at
   the end.

Not covered: `sparkleLetWireCache` / `sparkleLoopWireCache` stale hits (same
mechanism, no scenario here), a natural trigger (none is known), the full
corpus. -/

open Lean Meta Sparkle.Compiler.Elab
open Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.Tests.Compiler.LegacyCacheRollbackTest

namespace Sparkle.Tests.Compiler.LegacyCacheFixTest

/-! ## Sources -/

/-- Reducible, and its body calls another reducible helper on its argument:
an inline attempt inside an inline attempt. -/
@[reducible] def outerHR (y : Signal defaultDomain (BitVec 8)) :
    Signal defaultDomain (BitVec 8) := helperFR y + y

def parentNested (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  outerHR (helperG x)

/-- A tagged child. -/
@[hardware_module]
def kid (y : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) := y + y

/-- Reducible; its body instantiates the child on the argument. -/
@[reducible] def helperFT (y : Signal defaultDomain (BitVec 8)) :
    Signal defaultDomain (BitVec 8) := kid y + y

def parentChild (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  helperFT (helperG x)

/-- Unfolds at reducible transparency too (for the zeta scenario). -/
@[reducible] def redNat (n : Nat) : Nat := n + 1

/-! ## A fault after chosen calls -/

/-- `rec`; on the `n`-th call (from 0) whose expression `trigger` accepts,
with `n ∈ afterAt`: run `rec`, then throw. -/
def injectAt (afterAt : List Nat) (trigger : Lean.Expr → Bool) (fired : IO.Ref Nat)
    (rec : TranslateFn) : TranslateFn := fun e hint top named => do
  if trigger e then
    let n ← CompilerM.liftMetaM (fired.modifyGet fun n => (n, n + 1) : IO Nat)
    if afterAt.contains n then
      let _ ← rec e hint top named
      CompilerM.liftMetaM (throwError "injected: failure after the attempt's sub-translations")
    else rec e hint top named
  else rec e hint top named

/-- The real entry on `decl` (legacy front end) with the real step under
`injectAt`. -/
def runAt (afterAt : List Nat) (trigger : Lean.Expr → Bool) (decl : Name) : MetaM Run := do
  let tenv ← Lean.getEnv
  let fired ← IO.mkRef (0 : Nat)
  let tr : TranslateFn :=
    translateFuelFix
      (fun rec => translateStepWith (translateFallback tenv) (injectAt afterAt trigger fired rec)) 4096
  let outcome : Except String (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design) ←
    try
      let r ← synthesizeCombinationalCoreWith (fun _ => tr) decl [] false (certifiedFrontEnd := false)
      pure (Except.ok r)
    catch ex =>
      let msg ← ex.toMessageData.toString
      pure (Except.error msg)
  let nFired ← fired.get
  return { outcome := outcome, fired := nFired, fails := 0 }

/-- One scenario's line. -/
def scenario (title : String) (afterAt : List Nat) (decl : Name)
    (expected : Option (Nat → Nat)) : MetaM String := do
  let rep := describe title expected (← runAt afterAt sumOverG decl)
  let faults : Nat := afterAt.length
  if rep.fired < faults then
    return s!"NO VERDICT ({title}): only {rep.fired} matching call(s), {faults} fault(s) wanted — the dispatch differs from the reading\n    {rep.text}"
  else if rep.good then
    return s!"PASS  {rep.text}"
  else
    return s!"FAIL  {rep.text}"

run_cmd Lean.Elab.Command.liftTermElabM do
  try
    let double : Nat → Nat := fun x => (2 * (x + 1)) % 256
    let l1 ← scenario "1 retry, argument used twice" [0] ``parentRetry (some double)
    let l2 ← scenario "2 retry, then a later operand allocated" [0] ``parentRealloc
      (some (fun x => (3 + (x + 1) + 2 * x) % 256))
    let l3 ← scenario "3 sub-module after a failed attempt" [0] ``parentSub none
    let l4 ← scenario "4 nested attempts, the inner fails late" [1] ``parentNested
      (some (fun x => (3 * (x + 1)) % 256))
    let l5 ← scenario "5 nested attempts, both fail late" [0, 1] ``parentNested
      (some (fun x => (3 * (x + 1)) % 256))
    let l6 ← scenario "6 a child synthesis inside the failed attempt" [0] ``parentChild none
    logInfo m!"LEGACY CACHE FIX, scenarios 1–6 (fault INJECTED; PASS = compiled, well formed, the source's function where evaluated):\n  {l1}\n  {l2}\n  {l3}\n  {l4}\n  {l5}\n  {l6}"
  catch ex =>
    logInfo m!"LEGACY CACHE FIX, scenarios 1–6: harness error, no verdict: {ex.toMessageData}"

/-! ## The zeta mark -/

/-- Run a `CompilerM` action from a fresh builder state. -/
def runFresh {α : Type} (c : CompilerM α) :
    MetaM (α × Sparkle.IR.Builder.CircuitState) := do
  let cacheRef ← IO.mkRef ({} : Lean.ExprStructMap String)
  (c.run (entryCompilerState false cacheRef)).run (Sparkle.IR.Builder.CircuitM.init "zeta")

run_cmd Lean.Elab.Command.liftTermElabM do
  try
    let natT := mkConst ``Nat
    let verdict ← withLetDecl `zv natT (mkNatLit 1) fun fv => do
      let n := fv.fvarId!.name
      let before := (← (sparkleFvarZetaVisited.get : IO _)).contains n
      let calls ← IO.mkRef (0 : Nat)
      -- call 0: the REAL zeta arm on the let-bound variable, whose value's
      -- translation throws; call 1 (the retry): a wire
      let tr : TranslateFn := fun _ hint _ _ => do
        let k ← CompilerM.liftMetaM (calls.modifyGet fun k => (k, k + 1) : IO Nat)
        if k == 0 then
          Rec.translateExprToWireImpl
            (fun _ _ _ _ => CompilerM.liftMetaM (throwError "the value does not translate"))
            fv hint false false
        else pure "w_retry"
      let e := mkApp (mkConst ``redNat) (mkNatLit 1)
      let (r, _) ← runFresh (Rec.tryInlineUnfold tr e "h" false)
      let after := (← (sparkleFvarZetaVisited.get : IO _)).contains n
      -- leave the global ref as it was
      (sparkleFvarZetaVisited.modify (·.erase n) : IO Unit)
      let nCalls ← calls.get
      let state : String :=
        if nCalls < 2 then
          s!"NO VERDICT: {nCalls} translator call(s) — the retry did not run (wire {r.1})"
        else if before then "NO VERDICT: the variable was marked before the run"
        else if after then
          "FAIL  the mark of the let-bound variable is still in sparkleFvarZetaVisited after the recovered failure (the leak; expected on the unfixed compiler)"
        else "PASS  the mark is gone after the recovered failure"
      pure s!"{state} [wire {r.1}, {nCalls} translator calls]"
    logInfo m!"LEGACY CACHE FIX, scenario 7 (the zeta mark; the real zeta arm fails inside the real Rec.tryInlineUnfold, whose retry succeeds): {verdict}"
  catch ex =>
    logInfo m!"LEGACY CACHE FIX, scenario 7: harness error, no verdict: {ex.toMessageData}"

end Sparkle.Tests.Compiler.LegacyCacheFixTest
