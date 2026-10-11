import Tests.Compiler.LegacyCacheRollbackTest

/-! # Does a real source fail late in an inline attempt and recover?

`LegacyCacheRollbackTest` shows, with an INJECTED fault, that an entry the
failed first attempt of `Rec.tryInlineUnfold` left in the expression cache is
honoured afterwards (a malformed module, and a well-formed module computing
another function). Whether that is reachable without injection depends on one
thing: a source whose inline attempt throws AFTER a cacheable sub-translation
returned, and whose compile then still succeeds (the reducible retry, or the
sub-module synthesis with connections that pass `instLinkCheck`).

docs/parallel/G2-legacy.md §11 enumerates the exceptions reachable inside the
attempt and argues, case by case, why the recovery then fails too — and names
the classes the argument does NOT close. This file measures one declaration
per class, with NO injection: the real entry, the real step tied like
`translateExprToWire`, every recursive call counted when it throws
(`inject .plain`, which rethrows). A declaration that compiles with a
non-zero count has failed somewhere and recovered: that is a natural trigger
candidate, and its module is checked like in the rollback test.

Each declaration is run with the default front end (the gates and the machine
route first, as shipped) and with the legacy front end. Nothing here throws;
the result is logged. `runNatural` is reusable on any declaration (the corpus).
An empty result bounds these classes on these sources; it is not a proof that
no source recovers. -/

open Lean Meta Sparkle.Compiler.Elab
open Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.Tests.Compiler.LegacyCacheRollbackTest

namespace Sparkle.Tests.Compiler.LegacyCacheNaturalTest

/-! ## Class 1: the failure is in the unfolded body itself

A binary node whose first operand (the cached helper call) translates and
whose second operand is unsupported. The sub-module synthesis lowers the same
body, the retry the same unfolding: expected REJECTED, no recovery. -/

/-- The second operand is an `if` under `map` (not synthesizable). -/
def badTail (y : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  y + y.map (fun v => if v = 0#8 then 1#8 else v)

@[reducible] def badTailR (y : Signal defaultDomain (BitVec 8)) :
    Signal defaultDomain (BitVec 8) :=
  y + y.map (fun v => if v = 0#8 then 1#8 else v)

def natBadTail (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  badTail (helperG x)

def natBadTailR (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  badTailR (helperG x)

/-! ## Class 2: the child compiles by a route the inlined body does not take

A sequential helper, untagged: as a module it is a state machine for the
entry; inlined, its `circuit do` is lowered by the legacy loop handlers inside
the parent's own `circuit do`, with an argument built from the parent's
register through a cacheable helper call. -/

def accU {dom : DomainConfig} (d : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  circuit do
    let c ← Signal.reg 0#8
    let cs := (c : Signal dom (BitVec 8))
    c <~ cs + d
    return cs

def natFsmInFsm (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg 0#8
    let rs := (r : Signal defaultDomain (BitVec 8))
    let k := accU (helperG rs)
    r <~ rs + k + x
    return rs

/-- The same with two register slots in the parent (the packed-state
lowering). -/
def natFsm2 (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let a ← Signal.reg (0#8)
    let b ← Signal.reg (0#8)
    let aS := (a : Signal defaultDomain (BitVec 8))
    let bS := (b : Signal defaultDomain (BitVec 8))
    let k := accU (helperG aS + bS)
    a <~ aS + k
    b <~ bS + x
    return aS

/-! ## Class 3: a helper the front end unfolds differently from the handler

A helper by structural recursion on literal data: the front end has its own
pass for it; the legacy handler goes through Lean's smart unfolding. -/

def sumList (z : Signal defaultDomain (BitVec 8)) :
    List (Signal defaultDomain (BitVec 8)) → Signal defaultDomain (BitVec 8)
  | [] => z
  | a :: rest => a + sumList z rest

def natRec (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  sumList x [helperG x, helperG x, x]

/-! ## The measurement -/

/-- The real entry on `decl`, with the real step and every recursive
translation counted when it throws. `cfe`: the certified front end (the
shipped default) or the legacy front end. -/
def runNatural (cfe : Bool) (decl : Name) : MetaM Run := do
  let fired ← IO.mkRef (0 : Nat)
  let fails ← IO.mkRef (0 : Nat)
  let tr : TranslateFn :=
    translateFuelFix
      (fun rec => translateStepWith translateFallback
        (inject Fault.plain (fun _ => false) fired fails rec)) 4096
  let outcome : Except String (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design) ←
    try
      let r ← synthesizeCombinationalCoreWith tr decl [] false (certifiedFrontEnd := cfe)
      pure (Except.ok r)
    catch ex =>
      let msg ← ex.toMessageData.toString
      pure (Except.error msg)
  let nFired ← fired.get
  let nFails ← fails.get
  return { outcome := outcome, fired := nFired, fails := nFails }

run_cmd Lean.Elab.Command.liftTermElabM do
  try
    let candidates : List (Name × Option (Nat → Nat)) :=
      [(``natBadTail, none), (``natBadTailR, none),
       (``natFsmInFsm, none), (``natFsm2, none),
       (``natRec, some (fun x => (4 * x + 2) % 256))]
    let mut lines : String := ""
    let mut recovered : String := ""
    for (decl, expected) in candidates do
      for cfe in [true, false] do
        let fe : String := if cfe then "default front end" else "legacy front end"
        let label : String := s!"{decl} [{fe}]"
        let rep := describe label expected (← runNatural cfe decl)
        lines := lines ++ s!"\n  {rep.text}"
        if !rep.rejected && rep.fails > 0 then
          let state : String := if rep.good then "clean" else "NOT CLEAN, see its line"
          recovered := recovered ++
            s!"\n  {label}: {rep.fails} failed recursive translations recovered from; module {state}"
    if recovered.isEmpty then
      logInfo m!"LEGACY CACHE, NATURAL TRIGGER: none — no candidate compiled after a failed recursive translation (each either compiled with no failure, or was rejected). This bounds the listed classes on these sources only.{lines}"
    else
      logInfo m!"LEGACY CACHE, NATURAL TRIGGER FOUND (a compile that failed inside and recovered, no injection):{recovered}\n\nRuns:{lines}"
  catch ex =>
    logInfo m!"LEGACY CACHE, NATURAL TRIGGER: harness error, no verdict: {ex.toMessageData}"

end Sparkle.Tests.Compiler.LegacyCacheNaturalTest
