import Sparkle.Compiler.Elab
import Sparkle.IR.Semantics
import Sparkle

/-! # The legacy expression cache across a caught failure

Question (docs/parallel/G2-legacy.md §2): the legacy caching shim
`Rec.translateExprToWireCached` returns the wire the `IO.Ref` map
`ctx.exprCache` holds for an expression, without checking the builder state.
A `try … catch` in `CompilerM` restores the builder state — wires,
`usedNames`, the name counter — but not the `IO.Ref`. `Rec.tryInlineUnfold`
catches a failed first attempt and goes on (the reducible retry, or the
sub-module synthesis in `Rec.handleDefinitionUnfold`). If the failed attempt
had translated a sub-expression, is the entry it left honoured afterwards?

What this file does. It runs the REAL entry
(`synthesizeCombinationalCoreWith`, legacy front end) on small declarations
with the REAL translator step (`translateStepWith translateFallback`), tied
by `translateFuelFix` exactly like `translateExprToWire`, except that every
recursive call goes through `inject`: a one-shot fault at the inline
attempt's own translation call (`tr eReduced` — recognised by the unfolded
expression's shape), raised

* `before` the call (nothing was translated: the attempt fails cleanly), or
* `after` it (the attempt translated its sub-expressions — they are in the
  cache — and then fails), or
* not at all (`plain`).

The fault stands for any exception raised late in an inline attempt. It is
INJECTED: this file does not exhibit a source whose attempt fails late by
itself (the natural candidates at the end are measured, with the number of
recursive translations that failed and were recovered from).

For every run the emitted module is checked: every name a statement or an
instance connection reads or drives is declared; every name read is an input
or driven; no name is driven twice; and, for the combinational cases, the
module's output — evaluated with the IR semantics `evalAssigns`, iterated to
a fixpoint — is the source function on sample inputs.

The test does not throw on a reproduced defect: it logs the verdict. -/

open Lean Meta Sparkle.Compiler.Elab
open Sparkle.Core.Domain Sparkle.Core.Signal

namespace Sparkle.Tests.Compiler.LegacyCacheRollbackTest

/-! ## Sources -/

/-- An untagged helper: its call is lowered by the legacy inline arm, and is
a cacheable `.other` expression for the caching shim. -/
def helperG (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  x + (Signal.pure 1#8 : Signal defaultDomain (BitVec 8))

/-- Not reducible: after a failed attempt there is no retry; the handler
synthesises it as a sub-module and translates the call's argument. -/
def helperF (y : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) := y + y

/-- Reducible: after a failed attempt the retry translates the same
unfolding again. -/
@[reducible] def helperFR (y : Signal defaultDomain (BitVec 8)) :
    Signal defaultDomain (BitVec 8) := y + y

/-- Reducible, the argument second: the wire of `helperG x` is allocated with
the hint of a second operand. -/
@[reducible] def helperFK (y : Signal defaultDomain (BitVec 8)) :
    Signal defaultDomain (BitVec 8) :=
  (Signal.pure 3#8 : Signal defaultDomain (BitVec 8)) + y

def parentSub (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  helperF (helperG x)

def parentRetry (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  helperFR (helperG x)

/-- After the helper call, a second operand whose result wire is allocated
with the hint of a second operand as well. -/
def parentRealloc (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  helperFK (helperG x) + (x + x)

def dbl (y : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) := y + y

def natDeep (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  dbl (dbl (dbl x))

/-- A sequential helper, untagged (the body of `ctr1` in
`ShippingCloseInstsCheckTest`). -/
def ctrU {dom : DomainConfig} (en : Signal dom Bool) : Signal dom (BitVec 8) :=
  circuit do
    let c ← Signal.reg 0#8
    let cs := (c : Signal dom (BitVec 8))
    c <~ Signal.mux en (cs + (Signal.pure 1#8 : Signal dom (BitVec 8))) cs
    return cs

def natCtr (en : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 8) :=
  ctrU (Signal.map (fun b => !b) en)

/-! ## The translator with a one-shot fault -/

inductive Fault where
  | plain
  | before
  | after

/-- `rec`, counting the calls that throw (and rethrowing); at the first call
on an expression `trigger` accepts, the fault. -/
def inject (fault : Fault) (trigger : Lean.Expr → Bool) (fired fails : IO.Ref Nat)
    (rec : TranslateFn) : TranslateFn := fun e hint top named => do
  let counted : CompilerM String := do
    try
      rec e hint top named
    catch ex =>
      CompilerM.liftMetaM (fails.modify (· + 1) : IO Unit)
      throw ex
  if trigger e then
    let n ← CompilerM.liftMetaM (fired.modifyGet fun n => (n, n + 1) : IO Nat)
    if n == 0 then
      match fault with
      | .plain => counted
      | .before =>
        CompilerM.liftMetaM (throwError "injected: failure before the attempt translated anything")
      | .after => do
        let _ ← counted
        CompilerM.liftMetaM (throwError "injected: failure after the attempt's sub-translations")
    else counted
  else counted

/-- The inline attempt's translation call in the sources above: the unfolded
helper body, a sum whose second operand is the call of `helperG`. -/
def sumOverG (e : Lean.Expr) : Bool :=
  e.isAppOfArity ``HAdd.hAdd 6 && (e.getAppArgs.back!).getAppFn.isConstOf ``helperG

structure Run where
  outcome : Except String (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)
  fired : Nat
  fails : Nat

/-- The real entry on `decl` (legacy front end: the certified gates and the
machine route are off, so the declaration takes the legacy arm of
`synthesizeFromConst`), with the real step under the fault. -/
def runWith (fault : Fault) (trigger : Lean.Expr → Bool) (decl : Name) : MetaM Run := do
  let fired ← IO.mkRef (0 : Nat)
  let fails ← IO.mkRef (0 : Nat)
  let tr : TranslateFn :=
    translateFuelFix
      (fun rec => translateStepWith translateFallback (inject fault trigger fired fails rec)) 4096
  let outcome : Except String (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design) ←
    try
      let r ← synthesizeCombinationalCoreWith tr decl [] false (certifiedFrontEnd := false)
      pure (Except.ok r)
    catch ex =>
      let msg ← ex.toMessageData.toString
      pure (Except.error msg)
  let nFired ← fired.get
  let nFails ← fails.get
  return { outcome := outcome, fired := nFired, fails := nFails }

/-! ## Checking an emitted module -/

partial def exprRefs : Sparkle.IR.AST.Expr → List String
  | .ref n => [n]
  | .op _ args => args.flatMap exprRefs
  | .concat args => args.flatMap exprRefs
  | .slice e _ _ => exprRefs e
  | .sliceDim e _ _ => exprRefs e
  | .index a i => exprRefs a ++ exprRefs i
  | .const _ _ => []

/-- The names a statement reads and the names it drives. An instance drives
what is connected to an output port of its module (looked up in the design)
and reads its other connections. Clock and reset names of registers and
memories are not collected. -/
def stmtUse (design : Sparkle.IR.AST.Design) :
    Sparkle.IR.AST.Stmt → List String × List String
  | .assign l r => (exprRefs r, [l])
  | .register out _ _ input _ => (exprRefs input, [out])
  | .memory _ _ _ _ wa wd we ra rd _ _ er =>
    (exprRefs wa ++ exprRefs wd ++ exprRefs we ++ exprRefs ra ++
        er.flatMap (fun p => exprRefs p.1),
      rd :: er.map (fun p => p.2))
  | .inst mn _ conns =>
    let outs : List String :=
      match design.modules.find? (fun c => c.name == mn) with
      | some c => c.outputs.map (fun p => p.name)
      | none => []
    (conns.flatMap (fun c => if outs.contains c.1 then [] else exprRefs c.2),
      conns.flatMap (fun c => if outs.contains c.1 then exprRefs c.2 else []))

structure Check where
  /-- read or driven, but not an input, an output or a wire of the module -/
  undeclared : List String
  /-- read, not an input, driven by no statement -/
  undriven : List String
  /-- driven by more than one statement -/
  multi : List String

def checkModule (m : Sparkle.IR.AST.Module) (d : Sparkle.IR.AST.Design) : Check :=
  let declared : List String := (m.inputs ++ m.outputs ++ m.wires).map (fun p => p.name)
  let inputs : List String := m.inputs.map (fun p => p.name)
  let uses : List (List String × List String) := m.body.map (stmtUse d)
  let reads : List String := (uses.flatMap (fun u => u.1)).eraseDups
  let drives : List String := uses.flatMap (fun u => u.2)
  { undeclared := ((reads ++ drives).eraseDups).filter (fun n => !declared.contains n),
    undriven := reads.filter (fun n => !inputs.contains n && !drives.contains n),
    multi := (drives.eraseDups).filter
      (fun n => Nat.blt 1 ((drives.filter (fun k => k == n)).length)) }

def Check.clean (c : Check) : Bool :=
  c.undeclared.isEmpty && c.undriven.isEmpty && c.multi.isEmpty

/-- The assignments, evaluated `k` times over (continuous assignments have no
order; the emitted order may read a name before the statement driving it). -/
def iterAssigns (we : Sparkle.IR.Semantics.WEnv) (body : List Sparkle.IR.AST.Stmt) :
    Nat → Sparkle.IR.Semantics.Env → Option Sparkle.IR.Semantics.Env
  | 0, env => some env
  | k + 1, env =>
    match Sparkle.IR.Semantics.evalAssigns we (fun _ _ => 0) body env with
    | some env' => iterAssigns we body k env'
    | none => none

/-- The value of the port `out` when the module's first input is `x` (every
other undriven name 0; widths as declared, 0 for an undeclared name). -/
def evalOut (m : Sparkle.IR.AST.Module) (x : Nat) : Option Nat :=
  let ports : List Sparkle.IR.AST.Port := m.inputs ++ m.outputs ++ m.wires
  let we : Sparkle.IR.Semantics.WEnv := fun n =>
    match ports.find? (fun p => p.name == n) with
    | some p => (p.ty.bitWidth?).getD 0
    | none => 0
  let inName : String :=
    match m.inputs with
    | p :: _ => p.name
    | [] => ""
  let env0 : Sparkle.IR.Semantics.Env := fun n => if n == inName then x else 0
  (iterAssigns we m.body (m.body.length + 1) env0).map (fun env => env "out")

structure Report where
  text : String
  /-- compiled, well formed, and the function is the source's (when asked) -/
  good : Bool
  rejected : Bool
  fired : Nat
  fails : Nat

def describe (label : String) (expected : Option (Nat → Nat)) (r : Run) : Report :=
  match r.outcome with
  | .error msg =>
    { text := s!"{label}: COMPILE REJECTED — {msg} [fault fired {r.fired}x, recursive failures {r.fails}]",
      good := false, rejected := true, fired := r.fired, fails := r.fails }
  | .ok (m, d) =>
    let c := checkModule m d
    let samples : List Nat := [0, 1, 5, 200]
    let bad : List String :=
      match expected with
      | none => []
      | some f =>
        samples.filterMap fun x =>
          match evalOut m x with
          | some got => if got == f x then none else some s!"x={x}: out={got}, source={f x}"
          | none => some s!"x={x}: not evaluable, source={f x}"
    let body : String := String.intercalate "; " (m.body.map (fun st => toString st))
    let fn : String :=
      match expected with
      | none => "function not evaluated"
      | some _ => if bad.isEmpty then s!"function = source on {samples}" else s!"FUNCTION DIFFERS {bad}"
    { text := s!"{label}: compiled; undeclared {c.undeclared}; read but undriven {c.undriven}; driven twice {c.multi}; {fn}; inputs {m.inputs.map (fun p => p.name)}; wires {m.wires.map (fun p => p.name)}; body [{body}] [fault fired {r.fired}x, recursive failures {r.fails}]",
      good := c.clean && bad.isEmpty, rejected := false, fired := r.fired, fails := r.fails }

/-- The verdict of one faulted scenario from its three runs. -/
def verdict (name : String) (plain before after : Report) : String :=
  if after.fired == 0 then
    s!"{name}: FAULT NOT REACHED — no translation call matched the inline attempt's shape; the dispatch differs from the reading, no verdict"
  else if !(plain.good && before.good) then
    s!"{name}: INCONCLUSIVE — a control run (no fault / fault before any translation) is not clean, see its line"
  else if after.good then
    s!"{name}: no stale hit: with the fault AFTER the attempt's sub-translations the module is still well formed (and computes the source function where evaluated)"
  else if after.rejected then
    s!"{name}: STALE HIT REPRODUCED, CAUGHT AS A REJECTION: the same source compiles when the attempt fails before translating anything, and is rejected when it fails after; see the message in the `after` line"
  else
    s!"{name}: STALE HIT REPRODUCED: the emitted module is malformed or computes another function when the attempt fails after its sub-translations, and is clean when it fails before; see the `after` line for the offending wire"

run_cmd Lean.Elab.Command.liftTermElabM do
  try
    let scenarios : List (String × Name × Option (Nat → Nat)) :=
      [("retry (reducible helper), argument used twice", ``parentRetry,
          some (fun x => (2 * (x + 1)) % 256)),
       ("retry, then a later operand allocated", ``parentRealloc,
          some (fun x => (3 + (x + 1) + 2 * x) % 256)),
       ("sub-module after a failed inline", ``parentSub, none)]
    let mut lines : String := ""
    let mut verdicts : String := ""
    for (name, decl, expected) in scenarios do
      let plainFn : Option (Nat → Nat) :=
        match expected with
        | some f => some f
        | none => some (fun x => (2 * (x + 1)) % 256)
      let plain := describe "no fault" plainFn (← runWith .plain sumOverG decl)
      let before := describe "fault before" expected (← runWith .before sumOverG decl)
      let after := describe "fault after" expected (← runWith .after sumOverG decl)
      lines := lines ++ s!"\n[{name}] ({decl})\n  {plain.text}\n  {before.text}\n  {after.text}"
      verdicts := verdicts ++ s!"\n  {verdict name plain before after}"
    logInfo m!"LEGACY CACHE ROLLBACK — verdicts (fault INJECTED at the inline attempt's translation call):{verdicts}\n\nRuns:{lines}"
  catch ex =>
    logInfo m!"LEGACY CACHE ROLLBACK: harness error, no verdict: {ex.toMessageData}"

/-! ## Natural candidates (no fault)

The same harness without a fault: does any recursive translation fail and
get recovered from by itself, and is the emitted module well formed? -/

run_cmd Lean.Elab.Command.liftTermElabM do
  try
    let candidates : List (Name × Option (Nat → Nat)) :=
      [(``natDeep, some (fun x => (8 * x) % 256)), (``natCtr, none)]
    let mut lines : String := ""
    let mut recovered : List Name := []
    for (decl, expected) in candidates do
      let r ← runWith .plain (fun _ => false) decl
      let rep := describe (toString decl) expected r
      lines := lines ++ s!"\n  {rep.text}"
      if !rep.rejected && rep.fails > 0 then recovered := recovered ++ [decl]
    logInfo m!"LEGACY CACHE ROLLBACK — natural candidates: compiled after at least one failed-and-recovered recursive translation: {recovered} (an empty list means none of these sources fails late by itself; it is not evidence that no source does).{lines}"
  catch ex =>
    logInfo m!"LEGACY CACHE ROLLBACK (natural candidates): harness error: {ex.toMessageData}"

end Sparkle.Tests.Compiler.LegacyCacheRollbackTest
