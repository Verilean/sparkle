import Sparkle.Compiler.Elab
import Sparkle

/-! # The inline attempt returns its failure: regression against the old cell

`Rec.tryInlineUnfold` replaced a local closure that kept the last inline
failure in an `IO.Ref`. Checked here, with a SCRIPTED translator (each call
returns a wire, throws an error, or throws an interrupt) and the old code
kept as a reference:

* the result, the failure that is kept (rendered) and the number of
  translator calls are the same as the old code's, in every case below;
* first attempt fails, retry (reducible unfolding) succeeds → the wire, no
  failure kept by the new code's success path (the old cell still held the
  first failure, which nothing read on success);
* first attempt fails and there is no retry (the reducible unfolding leaves
  the expression) → the FIRST failure is kept;
* both attempts fail → the SECOND failure is kept;
* an interrupt is not caught: it propagates after ONE call, no retry;
* end to end through `Rec.handleDefinitionUnfold`: both attempts and the
  sub-module synthesis fail → the terminal error with the kept failure
  rendered; the inline attempt fails and the sub-module synthesis succeeds →
  a wire and the child's module in the design.

Observations, diagnostics and the success domain — not world equality. -/

open Lean Meta Sparkle.Compiler.Elab
open Sparkle.Core.Domain Sparkle.Core.Signal

namespace Sparkle.Tests.Compiler.InlineUnfoldRegressionTest

/-- Unfolds at default transparency only. -/
def plainDef (n : Nat) : Nat := n + 1
/-- Unfolds at reducible transparency too. -/
@[reducible] def redDef (n : Nat) : Nat := n + 1
/-- A combinational declaration, not tagged as a hardware module. -/
def plainSig (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  x + (Signal.pure 1#8 : Signal defaultDomain (BitVec 8))

inductive Step | ok (w : String) | err (msg : String) | interrupt | runtime | wire8

/-- A translator following a script, counting its calls. -/
def scripted (ctr : IO.Ref Nat) (script : List Step) (made : Option (IO.Ref (List String)) := none) :
    TranslateFn := fun _ _ _ _ => do
  let n ← CompilerM.liftMetaM (ctr.modifyGet fun n => (n, n + 1) : IO Nat)
  match script[n]? with
  | some (.ok w) => pure w
  | some (.err msg) => CompilerM.liftMetaM (throwError msg)
  | some .interrupt => throw (Exception.internal Lean.interruptExceptionId)
  -- a real 8-bit wire of the circuit (an argument of an instance)
  | some .wire8 => do
    let w ← CompilerM.makeWire "arg" (.bitVector 8) false
    if let some r := made then CompilerM.liftMetaM (r.modify (· ++ [w]) : IO Unit)
    pure w
  -- a resource-limit exception (`Exception.isRuntime`): like an interrupt, a
  -- `catch` does not handle it
  | some .runtime => CompilerM.liftMetaM (Lean.throwMaxRecDepthAt .missing)
  | none => CompilerM.liftMetaM (throwError "script exhausted")

/-- The OLD inline attempt (with its cell), and what the cell holds after. -/
def oldTryInline (translateExprToWire : TranslateFn) (e : Lean.Expr) (hint : String)
    (isNamed : Bool) : CompilerM (Option String × Option Exception) := do
  let lastInlineFail : IO.Ref (Option Lean.Exception) ← IO.mkRef none
  let tryInline : CompilerM (Option String) := do
    let eReduced ← CompilerM.liftMetaM do
      match ← Lean.Meta.unfoldDefinition? e with
        | some e' => return e'
        | none => return e
    if eReduced != e then
      try
        let w ← translateExprToWire eReduced hint false isNamed
        return some w
      catch ex1 =>
        lastInlineFail.set (some ex1)
        try
          let eReduced2 ← CompilerM.liftMetaM do
            Lean.Meta.withTransparency .reducible do
              match ← Lean.Meta.unfoldDefinition? e with
              | some e' => return e'
              | none => return e
          if eReduced2 != e then
            let w ← translateExprToWire eReduced2 hint false isNamed
            return some w
          else
            return none
        catch ex2 =>
          lastInlineFail.set (some ex2)
          return none
    else
      return none
  let r ← tryInline
  return (r, ← lastInlineFail.get)

/-- Run a `CompilerM` action from a fresh state. -/
def runC {α : Type} (c : CompilerM α) : MetaM (α × Sparkle.IR.Builder.CircuitState) := do
  let cacheRef ← IO.mkRef ({} : Lean.ExprStructMap String)
  (c.run (entryCompilerState false cacheRef)).run (Sparkle.IR.Builder.CircuitM.init "regress")

/-- Run `x` and return its outcome, INCLUDING an interrupt. A `try … catch`
in `MetaM` does not catch an interrupt (`Core.tryCatch` rethrows it) — which
is the very behaviour under test — so the outcome is taken below the
exception layer. -/
def outcome {α : Type} (x : MetaM α) : MetaM (Except Exception α) := do
  let mctx ← readThe Meta.Context
  let ms ← getThe Meta.State
  let cctx ← readThe Core.Context
  let cs ← getThe Core.State
  match ← ((x.run mctx ms).run cctx cs).toBaseIO with
  | .ok ((a, ms'), cs') => set cs'; set ms'; pure (.ok a)
  | .error e => pure (.error e)

/-- What a run shows: the wire, the kept failure rendered, a thrown error
rendered (or `interrupt`), and the number of translator calls. -/
structure Obs where
  wire : Option String
  kept : Option String
  thrown : Option String
  calls : Nat
  deriving BEq, Repr

def observe (f : TranslateFn → Lean.Expr → String → Bool → CompilerM (Option String × Option Exception))
    (script : List Step) (e : Lean.Expr) : MetaM Obs := do
  let ctr ← IO.mkRef 0
  match ← outcome (runC (f (scripted ctr script) e "h" false)) with
  | .ok ((w, ex?), _) =>
    let kept ← ex?.mapM fun ex => ex.toMessageData.toString
    return { wire := w, kept, thrown := none, calls := ← ctr.get }
  | .error ex =>
    let t ← if ex.isInterrupt then pure "interrupt" else if ex.isRuntime then pure "runtime"
      else ex.toMessageData.toString
    return { wire := none, kept := none, thrown := some t, calls := ← ctr.get }

def plainE : Lean.Expr := mkApp (mkConst ``plainDef) (mkNatLit 1)
def redE : Lean.Expr := mkApp (mkConst ``redDef) (mkNatLit 1)

run_cmd Lean.Elab.Command.liftTermElabM do
  let new := fun tr e h n => Rec.tryInlineUnfold (fun e h t n => tr e h t n) e h n
  let cases : List (String × List Step × Lean.Expr) :=
    [("first attempt succeeds", [.ok "w1"], plainE),
     ("no unfolding: no attempt", [], mkSort levelZero),
     ("fail, no retry (reducible unfolding leaves it)", [.err "A"], plainE),
     ("fail, retry succeeds", [.err "A", .ok "w2"], redE),
     ("fail, retry fails", [.err "A", .err "B"], redE),
     ("interrupt at the first attempt", [.interrupt, .ok "w2"], redE),
     ("fail, interrupt at the retry", [.err "A", .interrupt], redE),
     ("runtime exception at the first attempt", [.runtime, .ok "w2"], redE),
     ("fail, runtime exception at the retry", [.err "A", .runtime], redE)]
  let mut lines : MessageData := m!""
  for (what, script, e) in cases do
    let o ← observe oldTryInline script e
    let n ← observe new script e
    -- on success the old cell may still hold the first failure, which
    -- nothing read: compare the kept failure only when no wire came back
    let same := o.wire == n.wire && o.thrown == n.thrown && o.calls == n.calls &&
      (o.wire.isSome || o.kept == n.kept)
    unless same do throwError "{what}: old {repr o} / new {repr n}"
    lines := lines ++ m!"\n  {what}: wire {n.wire}, kept {n.kept}, thrown {n.thrown}, calls {n.calls}"
  -- the expected outcomes themselves (not only agreement)
  let exp (script : List Step) (e : Lean.Expr) (want : Obs) : MetaM Unit := do
    let n ← observe new script e
    unless n == want do throwError "expected {repr want}, got {repr n}"
  exp [] (mkSort levelZero) { wire := none, kept := none, thrown := none, calls := 0 }
  exp [.err "A"] plainE { wire := none, kept := some "A", thrown := none, calls := 1 }
  exp [.err "A", .ok "w2"] redE { wire := some "w2", kept := none, thrown := none, calls := 2 }
  exp [.err "A", .err "B"] redE { wire := none, kept := some "B", thrown := none, calls := 2 }
  exp [.interrupt, .ok "w2"] redE { wire := none, kept := none, thrown := some "interrupt", calls := 1 }
  exp [.err "A", .interrupt] redE { wire := none, kept := none, thrown := some "interrupt", calls := 2 }
  exp [.runtime, .ok "w2"] redE { wire := none, kept := none, thrown := some "runtime", calls := 1 }
  exp [.err "A", .runtime] redE { wire := none, kept := none, thrown := some "runtime", calls := 2 }
  logInfo m!"INLINE ATTEMPT vs THE OLD CELL: same wire, kept failure, thrown error and translator calls in {cases.length} scripted cases; first failure kept without a retry, second failure kept when the retry fails, an interrupt and a runtime (resource-limit) exception propagate without a retry (first attempt) and from the retry — the two branches `Core.tryCatch` does not handle.{lines}"

/-- The handler, end to end, with a scripted translator. -/
structure Inst where
  module : String
  /-- the names its connections read -/
  refs : List String
  deriving Repr

def runHandlerX (script : List Step) (e : Lean.Expr) (name : Name) :
    MetaM (Except String (Option String × List String × List Inst × List String) × Nat) := do
  let ctr ← IO.mkRef 0
  let made ← IO.mkRef ([] : List String)
  match ← outcome (runC (Rec.handleDefinitionUnfold
      (fun e h t n => scripted ctr script (some made) e h t n) e name e.getAppArgs "h" false)) with
  | .ok (r, st) =>
    let insts := st.module.body.filterMap fun s => match s with
      | .inst mn _ conns => some { module := mn, refs := conns.filterMap fun c => match c.2 with
          | .ref x => some x | _ => none : Inst }
      | _ => none
    return (.ok (r, st.design.modules.map (·.name), insts, ← made.get), ← ctr.get)
  | .error ex =>
    let t ← if ex.isInterrupt then pure "interrupt" else if ex.isRuntime then pure "runtime"
      else ex.toMessageData.toString
    return (.error t, ← ctr.get)

def runHandler (script : List Step) (e : Lean.Expr) (name : Name) :
    MetaM (Except String (Option String × List String) × Nat) := do
  let ctr ← IO.mkRef 0
  match ← outcome (runC (Rec.handleDefinitionUnfold (fun e h t n => scripted ctr script none e h t n)
      e name e.getAppArgs "h" false)) with
  | .ok (r, st) => return (.ok (r, st.design.modules.map (·.name)), ← ctr.get)
  | .error ex =>
    let t ← if ex.isInterrupt then pure "interrupt" else if ex.isRuntime then pure "runtime"
      else ex.toMessageData.toString
    return (.error t, ← ctr.get)

run_cmd Lean.Elab.Command.liftTermElabM do
  let has (s sub : String) : Bool := (s.splitOn sub).length > 1
  -- both attempts fail, and the sub-module synthesis fails: the terminal
  -- error renders the SECOND failure
  let (r, calls) ← runHandler [.err "FIRST", .err "SECOND"] redE ``redDef
  match r with
  | .error msg =>
    unless has msg "Cannot synthesise" && has msg "not inlinable and not a hardware module" &&
        has msg "Inline expansion failed with:\nSECOND" && !has msg "FIRST" && calls == 2 do
      throwError "both fail: {calls} calls, message:\n{msg}"
  | .ok _ => throwError "both fail: the handler returned"
  -- no retry: the terminal error renders the FIRST failure
  let (r, calls) ← runHandler [.err "FIRST"] plainE ``plainDef
  match r with
  | .error msg =>
    unless has msg "Inline expansion failed with:\nFIRST" && calls == 1 do
      throwError "no retry: {calls} calls, message:\n{msg}"
  | .ok _ => throwError "no retry: the handler returned"
  -- an interrupt is not turned into the terminal error
  let (r, calls) ← runHandler [.interrupt] redE ``redDef
  match r with
  | .error msg =>
    if msg != "interrupt" || calls != 1 then
      throwError "interrupt: {calls} calls, message:\n{msg}"
  | .ok _ => throwError "interrupt: the handler returned"
  -- nor is a runtime exception
  let (r, calls) ← runHandler [.runtime] redE ``redDef
  match r with
  | .error msg =>
    if msg != "runtime" || calls != 1 then
      throwError "runtime exception: {calls} calls, message:\n{msg}"
  | .ok _ => throwError "runtime exception: the handler returned"
  logInfo m!"HANDLER DIAGNOSTICS: both attempts and the sub-module fail → 'Cannot synthesise … Inline expansion failed with' the SECOND failure; no retry → the FIRST; an interrupt and a runtime exception propagate (no terminal error, one call)"

end Sparkle.Tests.Compiler.InlineUnfoldRegressionTest

namespace Sparkle.Tests.Compiler.InlineUnfoldRegressionTest
open Lean Meta Sparkle.Compiler.Elab
open Sparkle.Core.Domain Sparkle.Core.Signal

-- the inline attempt fails, the sub-module synthesis succeeds: the handler
-- goes on to instantiate the child (its module is added to the design)
run_cmd Lean.Elab.Command.liftTermElabM do
  let sigT ← mkAppM ``Signal #[mkConst ``defaultDomain, ← mkAppM ``BitVec #[mkNatLit 8]]
  withLocalDeclD `x sigT fun x => do
    let e := mkApp (mkConst ``plainSig) x
    let (r, calls) ← runHandlerX ([.err "INLINE"] ++ List.replicate 8 .wire8) e ``plainSig
    match r with
    | .ok (w, mods, insts, made) =>
      let isChild (m : String) : Bool := (m.splitOn "plainSig").length > 1
      -- a wire came back; the design has the child ONCE; the body has exactly
      -- one instance, of the child, reading the argument wire the translator
      -- made and driving the wire that came back
      let some rw := w | throwError "sub-module success: no wire came back"
      unless (mods.filter isChild).length == 1 do
        throwError "sub-module success: the child's module in the design: {mods}"
      let [i] := insts | throwError "sub-module success: instances {repr insts}"
      unless isChild i.module && made.length == 1 && made.all (i.refs.contains ·) &&
          i.refs.contains rw && calls == 2 do
        throwError "sub-module success: instance {repr i}, argument wires {made}, result {rw}, {calls} calls"
      logInfo m!"HANDLER, SUB-MODULE AFTER A FAILED INLINE: result {rw}; the design has the child once ({mods}); one instance, of the child, connected to the argument wire {made} and to the result wire ({repr i}); {calls} translator calls. (One case — not a proof about the success domain.)"
    | .error msg => throwError "sub-module success: the handler threw after {calls} calls:\n{msg}"

end Sparkle.Tests.Compiler.InlineUnfoldRegressionTest
