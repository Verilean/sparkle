/-
  Sparkle.Core.CircuitDo — circuit-flavoured `do` block on top of
  the v2 Circuit monad.

  Same surface syntax as the `Signal.circuit do` macro
  (`Sparkle/Core/Signal.lean`): statement-level register
  declarations, `<~` updates, branch-local `let _ := _`,
  statement-level `if cond then … else …` over a Signal Bool,
  and `return`.  The lowering is different:

    * `Signal.circuit do` flattens everything to a single
      `Signal.loop fun _ => bundleAll! [...]` and projects
      registers out by `projN!`.
    * `circuit do` (this file) compiles each register declaration
      to the matching `runCircuit{N}` arity and threads register
      updates through the v2 `Circuit` monad's `Bind.bind` /
      `Pure.pure`, all of which the elaborator now recognises
      thanks to `handleCircuitMonad`.

  The two forms produce semantically-identical Verilog and
  cycle-by-cycle output.  `circuit do` exists so the v2 monad
  surface is at usability parity with the legacy macro, so the
  legacy macro can be retired without UX regressions.

  Migration: replace `Signal.circuit do { … }` with
  `circuit do { … }`.  Body content is unchanged.  The only
  visible diff is the leading keyword.
-/

import Sparkle.Core.Signal
import Sparkle.Core.CircuitMonad

namespace Sparkle.Core

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ### Syntax category for circuit-do statements.

    Mirrors `circuitStmt` from `Signal.lean` so the macro
    flattener logic transfers verbatim, but lowering emits
    `Circuit.next` calls inside a v2 `Circuit dom S _`
    expression instead of macro-managed `bundleAll!` rows. -/

declare_syntax_cat cdoStmt

/-- `let r ← Signal.reg init` — declares one register. -/
syntax "let " ident " ← " "Signal.reg " (colGt term) (";")? : cdoStmt

/-- `r <~ rhs` — schedules the next-cycle value for register `r`. -/
syntax ident " <~ " (colGt term) (";")? : cdoStmt

/-- `let x := expr` — branch-local Lean value binding. -/
syntax "let " ident " := " (colGt term) (";")? : cdoStmt

/-- `return expr` — produces the circuit's output Signal. -/
syntax "return " (colGt term) (";")? : cdoStmt

/-- Statement-level `if cond then … else …` over a Signal Bool.
    Both branches use the same `cdoStmt` grammar; the macro
    lowers them by merging per-register `<~` rows with
    `Signal.mux cond thenRhs elseRhs`.  A register assigned in
    only one branch holds its current value on the other side. -/
syntax "if " (colGt term) " then" withPosition((colGe cdoStmt)*)
       "else" withPosition((colGe cdoStmt)*) : cdoStmt

/-- The top-level `circuit do { … }` term.  Wraps a sequence of
    `cdoStmt`s, lowering to the appropriate
    `Sparkle.Core.runCircuit{N}` call based on how many
    `Signal.reg` declarations the body has. -/
syntax "circuit" "do" ppLine
  withPosition((colGe cdoStmt)*) : term

/-! ### Flattener — same shape as Signal.lean's macro.

    Walks branch bodies, collapses branch-local `let` bindings
    into the rhs of every following `<~`, and rejects nested
    register declarations or `return` statements inside arms. -/

partial def collectCdoBranchAssigns
    (kind : String) (flat : Array (Lean.TSyntax `cdoStmt)) :
    Lean.MacroM (Array (Lean.Name × Lean.TSyntax `term × Lean.TSyntax `ident)) := do
  let mut t : Array (Lean.Name × Lean.TSyntax `term × Lean.TSyntax `ident) := #[]
  let mut localLets : Array (Lean.TSyntax `ident × Lean.TSyntax `term) := #[]
  for s in flat do
    match s with
    | `(cdoStmt| $n:ident <~ $rhs)
    | `(cdoStmt| $n:ident <~ $rhs ;) =>
      let mut wrapped : Lean.TSyntax `term := rhs
      for i in [:localLets.size] do
        let (lname, le) := localLets[localLets.size - 1 - i]!
        wrapped ← `(let $lname := $le; $wrapped)
      t := t.filter (fun (k, _, _) => k != n.getId)
      t := t.push (n.getId, wrapped, n)
    | `(cdoStmt| let $name := $rhs)
    | `(cdoStmt| let $name := $rhs ;) =>
      localLets := localLets.push (name, rhs)
    | `(cdoStmt| let $_ ← Signal.reg $_)
    | `(cdoStmt| let $_ ← Signal.reg $_ ;) =>
      Lean.Macro.throwError
        s!"circuit do: register declarations inside `{kind}` arms are not allowed"
    | `(cdoStmt| return $_)
    | `(cdoStmt| return $_ ;) =>
      Lean.Macro.throwError
        s!"circuit do: `return` inside `{kind}` arms is not allowed"
    | _ => Lean.Macro.throwUnsupported
  return t

/-- Flatten a sequence of `cdoStmt`s, lowering any `if cond
    then … else …` to per-register muxed `<~` assignments.

    Recursive: nested `if`s collapse bottom-up.  A register
    assigned on only one side keeps its current value on the
    other (hold semantics — the missing rhs becomes the
    register identifier itself). -/
partial def flattenCdoStmts (stmts : Array (Lean.TSyntax `cdoStmt)) :
    Lean.MacroM (Array (Lean.TSyntax `cdoStmt)) := do
  let mut out : Array (Lean.TSyntax `cdoStmt) := #[]
  for s in stmts do
    match s with
    | `(cdoStmt| if $cond then $thens:cdoStmt* else $elses:cdoStmt*) =>
      let thenFlat ← flattenCdoStmts thens
      let elseFlat ← flattenCdoStmts elses
      let thenAssigns ← collectCdoBranchAssigns "if" thenFlat
      let elseAssigns ← collectCdoBranchAssigns "if" elseFlat
      -- Union of register names assigned in either branch.
      let mut names : Array (Lean.Name × Lean.TSyntax `ident) := #[]
      for (n, _, nIdent) in thenAssigns do
        unless names.any (fun (k, _) => k == n) do
          names := names.push (n, nIdent)
      for (n, _, nIdent) in elseAssigns do
        unless names.any (fun (k, _) => k == n) do
          names := names.push (n, nIdent)
      -- Emit one `<~` per register with a Signal.mux rhs.
      for (n, nIdent) in names do
        let thenRhs : Lean.TSyntax `term ←
          match thenAssigns.find? (fun (k, _, _) => k == n) with
          | some (_, rhs, _) => pure rhs
          | none => `($nIdent)  -- hold: read current value
        let elseRhs : Lean.TSyntax `term ←
          match elseAssigns.find? (fun (k, _, _) => k == n) with
          | some (_, rhs, _) => pure rhs
          | none => `($nIdent)
        let muxed ← `(Signal.mux $cond $thenRhs $elseRhs)
        let stmt ← `(cdoStmt| $nIdent:ident <~ $muxed)
        out := out.push stmt
    | _ => out := out.push s
  return out

/-! ### Main expansion: `circuit do { … }` → `runCircuit{N}`.

    Strategy:
      1. Flatten if/else into single muxed `<~` rows.
      2. Collect all `Signal.reg` declarations in source order.
      3. Lower to the matching `runCircuit{N}` call with a body
         that uses Lean's standard `do`-notation over the v2
         Circuit monad. -/

macro_rules
  | `(circuit do $stmts:cdoStmt*) => do
    let flat ← flattenCdoStmts stmts
    -- Separate registers from other statements.
    let mut regs : Array (Lean.TSyntax `ident × Lean.TSyntax `term) := #[]
    let mut bodyStmts : Array (Lean.TSyntax `cdoStmt) := #[]
    for s in flat do
      match s with
      | `(cdoStmt| let $name:ident ← Signal.reg $init)
      | `(cdoStmt| let $name:ident ← Signal.reg $init ;) =>
        regs := regs.push (name, init)
      | _ => bodyStmts := bodyStmts.push s
    -- Build the body as nested `Sparkle.Core.Circuit.bind` chain
    -- ending in `Sparkle.Core.Circuit.pure' retExpr`.  Avoids
    -- having to thread a `doSeqItem` array through quotation —
    -- the macro reduce side only sees `Circuit.bind` /
    -- `Circuit.pure'`, which `handleCircuitMonad` already lowers.
    let mut steps : Array (Lean.TSyntax `term × Bool) := #[]
    -- Each step is (term, isLet).  `isLet = true` means we wrap
    -- the continuation with `let $name := $rhs;` instead of a
    -- `Circuit.bind`.
    let mut returnTerm : Option (Lean.TSyntax `term) := none
    let mut letBindings : Array (Lean.TSyntax `ident × Lean.TSyntax `term) := #[]
    for s in bodyStmts do
      match s with
      | `(cdoStmt| $n:ident <~ $rhs)
      | `(cdoStmt| $n:ident <~ $rhs ;) =>
        -- Apply pending value-level lets to the rhs.
        let mut wrapped : Lean.TSyntax `term := rhs
        for i in [:letBindings.size] do
          let (lname, le) := letBindings[letBindings.size - 1 - i]!
          wrapped ← `(let $lname := $le; $wrapped)
        letBindings := #[]
        let action ← `(Sparkle.Core.Circuit.next $n $wrapped)
        steps := steps.push (action, false)
      | `(cdoStmt| let $name := $rhs)
      | `(cdoStmt| let $name := $rhs ;) =>
        letBindings := letBindings.push (name, rhs)
      | `(cdoStmt| return $r)
      | `(cdoStmt| return $r ;) =>
        if returnTerm.isSome then
          Lean.Macro.throwError "circuit do: multiple `return` statements"
        let mut wrapped : Lean.TSyntax `term := r
        for i in [:letBindings.size] do
          let (lname, le) := letBindings[letBindings.size - 1 - i]!
          wrapped ← `(let $lname := $le; $wrapped)
        letBindings := #[]
        returnTerm := some wrapped
      | _ => Lean.Macro.throwUnsupported
    let some retExpr := returnTerm
      | Lean.Macro.throwError "circuit do: missing `return` statement"
    -- Fold right: build `bind a1 (fun _ => bind a2 (fun _ => …
    --   pure' retExpr))` from the steps array.
    let mut body : Lean.TSyntax `term ← `(Sparkle.Core.Circuit.pure' $retExpr)
    for i in [:steps.size] do
      let (action, _) := steps[steps.size - 1 - i]!
      body ← `(Sparkle.Core.Circuit.bind $action (fun _ => $body))
    let doBody := body
    let runCircuit ← match regs.size with
      | 0 =>
        Lean.Macro.throwError "circuit do: at least one `let r ← Signal.reg …` is required"
      | 1 =>
        let (r0, i0) := regs[0]!
        `(Sparkle.Core.runCircuit1 $i0 (fun $r0 => $doBody))
      | 2 =>
        let (r0, i0) := regs[0]!
        let (r1, i1) := regs[1]!
        `(Sparkle.Core.runCircuit2 $i0 $i1 (fun $r0 $r1 => $doBody))
      | 3 =>
        let (r0, i0) := regs[0]!
        let (r1, i1) := regs[1]!
        let (r2, i2) := regs[2]!
        `(Sparkle.Core.runCircuit3 $i0 $i1 $i2 (fun $r0 $r1 $r2 => $doBody))
      | n =>
        Lean.Macro.throwError s!"circuit do: only 1..3 registers supported currently (got {n}); extend runCircuit helpers"
    return runCircuit

end Sparkle.Core
