/-
  `deriving SignalLeaves` — auto-derive `Sparkle.Core.SignalLeaves`
  for user-defined record types.

  A record with fields `f₁ : Signal dom τ₁, f₂ : MyOtherRecord, …`
  gets the instance

    instance : SignalLeaves MyRec dom where
      toLeaves r := SignalLeaves.toLeaves r.f₁
                ++ SignalLeaves.toLeaves r.f₂
                ++ …

  The handler requires every field's type to have a
  `SignalLeaves` instance under the same `dom`.  Base instances
  cover `Signal dom τ` and `Prod α β`; nested records pick up
  recursively (when they also `deriving SignalLeaves`).
-/

import Sparkle.Core.CircuitMonad
import Lean.Elab.Deriving.Basic

namespace Sparkle.Core.SignalLeavesDerive

open Lean Lean.Meta Lean.Elab Lean.Elab.Command Lean.Elab.Term

/-- Construct the instance body source as a raw string and
    elaborate it as a fresh command.  Going through a string
    avoids the antiquotation gymnastics that fail when Lean
    parses the quotation site as Lean source (the `bracketedBinder`
    splice doesn't play well with `instance … where` even in
    upstream deriving handlers — see ToExpr/Repr — because the
    `where` clause expects a single value, not a sequence). -/
private def mkSignalLeavesInstanceCmd (declName : Name) : TermElabM String := do
  let indVal ← getConstInfoInduct declName
  unless indVal.ctors.length == 1 do
    throwError s!"deriving SignalLeaves: {declName} has {indVal.ctors.length} constructors (records only)"
  -- Capture each parameter as `(name, type)` so we can emit an
  -- explicit binder.  Otherwise `{dom}` without a type annotation
  -- forces Lean to invent a type for `dom`, which fails when the
  -- record's `dom : DomainConfig` parameter is among them.
  let paramData : Array (String × String) ←
    forallTelescopeReducing indVal.type fun paramsIndices _ => do
      let mut out : Array (String × String) := #[]
      for x in paramsIndices do
        let n := (← x.fvarId!.getUserName).eraseMacroScopes.toString
        let t ← inferType x
        let tStr := (← ppExpr t).pretty
        out := out.push (n, tStr)
      return out
  let paramNames : Array String := paramData.map (·.1)
  -- Collect field names from the single constructor.
  let ctorName := indVal.ctors.head!
  let ctorInfo ← getConstInfoCtor ctorName
  let fieldNames : Array String ←
    forallTelescopeReducing ctorInfo.type fun args _ => do
      let mut out : Array String := #[]
      let fields := args.toList.drop indVal.numParams
      for f in fields do
        out := out.push (← f.fvarId!.getUserName).toString
      return out
  -- If the record already has a `DomainConfig` parameter, re-use
  -- its name as the SignalLeaves `dom`; otherwise introduce a
  -- fresh `dom` binder.  This is what makes `RxOut dom`-style
  -- records derive correctly: the field types reference `dom`
  -- by name, so the instance must too.
  let domStr :=
    match paramData.toList.filterMap (fun (n, t) =>
            if t.endsWith "DomainConfig" then some n else none) with
    | n :: _ => n
    | []     => "dom"
  let typeApp := "@" ++ declName.toString ++
    String.join (paramNames.toList.map (fun s => " " ++ s))
  -- Emit a typed binder per parameter; if `dom` isn't already
  -- among them, add a fresh one with its type.
  let mainBinders := String.join (paramData.toList.map fun (n, t) =>
    "{" ++ n ++ " : " ++ t ++ "} ")
  let extraDomBinder :=
    if paramData.any (fun (n, _) => n == domStr) then ""
    else "{" ++ domStr ++ " : Sparkle.Core.Domain.DomainConfig}"
  let binderList := mainBinders ++ extraDomBinder
  let body :=
    if fieldNames.isEmpty then "[]"
    else
      let calls := fieldNames.toList.map fun f =>
        "Sparkle.Core.SignalLeaves.toLeaves r." ++ f
      String.intercalate " ++ " calls
  let instName := declName.toString ++ ".instSignalLeavesAuto"
  let cmd := "instance " ++ instName ++ " " ++ binderList ++ " : Sparkle.Core.SignalLeaves (" ++ typeApp ++ ") " ++ domStr ++ " where\n  toLeaves r := " ++ body
  return cmd

/-- Deriving handler for `Sparkle.Core.SignalLeaves`. -/
def mkSignalLeavesHandler (declNames : Array Name) : CommandElabM Bool := do
  if (← declNames.allM isInductive) then
    for declName in declNames do
      let src ← liftTermElabM (mkSignalLeavesInstanceCmd declName)
      -- Parse and elaborate the instance command from the
      -- assembled source string.
      let env ← getEnv
      let stx? := Parser.runParserCategory env `command src "<deriving SignalLeaves>"
      match stx? with
      | .ok cmd => elabCommand cmd
      | .error msg =>
        throwError s!"deriving SignalLeaves: failed to parse generated instance for {declName}:\n  source = {src}\n  error = {msg}"
    return true
  else
    return false

initialize
  Lean.Elab.registerDerivingHandler
    ``Sparkle.Core.SignalLeaves mkSignalLeavesHandler

end Sparkle.Core.SignalLeavesDerive
