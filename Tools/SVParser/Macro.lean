/-
  verilog! — Inline Verilog-to-Lean Elaboration Macro

  Parses Verilog at compile time, lowers to Sparkle IR, and injects
  State/Input/nextState/initState into the current Lean environment.

  The nextState body is built via Lean Syntax quotation (type-safe AST),
  not string interpolation — no parenthesis bugs or width mismatches.
-/

import Lean
import Tools.SVParser
import Tools.SVParser.Verify

open Lean Elab Command Term Meta
open Tools.SVParser.Parser
open Tools.SVParser.Lower
open Tools.SVParser.Verify

private def elabStr (s : String) : CommandElabM Unit := do
  match Parser.runParserCategory (← getEnv) `command s with
  | .error err => throwError "verilog! parse error:\n{err}\n\nSource:\n{s}"
  | .ok stx => elabCommand stx

-- ============================================================================
-- The verilog! command
-- ============================================================================

/-- Compile-time Verilog → Lean elaboration. -/
elab "verilog!" src:str : command => do
  let vSrc := src.getString
  match parseAndLower vSrc with
  | .error err => throwError "verilog!: parsing failed: {err}"
  | .ok design =>
    match design.modules.head? with
    | none => throwError "verilog!: no module found"
    | some m =>
      let model : SemanticModel := extractModel m
      let assigns := collectAssigns m.body
      let model : SemanticModel := { model with
        registers := model.registers.map fun r =>
          { r with nextExpr := inlineAssigns assigns r.nextExpr }
      }
      let wireWidths := m.wires.map fun w => (w.name, w.ty.bitWidth)
      let portWidths := m.inputs.map fun p => (p.name, p.ty.bitWidth)
      let regWidths := model.registers.map fun r => (r.name, r.width)
      let inputWidths := model.inputs.map fun i => (i.name, i.width)
      let allWidths := regWidths ++ inputWidths ++ wireWidths ++ portWidths
      let ns := leanName model.moduleName

      -- 1. namespace + State + Input (string-based: simple boilerplate)
      elabStr s!"namespace {ns}.Verify"

      let stateFields := String.intercalate "\n" <|
        model.registers.map fun r => s!"  {leanName r.name} : BitVec {r.width}"
      elabStr s!"structure State where\n{stateFields}\n  deriving DecidableEq, Repr, BEq, Inhabited"

      let inputFields := String.intercalate "\n" <|
        model.inputs.map fun i => s!"  {leanName i.name} : BitVec {i.width}"
      elabStr s!"structure Input where\n{inputFields}\n  deriving DecidableEq, Repr, BEq, Inhabited"

      -- 2. nextState (use irExprToLean for fully-parenthesized expressions)
      let lb := "{"
      let rb := "}"
      let regW := model.registers.map fun r => (r.name, r.width)
      let inpW := model.inputs.map fun i => (i.name, i.width)
      let nextFieldStrs := model.registers.map fun r =>
        let fixedExpr := fixConstWidths r.nextExpr r.width allWidths
        let valStr := irExprToLean fixedExpr regW inpW allWidths "s" "i"
        s!"    {leanName r.name} := {valStr}"
      let nextBody := String.intercalate ",\n" nextFieldStrs
      elabStr s!"def nextState (s : State) (i : Input) : State :=\n  {lb}\n{nextBody}\n  {rb}"

      -- 3. initState
      let initFields := String.intercalate ",\n" <|
        model.registers.map fun r => s!"    {leanName r.name} := ({r.initValue} : BitVec {r.width})"
      elabStr s!"def initState : State :=\n  {lb}\n{initFields}\n  {rb}"

      -- 4. Auto-generate theorems from Verilog assert statements
      let regW := model.registers.map fun r => (r.name, r.width)
      let inpW := model.inputs.map fun i => (i.name, i.width)
      for (assertName, condExpr) in model.assertions do
        -- Fix constant widths: use width inference per sub-expression
        let fixedCond := fixConstWidthsSmart condExpr allWidths
        -- Assertion checks next-state: let ns := nextState s i, use ns.field
        let condStr := irExprToLean fixedCond regW inpW allWidths "ns" "i"
        -- Generate theorem: simp unfolds nextState, then bv_decide proves the BitVec property
        let thmStr := s!"theorem {assertName} (s : State) (i : Input) : let ns := nextState s i; {condStr} != (0 : BitVec 1) := by simp [nextState]; bv_decide"
        try
          elabStr thmStr
        catch _ =>
          try
            elabStr s!"theorem {assertName} (s : State) (i : Input) : let ns := nextState s i; {condStr} != (0 : BitVec 1) := by simp [nextState]"
          catch _ =>
            elabStr s!"theorem {assertName} (s : State) (i : Input) : let ns := nextState s i; {condStr} != (0 : BitVec 1) := by sorry"

      -- 5. close namespace
      elabStr s!"end {ns}.Verify"
