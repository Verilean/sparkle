/-
  verilog! — Inline Verilog-to-Lean Elaboration Macro

  Parses a Verilog string at compile time, lowers to Sparkle IR,
  extracts a pure state-machine model, and injects the generated
  Lean definitions (State, Input, nextState, initState) into the
  current environment.

  Usage:
    verilog! "
      module counter8_en (
          input clk, input rst, input en,
          output [7:0] count
      );
          reg [7:0] count_reg;
          assign count = count_reg;
          always @(posedge clk) begin
              if (rst) count_reg <= 0;
              else if (en) count_reg <= count_reg + 1;
          end
      endmodule
    "

  This generates `counter8_en.Verify.State`, `.Input`, `.nextState`, `.initState`
  in the current file — no separate generation step or file import needed.
-/

import Lean
import Tools.SVParser
import Tools.SVParser.Verify

open Lean Elab Command
open Tools.SVParser.Parser
open Tools.SVParser.Lower
open Tools.SVParser.Verify

/-- Split generated Lean source into individual command blocks -/
private def splitCommandBlocks (src : String) : List String := Id.run do
  let lines := src.splitOn "\n"
  let mut blocks : List String := []
  let mut current : String := ""
  for line in lines do
    let trimmed := line.trimLeft
    if trimmed.startsWith "namespace " || trimmed.startsWith "end " ||
       trimmed.startsWith "structure " || trimmed.startsWith "def " ||
       trimmed.startsWith "theorem " then
      if !current.trim.isEmpty then
        blocks := blocks ++ [current]
      current := line
    else
      current := current ++ "\n" ++ line
  if !current.trim.isEmpty then
    blocks := blocks ++ [current]
  return blocks

/-- Compile-time Verilog → Lean elaboration.
    Parses Verilog source, lowers to IR, generates State/Input/nextState
    definitions, and injects them into the current Lean environment. -/
elab "verilog!" src:str : command => do
  let vSrc := src.getString
  -- Parse and lower Verilog to Sparkle IR
  match parseAndLower vSrc with
  | .error err => throwError "verilog!: parsing failed: {err}"
  | .ok design =>
    match design.modules.head? with
    | none => throwError "verilog!: no module found"
    | some m =>
      -- Generate Lean source string
      let leanStr := moduleToLean m
      -- Parse each line-group as a separate Lean command and elaborate
      -- Split on blank lines to get individual command blocks
      let blocks := splitCommandBlocks leanStr
      for block in blocks do
        let trimmed := block.trim
        if trimmed.isEmpty || trimmed.startsWith "/-" && trimmed.endsWith "-/" then
          continue  -- skip empty lines and doc comments
        let env ← getEnv
        match Parser.runParserCategory env `command trimmed with
        | .error err =>
          throwError "verilog!: parse error in block:\n{err}\n\nBlock:\n{trimmed}"
        | .ok stx =>
          elabCommand stx
