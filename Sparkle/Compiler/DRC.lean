/-
  DRC (Design Rule Check) — Registered Output Check

  Warns when output ports are driven by combinational logic rather than registers.
  For backend-friendly RTL (synthesis + STA), outputs should be driven by registers.
-/

import Sparkle.IR.AST

namespace Sparkle.Compiler.DRC

open Sparkle.IR.AST

/-- Find the statement that defines a given wire name -/
def findDriver (body : List Stmt) (wireName : String) : Option Stmt :=
  body.find? fun
    | .assign lhs _ => lhs == wireName
    | .register output .. => output == wireName
    | .memory (readData := rd) .. => rd == wireName
    | .inst _ instName _ => instName == wireName

/-- Check that all output ports are driven by registers or synchronous memory reads.
    Returns a list of warning strings for violations. -/
def checkRegisteredOutputs (m : Module) : List String :=
  m.outputs.filterMap fun port =>
    -- Skip infrastructure ports
    if port.name == "clk" || port.name == "rst" then
      none
    else
      -- Find the assign statement for this output port
      let assignStmt := m.body.find? fun
        | .assign lhs _ => lhs == port.name
        | _ => false
      match assignStmt with
      | none => none  -- No assign found, skip
      | some (.assign _ rhs) =>
        match rhs with
        | .ref wireName =>
          -- Check what defines this wire
          match findDriver m.body wireName with
          | some (.register ..) => none  -- Registered output, pass
          | some (.memory (comboRead := false) ..) => none  -- Synchronous memory read, pass
          | _ => some s!"[DRC] Module '{m.name}': output '{port.name}' is not driven by a register (driven by wire '{wireName}')"
        | _ => some s!"[DRC] Module '{m.name}': output '{port.name}' is driven by combinational logic"
      | _ => none  -- unreachable

end Sparkle.Compiler.DRC
