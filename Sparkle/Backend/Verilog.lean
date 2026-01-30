/-
  SystemVerilog Backend

  Generates synthesizable SystemVerilog code from the IR.
-/

import Sparkle.IR.AST
import Sparkle.IR.Type

namespace Sparkle.Backend.Verilog

open Sparkle.IR.AST
open Sparkle.IR.Type

/-- Sanitize a name to be a valid Verilog identifier -/
def sanitizeName (name : String) : String :=
  name.replace "." "_"
    |>.replace "-" "_"
    |>.replace " " "_"
    |>.replace "'" "_prime"
    |>.replace "#" ""

/-- Convert HWType to Verilog type declaration -/
def emitType (ty : HWType) : String :=
  match ty with
  | .bit => "logic"
  | .bitVector 1 => "logic"
  | .bitVector w => s!"logic [{w-1}:0]"
  | .array size elemType =>
    s!"{emitType elemType} [{size-1}:0]"

/-- Convert Operator to Verilog operator symbol -/
def emitOperator (op : Operator) : String :=
  match op with
  | .and => "&"
  | .or  => "|"
  | .xor => "^"
  | .not => "~"
  | .add => "+"
  | .sub => "-"
  | .mul => "*"
  | .eq  => "=="
  | .lt_u => "<"
  | .lt_s => "<" -- Handled in emitExpr with $signed()
  | .le_u => "<="
  | .le_s => "<=" -- Handled in emitExpr with $signed()
  | .gt_u => ">"
  | .gt_s => ">" -- Handled in emitExpr with $signed()
  | .ge_u => ">="
  | .ge_s => ">=" -- Handled in emitExpr with $signed()
  | .shl => "<<"
  | .shr => ">>"
  | .asr => ">>>"
  | .neg => "-"
  | .mux => "?"  -- Special case, handled in emitExpr

/-- Convert IR expression to Verilog expression -/
partial def emitExpr (e : Expr) : String :=
  match e with
  | .const value width =>
    s!"{width}'d{value}"

  | .ref name =>
    sanitizeName name

  | .concat args =>
    s!"\{{String.intercalate ", " (args.map emitExpr)}}"

  | .slice e hi lo =>
    s!"{emitExpr e}[{hi}:{lo}]"

  | .index arr idx =>
    s!"{emitExpr arr}[{emitExpr idx}]"

  | .op .mux args =>
    -- Mux is special: cond ? then_val : else_val
    match args with
    | [cond, thenVal, elseVal] =>
      s!"({emitExpr cond} ? {emitExpr thenVal} : {emitExpr elseVal})"
    | _ => "/* ERROR: mux requires 3 arguments */"

  | .op .not args =>
    -- Unary NOT
    match args with
    | [arg] => s!"~{emitExpr arg}"
    | _ => "/* ERROR: not requires 1 argument */"

  | .op .neg args =>
    -- Unary negation
    match args with
    | [arg] => s!"-{emitExpr arg}"
    | _ => "/* ERROR: neg requires 1 argument */"

  | .op operator args =>
    -- Binary operators
    match args with
    | [arg1, arg2] =>
      match operator with
      | .lt_s | .le_s | .gt_s | .ge_s | .asr =>
        s!"($signed({emitExpr arg1}) {emitOperator operator} $signed({emitExpr arg2}))"
      | _ =>
        s!"({emitExpr arg1} {emitOperator operator} {emitExpr arg2})"
    | _ => s!"/* ERROR: operator {operator} with wrong arity */"

/-- Emit a single statement -/
def emitStmt (stmt : Stmt) (indent : String := "    ") : String :=
  match stmt with
  | .assign lhs rhs =>
    s!"{indent}assign {sanitizeName lhs} = {emitExpr rhs};"

  | .register output clock reset input initValue =>
    -- Generate always_ff block for register
    s!"{indent}always_ff @(posedge {sanitizeName clock} or posedge {sanitizeName reset}) begin\n" ++
    s!"{indent}    if ({sanitizeName reset})\n" ++
    s!"{indent}        {sanitizeName output} <= {emitExpr (.const initValue 8)};\n" ++
    s!"{indent}    else\n" ++
    s!"{indent}        {sanitizeName output} <= {emitExpr input};\n" ++
    s!"{indent}end"

  | .memory name addrWidth dataWidth clock writeAddr writeData writeEnable readAddr readData =>
    -- Generate memory array and always_ff block
    let memSize := 2 ^ addrWidth
    let memDecl := s!"{indent}logic [{dataWidth-1}:0] {sanitizeName name} [0:{memSize-1}];"
    let alwaysBlock :=
      s!"{indent}always_ff @(posedge {sanitizeName clock}) begin\n" ++
      s!"{indent}    if ({emitExpr writeEnable}) begin\n" ++
      s!"{indent}        {sanitizeName name}[{emitExpr writeAddr}] <= {emitExpr writeData};\n" ++
      s!"{indent}    end\n" ++
      s!"{indent}    {sanitizeName readData} <= {sanitizeName name}[{emitExpr readAddr}];\n" ++
      s!"{indent}end"
    memDecl ++ "\n" ++ alwaysBlock

  | .inst moduleName instName connections =>
    let connStrs := connections.map fun (portName, expr) =>
      s!".{sanitizeName portName}({emitExpr expr})"
    let connList := String.intercalate ", " connStrs
    s!"{indent}{sanitizeName moduleName} {sanitizeName instName} ({connList});"

/-- Emit port declarations for module header -/
def emitPortList (inputs : List Port) (outputs : List Port) : String :=
  let inputDecls := inputs.map fun p =>
    s!"input {emitType p.ty} {sanitizeName p.name}"
  let outputDecls := outputs.map fun p =>
    s!"output {emitType p.ty} {sanitizeName p.name}"

  let allPorts := inputDecls ++ outputDecls
  if allPorts.isEmpty then
    ""
  else
    "\n    " ++ String.intercalate ",\n    " allPorts ++ "\n"

/-- Emit wire declarations -/
def emitWireDecls (wires : List Port) (indent : String := "    ") : String :=
  if wires.isEmpty then
    ""
  else
    let wireDecls := wires.map fun p =>
      s!"{indent}{emitType p.ty} {sanitizeName p.name};"
    String.intercalate "\n" wireDecls ++ "\n"

/-- Emit the full module -/
def emitModule (m : Module) : String :=
  -- For primitive/blackbox modules, just emit a comment (actual module comes from vendor)
  if m.isPrimitive then
    s!"// Primitive module: {m.name}\n" ++
    s!"// This is a blackbox module provided by the technology library\n" ++
    s!"// Interface: inputs={m.inputs.length}, outputs={m.outputs.length}\n\n"
  else
    let header := s!"// Generated by Sparkle HDL\n" ++
                  s!"// Module: {m.name}\n\n" ++
                  s!"module {sanitizeName m.name} ({emitPortList m.inputs m.outputs});\n"

    let wires := if m.wires.isEmpty then
      ""
    else
      "\n" ++ emitWireDecls m.wires ++ "\n"

    let body := if m.body.isEmpty then
      ""
    else
      let stmts := m.body.map (emitStmt · "    ")
      "\n" ++ String.intercalate "\n\n" stmts ++ "\n"

    let footer := "\nendmodule\n"

    header ++ wires ++ body ++ footer

/-- Main entry point: Convert a Module to SystemVerilog -/
def toVerilog (m : Module) : String :=
  emitModule m

/-- Convert a full Design to SystemVerilog -/
def toVerilogDesign (d : Design) : String :=
  let modules := d.modules.map emitModule
  String.intercalate "\n" modules

/-- Write module to a file -/
def writeVerilogFile (m : Module) (filename : String) : IO Unit := do
  let verilog := toVerilog m
  IO.FS.writeFile filename verilog
  IO.println s!"Generated {filename}"

/-- Write a full design to a file -/
def writeVerilogDesignFile (d : Design) (filename : String) : IO Unit := do
  let verilog := toVerilogDesign d
  IO.FS.writeFile filename verilog
  IO.println s!"Generated {filename}"

end Sparkle.Backend.Verilog
