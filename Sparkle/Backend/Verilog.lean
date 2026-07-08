/-
  SystemVerilog Backend

  Generates synthesizable SystemVerilog code from the IR.
-/

import Sparkle.IR.AST
import Sparkle.IR.Type
import Sparkle.IR.Optimize

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

/-- Convert IR expression to Verilog expression.
    `widthOf` maps a wire name to its declared bit width (when known),
    so a full-width / scalar `.slice` can be elided — Verilog forbids a
    part-select on a scalar (`s[0:0]` → "can not select part of
    scalar"). -/
partial def emitExpr (widthOf : String → Option Nat := fun _ => none)
    (e : Expr) : String :=
  match e with
  | .const value width =>
    -- Verilog forbids a zero-width sized literal (`0'd0` → "Sized
    -- numeric constant must have a size greater than zero").  A
    -- 0-width constant only ever arises as a degenerate zero-extend
    -- piece (e.g. `{x, <0-width>}`); the wires that carry it are
    -- declared `[0:0]` (1 bit), so emit a 1-bit literal to match.
    let width := if width == 0 then 1 else width
    if value < 0 then
      -- Negative values: convert to two's complement hex to avoid
      -- invalid Verilog literals like 32'd-2147483648
      let modulus : Int := (2 : Int) ^ width
      let unsigned := ((value % modulus) + modulus) % modulus
      s!"{width}'h{String.ofList (Nat.toDigits 16 unsigned.toNat)}"
    else
      s!"{width}'d{value}"

  | .ref name =>
    sanitizeName name

  | .concat args =>
    s!"\{{String.intercalate ", " (args.map (emitExpr widthOf))}}"

  | .slice e hi lo =>
    -- Elide a slice that selects the FULL width of a known wire (in
    -- particular `s[0:0]` on a scalar, which Verilog rejects with
    -- "can not select part of scalar").  Only when the source is a
    -- `.ref` with a known width and the range covers [width-1 : 0].
    match e with
    | .ref name =>
      match widthOf (sanitizeName name) with
      | some w =>
        if lo == 0 && hi + 1 >= w then sanitizeName name
        else s!"{sanitizeName name}[{hi}:{lo}]"
      | none => s!"{sanitizeName name}[{hi}:{lo}]"
    | _ =>
      -- A part-select is only legal in Verilog on a NAME (net/reg/array
      -- element) — `(a >> b)[0:0]` is a syntax error.  When the operand is
      -- a compound expression (e.g. a single-use shift the optimizer
      -- inlined here), emit the equivalent shift-and-mask `((e >> lo) &
      -- {n{1'b1}})` instead, which is valid on any expression.
      let n := hi + 1 - lo
      let mask := (Nat.pow 2 n) - 1
      s!"(({emitExpr widthOf e} >> {lo}) & {n}'h{String.ofList (Nat.toDigits 16 mask)})"

  | .index arr idx =>
    s!"{emitExpr widthOf arr}[{emitExpr widthOf idx}]"

  | .op .mux args =>
    -- Mux is special: cond ? then_val : else_val
    match args with
    | [cond, thenVal, elseVal] =>
      s!"({emitExpr widthOf cond} ? {emitExpr widthOf thenVal} : {emitExpr widthOf elseVal})"
    | _ => "/* ERROR: mux requires 3 arguments */"

  | .op .not args =>
    -- Unary NOT
    match args with
    | [arg] => s!"~{emitExpr widthOf arg}"
    | _ => "/* ERROR: not requires 1 argument */"

  | .op .neg args =>
    -- Unary negation
    match args with
    | [arg] => s!"-{emitExpr widthOf arg}"
    | _ => "/* ERROR: neg requires 1 argument */"

  | .op operator args =>
    -- Binary operators
    match args with
    | [arg1, arg2] =>
      match operator with
      | .lt_s | .le_s | .gt_s | .ge_s | .asr =>
        s!"($signed({emitExpr widthOf arg1}) {emitOperator operator} $signed({emitExpr widthOf arg2}))"
      | _ =>
        s!"({emitExpr widthOf arg1} {emitOperator operator} {emitExpr widthOf arg2})"
    | _ => s!"/* ERROR: operator {operator} with wrong arity */"

/-- Emit a single statement.
    The optional `wires` parameter provides wire declarations for register
    reset value width lookup. -/
def emitStmt (stmt : Stmt) (indent : String := "    ")
    (wires : List Port := []) : String :=
  -- Wire-name → declared width, so `emitExpr` can elide full-width /
  -- scalar slices that Verilog would reject.
  let widthOf : String → Option Nat := fun n =>
    (wires.find? (fun p => sanitizeName p.name == n)).bind fun p =>
      match p.ty with
      | .bitVector w => some w
      | .bit         => some 1
      | _            => none
  match stmt with
  | .assign lhs rhs =>
    s!"{indent}assign {sanitizeName lhs} = {emitExpr widthOf rhs};"

  | .register output clock reset input initValue =>
    -- Generate always_ff block for register.  The sensitivity list
    -- depends on whether the user declared the domain's reset as
    -- synchronous (clock-edge-only) or asynchronous (clock-edge OR
    -- reset rising edge).
    let (rstName, rstKind) := reset
    -- Look up output wire width for correct reset literal width
    let resetWidth := match wires.find? (fun p => p.name == output) with
      | some p => match p.ty with
        | .bitVector w => w
        | .bit => 1
        | _ => 8
      | none => 8
    let sensitivity := match rstKind with
      | .asynchronous =>
        s!"@(posedge {sanitizeName clock} or posedge {sanitizeName rstName})"
      | .synchronous =>
        s!"@(posedge {sanitizeName clock})"
    s!"{indent}always_ff {sensitivity} begin\n" ++
    s!"{indent}    if ({sanitizeName rstName})\n" ++
    s!"{indent}        {sanitizeName output} <= {emitExpr widthOf (.const initValue resetWidth)};\n" ++
    s!"{indent}    else\n" ++
    s!"{indent}        {sanitizeName output} <= {emitExpr widthOf input};\n" ++
    s!"{indent}end"

  | .memory name addrWidth dataWidth clock writeAddr writeData writeEnable readAddr readData comboRead =>
    -- Generate memory array and always_ff block
    let memSize := 2 ^ addrWidth
    let memDecl := s!"{indent}logic [{dataWidth-1}:0] {sanitizeName name} [0:{memSize-1}];"
    if comboRead then
      -- Combinational read: assign readData = mem[readAddr]
      let assignRead := s!"{indent}assign {sanitizeName readData} = {sanitizeName name}[{emitExpr widthOf readAddr}];"
      let alwaysBlock :=
        s!"{indent}always_ff @(posedge {sanitizeName clock}) begin\n" ++
        s!"{indent}    if ({emitExpr widthOf writeEnable}) begin\n" ++
        s!"{indent}        {sanitizeName name}[{emitExpr widthOf writeAddr}] <= {emitExpr widthOf writeData};\n" ++
        s!"{indent}    end\n" ++
        s!"{indent}end"
      memDecl ++ "\n" ++ assignRead ++ "\n" ++ alwaysBlock
    else
      -- Registered read: readData latched inside always_ff
      let alwaysBlock :=
        s!"{indent}always_ff @(posedge {sanitizeName clock}) begin\n" ++
        s!"{indent}    if ({emitExpr widthOf writeEnable}) begin\n" ++
        s!"{indent}        {sanitizeName name}[{emitExpr widthOf writeAddr}] <= {emitExpr widthOf writeData};\n" ++
        s!"{indent}    end\n" ++
        s!"{indent}    {sanitizeName readData} <= {sanitizeName name}[{emitExpr widthOf readAddr}];\n" ++
        s!"{indent}end"
      memDecl ++ "\n" ++ alwaysBlock

  | .inst moduleName instName connections =>
    let connStrs := connections.map fun (portName, expr) =>
      s!".{sanitizeName portName}({emitExpr widthOf expr})"
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

    -- Filter out wires that are already declared as input/output ports
    let portNames := (m.inputs ++ m.outputs).map (·.name)
    let internalWires := m.wires.filter fun w => !portNames.contains w.name
    let wires := if internalWires.isEmpty then
      ""
    else
      "\n" ++ emitWireDecls internalWires ++ "\n"

    let body := if m.body.isEmpty then
      ""
    else
      let stmts := m.body.map (emitStmt · "    " m.wires)
      "\n" ++ String.intercalate "\n\n" stmts ++ "\n"

    let footer := "\nendmodule\n"

    header ++ wires ++ body ++ footer

/-- Main entry point: Convert a Module to SystemVerilog -/
def toVerilog (m : Module) : String :=
  emitModule m

/-- Convert a full Design to SystemVerilog.

    Each module is run through the IR optimizer first — exactly as
    `#synthesizeVerilog` does before `toVerilog` (see
    `Sparkle.Compiler.Elab`).  This is essential, not cosmetic: the
    optimizer's 0-bit elimination pass strips the degenerate 0-width
    concat tails that `circuit do` / `Signal.loop` bundles leave behind
    (`{reg, <0-bit>}`).  Without it those tails reach `emitConst`, which
    promotes a 0-width literal to `1'd0`, widening the concat by one bit
    so the intermediate wire (sized for the real field) TRUNCATES the
    real value away — silently freezing the least-significant register of
    every bundle at its reset value.  Hierarchical emission
    (`#writeVerilogDesign`) is the only source of the `@[hardware_module]`
    submodules, so skipping this here broke every sub-module's last
    register (e.g. `uartRxHW`'s `rxValid`). -/
def toVerilogDesign (d : Design) : String :=
  let modules := d.modules.map (fun m => emitModule (Sparkle.IR.Optimize.optimizeModule m))
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
