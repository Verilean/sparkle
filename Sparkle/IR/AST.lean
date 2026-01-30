/-
  Abstract Syntax Tree for Hardware Netlist

  Defines the IR (Intermediate Representation) that hardware designs compile to.
  This is similar to a simplified Verilog AST.
-/

import Sparkle.IR.Type

namespace Sparkle.IR.AST

open Sparkle.IR.Type

/-- Port declaration (input/output of a module) -/
structure Port where
  name : String
  ty   : HWType
  deriving Repr, BEq, Inhabited


/--
  Hardware operators

  These represent primitive operations that map directly to hardware gates.
-/
inductive Operator where
  | and  : Operator  -- Bitwise AND
  | or   : Operator  -- Bitwise OR
  | xor  : Operator  -- Bitwise XOR
  | not  : Operator  -- Bitwise NOT
  | add  : Operator  -- Addition
  | sub  : Operator  -- Subtraction
  | mul  : Operator  -- Multiplication
  | eq   : Operator  -- Equality comparison
  | lt_u : Operator  -- Less than comparison (unsigned)
  | lt_s : Operator  -- Less than comparison (signed)
  | le_u : Operator  -- Less than or equal (unsigned)
  | le_s : Operator  -- Less than or equal (signed)
  | gt_u : Operator  -- Greater than (unsigned)
  | gt_s : Operator  -- Greater than (signed)
  | ge_u : Operator  -- Greater than or equal (unsigned)
  | ge_s : Operator  -- Greater than or equal (signed)
  | mux  : Operator  -- Multiplexer (ternary: condition ? then : else)
  | shl  : Operator  -- Shift left
  | shr  : Operator  -- Shift right (logical)
  | asr  : Operator  -- Arithmetic shift right (signed)
  | neg  : Operator  -- Arithmetic negation
  deriving Repr, BEq, DecidableEq

namespace Operator

/-- Convert operator to string representation -/
def toString : Operator → String
  | and  => "and"
  | or   => "or"
  | xor  => "xor"
  | not  => "not"
  | add  => "add"
  | sub  => "sub"
  | mul  => "mul"
  | eq   => "eq"
  | lt_u => "lt_u"
  | lt_s => "lt_s"
  | le_u => "le_u"
  | le_s => "le_s"
  | gt_u => "gt_u"
  | gt_s => "gt_s"
  | ge_u => "ge_u"
  | ge_s => "ge_s"
  | mux  => "mux"
  | shl  => "shl"
  | shr  => "shr"
  | asr  => "asr"
  | neg  => "neg"

instance : ToString Operator where
  toString := Operator.toString

end Operator

/--
  Expression in the netlist IR

  - Const: Literal constant value
  - Ref: Reference to a wire or port by name
  - Op: Application of an operator to arguments
-/
inductive Expr where
  | const (value : Int) (width : Nat) : Expr
  | ref (name : String) : Expr
  | op (operator : Operator) (args : List Expr) : Expr
  | concat (args : List Expr) : Expr
  | slice (expr : Expr) (hi lo : Nat) : Expr
  | index (array : Expr) (idx : Expr) : Expr
  deriving Repr, BEq

namespace Expr

/-- Create a constant expression from a BitVec -/
def ofBitVec {n : Nat} (bv : BitVec n) : Expr :=
  .const bv.toInt n

/-- Create a wire reference -/
def wire (name : String) : Expr := .ref name

/-- Helper constructors for common operations -/
def and (a b : Expr) : Expr := .op .and [a, b]
def or (a b : Expr) : Expr := .op .or [a, b]
def xor (a b : Expr) : Expr := .op .xor [a, b]
def not (a : Expr) : Expr := .op .not [a]
def add (a b : Expr) : Expr := .op .add [a, b]
def sub (a b : Expr) : Expr := .op .sub [a, b]
def mul (a b : Expr) : Expr := .op .mul [a, b]
def eq (a b : Expr) : Expr := .op .eq [a, b]
def lt_u (a b : Expr) : Expr := .op .lt_u [a, b]
def lt_s (a b : Expr) : Expr := .op .lt_s [a, b]
def mux (cond then_ else_ : Expr) : Expr := .op .mux [cond, then_, else_]

/-- Convert expression to string (for debugging) -/
partial def toString : Expr → String
  | const v w => s!"{v}#{w}"
  | ref name => name
  | op operator args =>
      let argStr := String.intercalate ", " (args.map toString)
      s!"{operator}({argStr})"
  | concat args => s!"\{{String.intercalate ", " (args.map toString)}}"
  | slice e hi lo => s!"{toString e}[{hi}:{lo}]"
  | index arr idx => s!"{toString arr}[{toString idx}]"

instance : ToString Expr where
  toString := Expr.toString

end Expr

/--
  Statement in the netlist IR

  - Assign: Continuous assignment (combinational logic)
  - Register: Sequential logic (D flip-flop)
  - Inst: Instantiation of another module
-/
inductive Stmt where
  | assign (lhs : String) (rhs : Expr) : Stmt
  | register
      (output : String)      -- Output wire name
      (clock : String)       -- Clock signal name
      (reset : String)       -- Reset signal name
      (input : Expr)         -- Input expression
      (initValue : Int)      -- Reset/initial value
      : Stmt
  | inst
      (moduleName : String)   -- Name of module to instantiate
      (instName : String)     -- Instance name
      (connections : List (String × Expr))  -- Port connections
      : Stmt
  deriving Repr, BEq

namespace Stmt

/-- Convert statement to string (for debugging) -/
def toString : Stmt → String
  | assign lhs rhs => s!"{lhs} := {rhs}"
  | register output clock reset input initValue =>
      s!"reg {output} @(posedge {clock}, {reset}) <= {input} (init: {initValue})"
  | inst modName instName conns =>
      let connStr := String.intercalate ", " (conns.map fun (p, e) => s!".{p}({e})")
      s!"{modName} {instName}({connStr})"

instance : ToString Stmt where
  toString := Stmt.toString

end Stmt

/--
  Module: A hardware module with inputs, outputs, internal wires, and logic

  This represents a synthesizable hardware component.

  If isPrimitive is true, this is a blackbox module (e.g., vendor SRAM, clock gate)
  that should be instantiated but not defined. The body is ignored for primitives.
-/
structure Module where
  name        : String
  inputs      : List Port
  outputs     : List Port
  wires       : List Port    -- Internal wires (ignored for primitives)
  body        : List Stmt    -- Logic (ignored for primitives)
  isPrimitive : Bool := false  -- True for vendor-provided blackbox modules
  deriving Repr, BEq

namespace Module

/-- Create an empty module -/
def empty (name : String) : Module :=
  { name := name
  , inputs := []
  , outputs := []
  , wires := []
  , body := []
  , isPrimitive := false
  }

/-- Create a primitive (blackbox) module with specified interface -/
def primitive (name : String) (inputs : List Port) (outputs : List Port) : Module :=
  { name := name
  , inputs := inputs
  , outputs := outputs
  , wires := []
  , body := []
  , isPrimitive := true
  }

/-- Add an input port -/
def addInput (m : Module) (p : Port) : Module :=
  { m with inputs := m.inputs ++ [p] }

/-- Add an output port -/
def addOutput (m : Module) (p : Port) : Module :=
  { m with outputs := m.outputs ++ [p] }

/-- Add an internal wire -/
def addWire (m : Module) (p : Port) : Module :=
  { m with wires := m.wires ++ [p] }

/-- Add a statement to the body -/
def addStmt (m : Module) (s : Stmt) : Module :=
  { m with body := m.body ++ [s] }

/-- Convert module to string (for debugging) -/
def toString (m : Module) : String :=
  let inputStr := String.intercalate ", " (m.inputs.map fun p => s!"{p.name}: {p.ty}")
  let outputStr := String.intercalate ", " (m.outputs.map fun p => s!"{p.name}: {p.ty}")
  let wireStr := String.intercalate ", " (m.wires.map fun p => s!"{p.name}: {p.ty}")
  let bodyStr := String.intercalate "\n  " (m.body.map Stmt.toString)
  s!"module {m.name}\n" ++
  s!"  inputs:  {inputStr}\n" ++
  s!"  outputs: {outputStr}\n" ++
  s!"  wires:   {wireStr}\n" ++
  s!"  body:\n  {bodyStr}"

instance : ToString Module where
  toString := Module.toString

end Module

/--
  Design: A collection of modules that make up a hardware project.
-/
structure Design where
  topModule : String
  modules   : List Module
  deriving Repr, BEq

namespace Design

/-- Create an empty design -/
def empty (topName : String) : Design :=
  { topModule := topName, modules := [] }

/-- Add a module to the design -/
def addModule (d : Design) (m : Module) : Design :=
  { d with modules := d.modules ++ [m] }

/-- Find a module by name -/
def findModule (d : Design) (name : String) : Option Module :=
  d.modules.find? (·.name == name)

end Design

end Sparkle.IR.AST
