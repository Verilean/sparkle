/-
  Abstract Syntax Tree for Hardware Netlist

  Defines the IR (Intermediate Representation) that hardware designs compile to.
  This is similar to a simplified Verilog AST.
-/

import Sparkle.IR.Type

namespace Sparkle.IR.AST

open Sparkle.IR.Type

/-- A retained top-level Lean `Nat` binder exposed as a module parameter. -/
structure Parameter where
  name : String
  defaultValue : Nat
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Port declaration (input/output of a module) -/
structure Port where
  name : String
  ty   : HWType
  deriving Repr, BEq, DecidableEq, Inhabited


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
  | sliceDim (expr : Expr) (hi lo : DimExpr) : Expr
  | index (array : Expr) (idx : Expr) : Expr
  deriving Repr, BEq, Inhabited

mutual
/-- Decidable equality of expressions (structural; `deriving` does not handle
the nested `List Expr`). -/
def Expr.decEq : (a b : Expr) → Decidable (a = b)
  | .const v₁ w₁, .const v₂ w₂ =>
    match _root_.decEq v₁ v₂, _root_.decEq w₁ w₂ with
    | isTrue h0, isTrue h1 => isTrue (by subst h0; subst h1; rfl)
    | isFalse h, _ => isFalse (fun e => by injection e; contradiction)
    | _, isFalse h => isFalse (fun e => by injection e; contradiction)
  | .const v₁ w₁, .ref n₂ => isFalse (fun h => Expr.noConfusion h)
  | .const v₁ w₁, .op o₂ as₂ => isFalse (fun h => Expr.noConfusion h)
  | .const v₁ w₁, .concat as₂ => isFalse (fun h => Expr.noConfusion h)
  | .const v₁ w₁, .slice e₂ hi₂ lo₂ => isFalse (fun h => Expr.noConfusion h)
  | .const v₁ w₁, .sliceDim e₂ hi₂ lo₂ => isFalse (fun h => Expr.noConfusion h)
  | .const v₁ w₁, .index a₂ i₂ => isFalse (fun h => Expr.noConfusion h)
  | .ref n₁, .const v₂ w₂ => isFalse (fun h => Expr.noConfusion h)
  | .ref n₁, .ref n₂ =>
    match _root_.decEq n₁ n₂ with
    | isTrue h0 => isTrue (by subst h0; rfl)
    | isFalse h => isFalse (fun e => by injection e; contradiction)
  | .ref n₁, .op o₂ as₂ => isFalse (fun h => Expr.noConfusion h)
  | .ref n₁, .concat as₂ => isFalse (fun h => Expr.noConfusion h)
  | .ref n₁, .slice e₂ hi₂ lo₂ => isFalse (fun h => Expr.noConfusion h)
  | .ref n₁, .sliceDim e₂ hi₂ lo₂ => isFalse (fun h => Expr.noConfusion h)
  | .ref n₁, .index a₂ i₂ => isFalse (fun h => Expr.noConfusion h)
  | .op o₁ as₁, .const v₂ w₂ => isFalse (fun h => Expr.noConfusion h)
  | .op o₁ as₁, .ref n₂ => isFalse (fun h => Expr.noConfusion h)
  | .op o₁ as₁, .op o₂ as₂ =>
    match _root_.decEq o₁ o₂, Expr.decEqList as₁ as₂ with
    | isTrue h0, isTrue h1 => isTrue (by subst h0; subst h1; rfl)
    | isFalse h, _ => isFalse (fun e => by injection e; contradiction)
    | _, isFalse h => isFalse (fun e => by injection e; contradiction)
  | .op o₁ as₁, .concat as₂ => isFalse (fun h => Expr.noConfusion h)
  | .op o₁ as₁, .slice e₂ hi₂ lo₂ => isFalse (fun h => Expr.noConfusion h)
  | .op o₁ as₁, .sliceDim e₂ hi₂ lo₂ => isFalse (fun h => Expr.noConfusion h)
  | .op o₁ as₁, .index a₂ i₂ => isFalse (fun h => Expr.noConfusion h)
  | .concat as₁, .const v₂ w₂ => isFalse (fun h => Expr.noConfusion h)
  | .concat as₁, .ref n₂ => isFalse (fun h => Expr.noConfusion h)
  | .concat as₁, .op o₂ as₂ => isFalse (fun h => Expr.noConfusion h)
  | .concat as₁, .concat as₂ =>
    match Expr.decEqList as₁ as₂ with
    | isTrue h0 => isTrue (by subst h0; rfl)
    | isFalse h => isFalse (fun e => by injection e; contradiction)
  | .concat as₁, .slice e₂ hi₂ lo₂ => isFalse (fun h => Expr.noConfusion h)
  | .concat as₁, .sliceDim e₂ hi₂ lo₂ => isFalse (fun h => Expr.noConfusion h)
  | .concat as₁, .index a₂ i₂ => isFalse (fun h => Expr.noConfusion h)
  | .slice e₁ hi₁ lo₁, .const v₂ w₂ => isFalse (fun h => Expr.noConfusion h)
  | .slice e₁ hi₁ lo₁, .ref n₂ => isFalse (fun h => Expr.noConfusion h)
  | .slice e₁ hi₁ lo₁, .op o₂ as₂ => isFalse (fun h => Expr.noConfusion h)
  | .slice e₁ hi₁ lo₁, .concat as₂ => isFalse (fun h => Expr.noConfusion h)
  | .slice e₁ hi₁ lo₁, .slice e₂ hi₂ lo₂ =>
    match Expr.decEq e₁ e₂, _root_.decEq hi₁ hi₂, _root_.decEq lo₁ lo₂ with
    | isTrue h0, isTrue h1, isTrue h2 => isTrue (by subst h0; subst h1; subst h2; rfl)
    | isFalse h, _, _ => isFalse (fun e => by injection e; contradiction)
    | _, isFalse h, _ => isFalse (fun e => by injection e; contradiction)
    | _, _, isFalse h => isFalse (fun e => by injection e; contradiction)
  | .slice e₁ hi₁ lo₁, .sliceDim e₂ hi₂ lo₂ => isFalse (fun h => Expr.noConfusion h)
  | .slice e₁ hi₁ lo₁, .index a₂ i₂ => isFalse (fun h => Expr.noConfusion h)
  | .sliceDim e₁ hi₁ lo₁, .const v₂ w₂ => isFalse (fun h => Expr.noConfusion h)
  | .sliceDim e₁ hi₁ lo₁, .ref n₂ => isFalse (fun h => Expr.noConfusion h)
  | .sliceDim e₁ hi₁ lo₁, .op o₂ as₂ => isFalse (fun h => Expr.noConfusion h)
  | .sliceDim e₁ hi₁ lo₁, .concat as₂ => isFalse (fun h => Expr.noConfusion h)
  | .sliceDim e₁ hi₁ lo₁, .slice e₂ hi₂ lo₂ => isFalse (fun h => Expr.noConfusion h)
  | .sliceDim e₁ hi₁ lo₁, .sliceDim e₂ hi₂ lo₂ =>
    match Expr.decEq e₁ e₂, _root_.decEq hi₁ hi₂, _root_.decEq lo₁ lo₂ with
    | isTrue h0, isTrue h1, isTrue h2 => isTrue (by subst h0; subst h1; subst h2; rfl)
    | isFalse h, _, _ => isFalse (fun e => by injection e; contradiction)
    | _, isFalse h, _ => isFalse (fun e => by injection e; contradiction)
    | _, _, isFalse h => isFalse (fun e => by injection e; contradiction)
  | .sliceDim e₁ hi₁ lo₁, .index a₂ i₂ => isFalse (fun h => Expr.noConfusion h)
  | .index a₁ i₁, .const v₂ w₂ => isFalse (fun h => Expr.noConfusion h)
  | .index a₁ i₁, .ref n₂ => isFalse (fun h => Expr.noConfusion h)
  | .index a₁ i₁, .op o₂ as₂ => isFalse (fun h => Expr.noConfusion h)
  | .index a₁ i₁, .concat as₂ => isFalse (fun h => Expr.noConfusion h)
  | .index a₁ i₁, .slice e₂ hi₂ lo₂ => isFalse (fun h => Expr.noConfusion h)
  | .index a₁ i₁, .sliceDim e₂ hi₂ lo₂ => isFalse (fun h => Expr.noConfusion h)
  | .index a₁ i₁, .index a₂ i₂ =>
    match Expr.decEq a₁ a₂, Expr.decEq i₁ i₂ with
    | isTrue h0, isTrue h1 => isTrue (by subst h0; subst h1; rfl)
    | isFalse h, _ => isFalse (fun e => by injection e; contradiction)
    | _, isFalse h => isFalse (fun e => by injection e; contradiction)
/-- Decidable equality of expression lists. -/
def Expr.decEqList : (a b : List Expr) → Decidable (a = b)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (fun h => by cases h)
  | _ :: _, [] => isFalse (fun h => by cases h)
  | x :: xs, y :: ys =>
    match Expr.decEq x y, Expr.decEqList xs ys with
    | isTrue h0, isTrue h1 => isTrue (by subst h0; subst h1; rfl)
    | isFalse h, _ => isFalse (fun e => by injection e; contradiction)
    | _, isFalse h => isFalse (fun e => by injection e; contradiction)
end

instance : DecidableEq Expr := Expr.decEq

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
  | sliceDim e hi lo => s!"{toString e}[{hi}:{lo}]"
  | index arr idx => s!"{toString arr}[{toString idx}]"

instance : ToString Expr where
  toString := Expr.toString

end Expr

/--
  Statement in the netlist IR

  - Assign: Continuous assignment (combinational logic)
  - Register: Sequential logic (D flip-flop)
  - Memory: Synchronous RAM/BRAM primitive
  - Inst: Instantiation of another module
-/
inductive Stmt where
  | assign (lhs : String) (rhs : Expr) : Stmt
  | register
      (output : String)                  -- Output wire name
      (clock : String)                   -- Clock signal name
      (reset : String × Sparkle.IR.Type.ResetKind)
                                         -- (reset wire name, sync/async)
      (input : Expr)                     -- Input expression
      (initValue : Int)                  -- Reset/initial value
      : Stmt
  | memory
      (name : String)         -- Memory instance name
      (addrWidth : Nat)       -- Address width (size = 2^addrWidth)
      (dataWidth : Nat)       -- Data width
      (clock : String)        -- Clock signal
      (writeAddr : Expr)      -- Write address port (port 0)
      (writeData : Expr)      -- Write data port (port 0)
      (writeEnable : Expr)    -- Write enable port (port 0)
      (readAddr : Expr)       -- Read address port (port 0)
      (readData : String)     -- Read data output wire (port 0)
      (comboRead : Bool := false) -- Combinational (same-cycle) read
      -- EXTRA ports beyond port 0, for true multi-port memories.
      --
      -- Real SRAM macros are not all 1R1W: XiangShan's generated memories
      -- are 61× 1R1W, 31× single read-write (RW), and one 8R8W
      -- (`dt_352x1`, the Difftest debug array).  Port 0 keeps its own
      -- fields so every existing `.memory` pattern match — 72 sites
      -- across the backends — stays valid; additional ports live here and
      -- are honoured by the backends that support them.
      --
      -- Semantics: all ports share `clock`.  Reads see the state BEFORE
      -- this cycle's writes (read-old / write-after-read), matching the
      -- single-port behaviour the CSim/Verilog backends already
      -- implement.  Simultaneous writes to the SAME address are resolved
      -- by port order: the LAST enabled port in the list wins, which is
      -- what a Verilog `always_ff` with sequential `if` statements does.
      (extraWrites : List (Expr × Expr × Expr) := [])
                              -- (addr, data, enable) per additional port
      (extraReads : List (Expr × String) := [])
                              -- (addr, readData wire) per additional port
      : Stmt
  | inst
      (moduleName : String)   -- Name of module to instantiate
      (instName : String)     -- Instance name
      (connections : List (String × Expr))  -- Port connections
      : Stmt
  deriving Repr, BEq, DecidableEq

namespace Stmt

/-- Convert statement to string (for debugging) -/
def toString : Stmt → String
  | assign lhs rhs => s!"{lhs} := {rhs}"
  | register output clock reset input initValue =>
      let (rstName, rstKind) := reset
      let edge := match rstKind with
        | .synchronous => "sync"
        | .asynchronous => "async"
      s!"reg {output} @(posedge {clock}, {edge} {rstName}) <= {input} (init: {initValue})"
  | memory name addrWidth dataWidth clock writeAddr writeData writeEnable readAddr readData comboRead .. =>
      let readKind := if comboRead then "combo_read" else "read"
      s!"memory {name}[2^{addrWidth}][{dataWidth}] @(posedge {clock}) " ++
      s!"write({writeAddr}, {writeData}, {writeEnable}) {readKind}({readAddr}) => {readData}"
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
  parameters  : List Parameter := []
  inputs      : List Port
  outputs     : List Port
  wires       : List Port    -- Internal wires (ignored for primitives)
  body        : List Stmt    -- Logic (ignored for primitives)
  assertions  : List (String × Expr) := []  -- Formal assertions (name, condition)
  isPrimitive : Bool := false  -- True for vendor-provided blackbox modules
  deriving Repr, BEq, DecidableEq

namespace Module

/-- Create an empty module -/
def empty (name : String) : Module :=
  { name := name
  , parameters := []
  , inputs := []
  , outputs := []
  , wires := []
  , body := []
  , isPrimitive := false
  }

/-- Create a primitive (blackbox) module with specified interface -/
def primitive (name : String) (inputs : List Port) (outputs : List Port) : Module :=
  { name := name
  , parameters := []
  , inputs := inputs
  , outputs := outputs
  , wires := []
  , body := []
  , isPrimitive := true
  }

/-! ### Append-vs-prepend perf note

    `addParameter` / `addInput` / `addOutput` / `addWire` / `addStmt`
    are called in the inner loop of synthesis. The natural definition
    (`m.body ++ [s]`)
    is O(n) per call, which makes the whole module-building
    loop O(n²) and dominated runtime for FSM-shape circuits
    (memcached server top-level synth went from ~0.5 s for the
    first multi-output leaf to 32+ s for the sixth — same Δcalls,
    but `module.body` had grown 6× and every `++ [s]` paid
    for that).

    Fix: build the lists in REVERSE order via head-prepend
    (O(1)), then reverse them once at the end of synthesis
    in `Module.finalize`.  External callers that read
    module lists after `finalize` see the same forward
    order they always did. -/

/-- Add a retained module parameter (O(1); reversed by `finalize`). -/
def addParameter (m : Module) (parameter : Parameter) : Module :=
  { m with parameters := parameter :: m.parameters }

/-- Add an input port (O(1); reversed by `finalize`). -/
def addInput (m : Module) (p : Port) : Module :=
  { m with inputs := p :: m.inputs }

/-- Add an output port (O(1); reversed by `finalize`). -/
def addOutput (m : Module) (p : Port) : Module :=
  { m with outputs := p :: m.outputs }

/-- Add an internal wire (O(1); reversed by `finalize`). -/
def addWire (m : Module) (p : Port) : Module :=
  { m with wires := p :: m.wires }

/-- Add a statement to the body (O(1); reversed by `finalize`). -/
def addStmt (m : Module) (s : Stmt) : Module :=
  { m with body := s :: m.body }

/-- Reverse the append-in-reverse lists to forward order.
    Must be called exactly once after all incremental
    additions are done and before any consumer reads
    `m.parameters / inputs / outputs / wires / body`. -/
def finalize (m : Module) : Module :=
  { m with
    parameters := m.parameters.reverse
    inputs     := m.inputs.reverse
    outputs    := m.outputs.reverse
    wires      := m.wires.reverse
    body       := m.body.reverse
  }

/-- Convert module to string (for debugging) -/
def toString (m : Module) : String :=
  let parameterStr := String.intercalate ", "
    (m.parameters.map fun p => s!"{p.name}={p.defaultValue}")
  let inputStr := String.intercalate ", " (m.inputs.map fun p => s!"{p.name}: {p.ty}")
  let outputStr := String.intercalate ", " (m.outputs.map fun p => s!"{p.name}: {p.ty}")
  let wireStr := String.intercalate ", " (m.wires.map fun p => s!"{p.name}: {p.ty}")
  let bodyStr := String.intercalate "\n  " (m.body.map Stmt.toString)
  s!"module {m.name}\n" ++
  s!"  parameters: {parameterStr}\n" ++
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
