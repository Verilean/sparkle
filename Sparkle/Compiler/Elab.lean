/-
  Elaborator & Compiler

  Translates Lean expressions into hardware netlists using metaprogramming.
  This bridges the gap between high-level Signal code and low-level IR.
-/

import Lean
import Sparkle.IR.Builder
import Sparkle.IR.AST
import Sparkle.IR.Type
import Sparkle.Data.BitPack
import Sparkle.Backend.Verilog

namespace Sparkle.Compiler.Elab

open Lean Lean.Elab Lean.Elab.Command Lean.Meta
open Sparkle.IR.Builder
open Sparkle.IR.AST (Operator Port Module Expr Stmt)
open Sparkle.IR.Type
open Sparkle.Backend.Verilog

/-- Compiler state tracking variable mappings and context -/
structure CompilerState where
  varMap : List (FVarId × String) := []  -- Map Lean variables to wire names
  clockWire : Option String := none       -- Name of clock wire (if any)
  resetWire : Option String := none       -- Name of reset wire (if any)

/-- Compiler monad: combines CircuitM builder with MetaM -/
abbrev CompilerM := ReaderT CompilerState (StateT CircuitState MetaM)

namespace CompilerM

/-- Get the current compiler state (from ReaderT) -/
def getCompilerState : CompilerM CompilerState :=
  read

/-- Lookup a variable mapping -/
def lookupVar (fvarId : FVarId) : CompilerM (Option String) := do
  let s ← getCompilerState
  return s.varMap.lookup fvarId

/-- Add a variable mapping (not used in current ReaderT-based implementation) -/
def addVarMapping (fvarId : FVarId) (wireName : String) : CompilerM Unit :=
  -- Note: In the current implementation with ReaderT, we can't modify the compiler state
  -- This is a placeholder for future enhancement
  pure ()

/-- Lift MetaM into CompilerM -/
def liftMetaM {α : Type} (m : MetaM α) : CompilerM α :=
  liftM m

/-- Lift CircuitM operations by modifying the circuit state -/
def makeWire (hint : String) (ty : HWType) : CompilerM String := do
  let cs ← get
  let (name, cs') := CircuitM.makeWire hint ty cs
  set cs'
  return name

def emitAssign (lhs : String) (rhs : Sparkle.IR.AST.Expr) : CompilerM Unit := do
  let cs ← get
  let ((), cs') := CircuitM.emitAssign lhs rhs cs
  set cs'

def addInput (name : String) (ty : HWType) : CompilerM Unit := do
  let cs ← get
  let ((), cs') := CircuitM.addInput name ty cs
  set cs'

def addOutput (name : String) (ty : HWType) : CompilerM Unit := do
  let cs ← get
  let ((), cs') := CircuitM.addOutput name ty cs
  set cs'

def emitRegister (hint : String) (clk : String) (rst : String) (input : Sparkle.IR.AST.Expr) (initVal : Nat) (ty : HWType) : CompilerM String := do
  let cs ← get
  let (name, cs') := CircuitM.emitRegister hint clk rst input initVal ty cs
  set cs'
  return name

end CompilerM

/--
  Primitive Registry: Maps Lean function names to IR operators
-/
def primitiveRegistry : List (Name × Operator) :=
  [
    -- Logical operations
    (``BitVec.and, .and),
    (``BitVec.or, .or),
    (``BitVec.xor, .xor),
    -- Arithmetic operations
    (``BitVec.add, .add),
    (``BitVec.sub, .sub),
    (``BitVec.mul, .mul),
    -- Comparison operations
    (``BEq.beq, .eq),
    (``LT.lt, .lt),
    (``LE.le, .le)
  ]

/-- Check if a name is a known primitive -/
def isPrimitive (name : Name) : Bool :=
  primitiveRegistry.any (fun (n, _) => n == name)

/-- Get the operator for a primitive -/
def getOperator (name : Name) : Option Operator :=
  primitiveRegistry.lookup name

/--
  Infer the hardware type from a Lean type expression.
-/
partial def inferHWType (type : Lean.Expr) : MetaM (Option HWType) := do
  let type ← whnf type

  match type with
  | .app (.const ``BitVec _) (.lit (.natVal n)) =>
    return some (if n == 1 then .bit else .bitVector n)
  | .const ``Bool _ =>
    return some .bit
  | _ =>
    return none

/--
  Infer hardware type from Signal dom α type.
  Extracts the inner type α and calls inferHWType on it.
-/
def inferHWTypeFromSignal (signalType : Lean.Expr) : CompilerM HWType := do
  let signalType ← CompilerM.liftMetaM (whnf signalType)

  match signalType with
  -- Signal dom α pattern - Signal is a structure, match on application
  | .app (.app signalConstr _dom) innerType =>
    -- Check if this is actually the Signal constructor
    match signalConstr with
    | .const name _ =>
      if name.toString.endsWith "Signal" then
        match ← CompilerM.liftMetaM (inferHWType innerType) with
        | some hwType => return hwType
        | none => CompilerM.liftMetaM $ throwError s!"Cannot infer hardware type from {innerType}"
      else
        -- Not a Signal, try fallback
        match ← CompilerM.liftMetaM (inferHWType signalType) with
        | some hwType => return hwType
        | none => return .bitVector 8
    | _ =>
      match ← CompilerM.liftMetaM (inferHWType signalType) with
      | some hwType => return hwType
      | none => return .bitVector 8

  -- Fallback: try to infer directly (for non-Signal types)
  | _ =>
    match ← CompilerM.liftMetaM (inferHWType signalType) with
    | some hwType => return hwType
    | none => return .bitVector 8  -- Default to 8-bit for MVP

/--
  Extract numeric value and width from BitVec literal.
  Handles patterns like: 0#8, 42#16, etc.
-/
def extractBitVecLiteral (expr : Lean.Expr) : CompilerM (Nat × Nat) := do
  let expr ← CompilerM.liftMetaM (whnf expr)

  match expr with
  -- BitVec.ofNat (w : Nat) (x : Nat) : BitVec w
  -- Appears as: (.app (.app (.app (.const ``BitVec.ofNat _) (.lit (.natVal width))) _) (.lit (.natVal value)))
  | .app (.app (.app (.const ``BitVec.ofNat _) (.lit (.natVal width))) _) (.lit (.natVal value)) =>
    return (value, width)

  -- Plain Nat literal - assume 8-bit width
  | .lit (.natVal value) =>
    return (value, 8)

  | _ =>
    CompilerM.liftMetaM $ throwError s!"Expected BitVec literal, got: {expr}"

/--
  Translate a Lean expression to a wire name (creating assignments as needed).
  Returns the wire name holding the result.
-/
partial def translateExprToWire (e : Lean.Expr) (hint : String := "wire") : CompilerM String := do
  let e ← CompilerM.liftMetaM (whnf e)

  match e with
  -- Literal constants
  | .lit (.natVal n) => do
    let wire ← CompilerM.makeWire hint (.bitVector 8)
    CompilerM.emitAssign wire (.const (Int.ofNat n) 8)
    return wire

  -- Variables
  | .fvar fvarId => do
    match ← CompilerM.lookupVar fvarId with
    | some wireName => return wireName
    | none =>
      CompilerM.liftMetaM $ throwError s!"Unbound variable: {fvarId.name}"

  -- Let bindings
  | .letE name _type value body _ => do
    -- Translate the value expression to a wire
    let valueWire ← translateExprToWire value name.toString
    -- For now, we inline the body evaluation
    -- TODO: Properly handle variable bindings in body
    translateExprToWire body hint

  -- Lambda expressions (parameters become inputs)
  | .lam name _ body _ => do
    -- Create an input wire for the parameter
    let paramWire ← CompilerM.makeWire name.toString (.bitVector 8)
    CompilerM.addInput paramWire (.bitVector 8)
    -- TODO: Add proper parameter tracking
    translateExprToWire body hint

  -- Binary operations (primitives)
  | .app (.app (.const name _) arg1) arg2 =>
    if isPrimitive name then
      match getOperator name with
      | some op =>
        let wire1 ← translateExprToWire arg1 "arg1"
        let wire2 ← translateExprToWire arg2 "arg2"
        let resultWire ← CompilerM.makeWire hint (.bitVector 8)
        CompilerM.emitAssign resultWire (.op op [.ref wire1, .ref wire2])
        return resultWire
      | none =>
        CompilerM.liftMetaM $ throwError s!"Unknown operator for primitive: {name}"
    else
      CompilerM.liftMetaM $ throwError s!"Cannot synthesize application: {name}"

  -- BitVec literals
  | .app (.app (.app (.const ``BitVec.ofNat _) (.lit (.natVal width))) _) (.lit (.natVal value)) => do
    let wire ← CompilerM.makeWire hint (.bitVector width)
    CompilerM.emitAssign wire (.const (Int.ofNat value) width)
    return wire

  -- Signal.register primitive: register {dom} {α} init input
  | .app (.app (.app (.app (.const regName _) _dom) _ty) init) input =>
    if regName.toString.endsWith ".register" then do
      -- Extract init value using helper
      let (initVal, _width) ← extractBitVecLiteral init

      -- Translate input signal recursively
      let inputWire ← translateExprToWire input "reg_input"

      -- Infer hardware type from the expression's type
      let exprType ← CompilerM.liftMetaM (inferType e)
      let hwType ← inferHWTypeFromSignal exprType

      -- Emit register with hardcoded clock/reset names (will be added as inputs automatically)
      let regWire ← CompilerM.emitRegister hint "clk" "rst" (.ref inputWire) initVal hwType

      return regWire
    else
      CompilerM.liftMetaM $ throwError s!"Cannot synthesize: {regName}"

  -- Signal.mux primitive: mux {dom} {α} cond thenSig elseSig
  | .app (.app (.app (.app (.app (.const muxName _) _dom) _ty) cond) thenSig) elseSig =>
    if muxName.toString.endsWith ".mux" then do
      -- Translate all three arguments to wire names
      let condWire ← translateExprToWire cond "mux_cond"
      let thenWire ← translateExprToWire thenSig "mux_then"
      let elseWire ← translateExprToWire elseSig "mux_else"

      -- Create result wire
      let resultWire ← CompilerM.makeWire hint (.bitVector 8)

      -- Emit assignment with mux operator (3 arguments required)
      CompilerM.emitAssign resultWire (.op .mux [.ref condWire, .ref thenWire, .ref elseWire])

      return resultWire
    else
      CompilerM.liftMetaM $ throwError s!"Cannot synthesize: {muxName}"

  -- Unsupported Signal operations
  | .app (.const name _) _ =>
    if name.toString.startsWith "Sparkle.Core.Signal" then
      CompilerM.liftMetaM $ throwError s!"Signal operation '{name}' is not yet supported for synthesis. Supported: register, mux, pure, map. Consider using manual IR construction."
    else
      CompilerM.liftMetaM $ throwError s!"Cannot synthesize: {name}"

  | _ =>
    CompilerM.liftMetaM $ throwError s!"Cannot synthesize expression: {e}"

/--
  Translate a Lean expression to an IR expression (for use in assignments).
-/
partial def translateExpr (e : Lean.Expr) : CompilerM Sparkle.IR.AST.Expr := do
  let e ← CompilerM.liftMetaM (whnf e)

  match e with
  -- Literal constants
  | .lit (.natVal n) =>
    return .const (Int.ofNat n) 8

  -- Variables
  | .fvar fvarId => do
    match ← CompilerM.lookupVar fvarId with
    | some wireName => return .ref wireName
    | none =>
      CompilerM.liftMetaM $ throwError s!"Unbound variable: {fvarId.name}"

  -- Binary operations (primitives)
  | .app (.app (.const name _) arg1) arg2 =>
    if isPrimitive name then
      match getOperator name with
      | some op =>
        let e1 ← translateExpr arg1
        let e2 ← translateExpr arg2
        return .op op [e1, e2]
      | none =>
        CompilerM.liftMetaM $ throwError s!"Unknown operator for primitive: {name}"
    else
      CompilerM.liftMetaM $ throwError s!"Cannot synthesize application: {name}"

  -- BitVec literals
  | .app (.app (.app (.const ``BitVec.ofNat _) (.lit (.natVal width))) _) (.lit (.natVal value)) =>
    return .const (Int.ofNat value) width

  | _ =>
    CompilerM.liftMetaM $ throwError s!"Cannot synthesize expression: {e}"

/--
  Synthesize a simple combinational function into a hardware module.

  Takes a function definition and compiles it to IR.
-/
def synthesizeCombinational (declName : Name) : MetaM Sparkle.IR.AST.Module := do
  -- Get the declaration
  let constInfo ← getConstInfo declName

  match constInfo with
  | .defnInfo defnInfo =>
    let body := defnInfo.value
    let _type := defnInfo.type

    -- Create initial states
    let compilerState : CompilerState := { varMap := [], clockWire := none, resetWire := none }
    let circuitState := CircuitM.init declName.toString

    -- Translate the function body
    let compiler : CompilerM String := do
      -- Process the body to get result wire
      let resultWire ← translateExprToWire body "result"

      -- Add output port
      CompilerM.addOutput "out" (.bitVector 8)
      CompilerM.emitAssign "out" (.ref resultWire)

      return resultWire

    let (_, finalCircuitState) ← (compiler.run compilerState).run circuitState

    -- POST-PROCESSING: Add clock and reset inputs if any registers exist
    let mut module := finalCircuitState.module
    let hasRegisters := module.body.any (fun stmt =>
      match stmt with
      | .register _ _ _ _ _ => true
      | _ => false
    )

    if hasRegisters then
      -- Add clock and reset as first inputs
      module := module.addInput { name := "clk", ty := .bit }
      module := module.addInput { name := "rst", ty := .bit }

    return module

  | _ =>
    throwError s!"Cannot synthesize {declName}: not a definition"

/--
  Pretty-print a module's IR for debugging.
-/
def printModule (m : Sparkle.IR.AST.Module) : MetaM Unit := do
  IO.println s!"Module: {m.name}"
  IO.println s!"Inputs: {m.inputs.length}"
  for input in m.inputs do
    IO.println s!"  - {input.name}: {input.ty}"
  IO.println s!"Outputs: {m.outputs.length}"
  for output in m.outputs do
    IO.println s!"  - {output.name}: {output.ty}"
  IO.println s!"Wires: {m.wires.length}"
  for wire in m.wires do
    IO.println s!"  - {wire.name}: {wire.ty}"
  IO.println s!"Statements: {m.body.length}"
  for stmt in m.body do
    IO.println s!"  {stmt}"

/--
  Synthesize command: Compiles a Lean function to hardware IR and prints it.

  Usage: #synthesize myFunction
-/
elab "#synthesize" id:ident : command => do
  let declName := id.getId
  Lean.Elab.Command.liftTermElabM do
    try
      let module ← synthesizeCombinational declName
      printModule module
      IO.println "\n-- IR successfully generated!"
    catch _ =>
      logError m!"Synthesis failed for {declName}"

/--
  Synthesize to Verilog command: Compiles and generates SystemVerilog.

  Usage: #synthesizeVerilog myFunction
-/
elab "#synthesizeVerilog" id:ident : command => do
  let declName := id.getId
  Lean.Elab.Command.liftTermElabM do
    try
      let module ← synthesizeCombinational declName
      let verilog := toVerilog module
      IO.println verilog
      IO.println "\n-- Verilog successfully generated!"
    catch _ =>
      logError m!"Synthesis failed for {declName}"

end Sparkle.Compiler.Elab
