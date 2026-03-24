/-
  Verilog IR → Lean Semantic Model Generator

  Extracts a pure state-machine model from Sparkle IR (Module),
  generating Lean source code with State/Input/nextState definitions
  suitable for formal verification with `simp`, `omega`, `bv_decide`.

  Pipeline:
    Verilog → [SVParser] → IR Module → [extractModel] → SemanticModel → [generateLean] → .lean source
-/

import Sparkle.IR.AST
import Sparkle.IR.Type

open Sparkle.IR.AST
open Sparkle.IR.Type

namespace Tools.SVParser.Verify

-- ============================================================================
-- Semantic Model types
-- ============================================================================

/-- A register extracted from the IR -/
structure RegField where
  name : String
  width : Nat
  initValue : Int
  nextExpr : Expr
  deriving Repr

/-- An input port -/
structure InputField where
  name : String
  width : Nat
  deriving Repr

/-- Extracted semantic model of a hardware module -/
structure SemanticModel where
  moduleName : String
  registers : List RegField
  inputs : List InputField
  deriving Repr

-- ============================================================================
-- Model extraction from IR
-- ============================================================================

/-- Extract semantic model from an IR Module -/
def extractModel (m : Module) : SemanticModel :=
  let regs := m.body.filterMap fun stmt => match stmt with
    | .register name _clk _rst input initVal =>
      let width := match m.wires.find? (fun w => w.name == name) with
        | some p => p.ty.bitWidth
        | none => match m.outputs.find? (fun w => w.name == name) with
          | some p => p.ty.bitWidth
          | none => 32
      some { name, width, initValue := initVal, nextExpr := input }
    | _ => none
  let inputs := m.inputs.filter (fun p => p.name != "clk" && p.name != "rst")
    |>.map fun p => { name := p.name, width := p.ty.bitWidth : InputField }
  { moduleName := m.name, registers := regs, inputs := inputs }

-- ============================================================================
-- Wire inlining (substitute assign references)
-- ============================================================================

/-- Build a map of wire name → expression from Stmt.assign -/
def collectAssigns (body : List Stmt) : List (String × Expr) :=
  body.filterMap fun stmt => match stmt with
    | .assign name rhs => some (name, rhs)
    | _ => none

/-- Recursively inline wire references with their definitions -/
partial def inlineAssigns (assigns : List (String × Expr)) : Expr → Expr
  | .ref name =>
    match assigns.find? (·.1 == name) with
    | some (_, rhs) => inlineAssigns assigns rhs
    | none => .ref name
  | .op operator args => .op operator (args.map (inlineAssigns assigns))
  | .concat args => .concat (args.map (inlineAssigns assigns))
  | .slice e hi lo => .slice (inlineAssigns assigns e) hi lo
  | .index a i => .index (inlineAssigns assigns a) (inlineAssigns assigns i)
  | e => e  -- const passes through

-- ============================================================================
-- Width inference
-- ============================================================================

/-- Infer the BitVec width of an IR expression -/
partial def inferWidth (regWidths inputWidths : List (String × Nat)) : Expr → Nat
  | .const _ w => w
  | .ref name =>
    match regWidths.find? (·.1 == name) with
    | some (_, w) => w
    | none => match inputWidths.find? (·.1 == name) with
      | some (_, w) => w
      | none => 32
  | .op .eq _ => 1
  | .op .lt_u _ => 1
  | .op .lt_s _ => 1
  | .op .le_u _ => 1
  | .op .le_s _ => 1
  | .op .gt_u _ => 1
  | .op .gt_s _ => 1
  | .op .ge_u _ => 1
  | .op .ge_s _ => 1
  | .op .mux args => match args with
    | [_, t, _] => inferWidth regWidths inputWidths t
    | _ => 32
  | .op _ args => match args with
    | a :: _ => inferWidth regWidths inputWidths a
    | _ => 32
  | .slice _ hi lo => hi - lo + 1
  | .concat args => args.foldl (fun acc a => acc + inferWidth regWidths inputWidths a) 0
  | .index _ _ => 32

-- ============================================================================
-- IR Expr → Lean source string
-- ============================================================================

/-- Sanitize a name for Lean (replace special chars) -/
private def leanName (s : String) : String :=
  s.map fun c => if c == '$' || c == '.' then '_' else c

/-- Convert IR Expr to a Lean BitVec expression string -/
partial def irExprToLean (expr : Expr) (regWidths inputWidths : List (String × Nat))
    (stateVar inputVar : String) : String :=
  let go (e : Expr) := irExprToLean e regWidths inputWidths stateVar inputVar
  let width := inferWidth regWidths inputWidths expr
  match expr with
  | .const v w =>
    if v < 0 then s!"(BitVec.ofInt {w} ({v}))"
    else s!"({v}#{ w})"
  | .ref name =>
    if regWidths.any (·.1 == name) then s!"{stateVar}.{leanName name}"
    else if inputWidths.any (·.1 == name) then s!"{inputVar}.{leanName name}"
    else s!"{leanName name}"
  | .op .mux [cond, thenVal, elseVal] =>
    let condW := inferWidth regWidths inputWidths cond
    s!"(if {go cond} != (0 : BitVec {condW}) then {go thenVal} else {go elseVal})"
  | .op .add [a, b] => s!"({go a} + {go b})"
  | .op .sub [a, b] => s!"({go a} - {go b})"
  | .op .mul [a, b] => s!"({go a} * {go b})"
  | .op .and [a, b] => s!"({go a} &&& {go b})"
  | .op .or [a, b] => s!"({go a} ||| {go b})"
  | .op .xor [a, b] => s!"({go a} ^^^ {go b})"
  | .op .not [a] =>
    if width <= 1 then s!"(if {go a} == (0 : BitVec {width}) then (1 : BitVec {width}) else (0 : BitVec {width}))"
    else s!"(~~~ {go a})"
  | .op .eq [a, b] =>
    s!"(if {go a} == {go b} then (1 : BitVec 1) else (0 : BitVec 1))"
  | .op .lt_u [a, b] => s!"(if {go a} < {go b} then (1 : BitVec 1) else (0 : BitVec 1))"
  | .op .shl [a, b] => s!"({go a} <<< {go b})"
  | .op .shr [a, b] => s!"({go a} >>> {go b})"
  | .op .asr [a, b] =>
    s!"(BitVec.sshiftRight {go a} {go b}.toNat)"
  | .op .neg [a] => s!"(- {go a})"
  | .slice e hi lo => s!"(BitVec.extractLsb' {lo} {hi - lo + 1} {go e})"
  | .concat args =>
    match args with
    | [] => "(0 : BitVec 0)"
    | [a] => go a
    | a :: rest =>
      let aStr := go a
      let restStr := go (Expr.concat rest)
      s!"({aStr} ++ {restStr})"
  | _ => s!"sorry /- unsupported expr: {repr expr} -/"

-- ============================================================================
-- Lean source generation
-- ============================================================================

/-- Generate complete Lean source file from a semantic model -/
def generateLean (model : SemanticModel) : String :=
  let ns := leanName model.moduleName
  let regWidths := model.registers.map fun r => (r.name, r.width)
  let inputWidths := model.inputs.map fun i => (i.name, i.width)

  -- State structure
  let stateFields := model.registers.map fun r =>
    s!"  {leanName r.name} : BitVec {r.width}"
  let stateStruct := s!"structure State where\n" ++
    String.intercalate "\n" stateFields ++
    "\n  deriving DecidableEq, Repr, BEq, Inhabited\n"

  -- Input structure
  let inputFields := model.inputs.map fun i =>
    s!"  {leanName i.name} : BitVec {i.width}"
  let inputStruct := s!"structure Input where\n" ++
    String.intercalate "\n" inputFields ++
    "\n  deriving DecidableEq, Repr, BEq, Inhabited\n"

  -- nextState function
  let regAssigns := model.registers.map fun r =>
    s!"    {leanName r.name} := {irExprToLean r.nextExpr regWidths inputWidths "s" "i"}"
  let nextStateFn := "def nextState (s : State) (i : Input) : State :=\n  {\n" ++
    String.intercalate "\n" regAssigns ++
    "\n  }\n"

  -- Initial state
  let initFields := model.registers.map fun r =>
    s!"    {leanName r.name} := ({r.initValue}#{ r.width})"
  let initState := "def initState : State :=\n  {\n" ++
    String.intercalate "\n" initFields ++
    "\n  }\n"

  -- Assemble
  s!"/-\n  Auto-generated semantic model from Verilog module: {model.moduleName}\n  Generated by Sparkle SVParser Verify\n-/\n\n" ++
  s!"namespace {ns}.Verify\n\n" ++
  stateStruct ++ "\n" ++
  inputStruct ++ "\n" ++
  nextStateFn ++ "\n" ++
  initState ++ "\n" ++
  s!"end {ns}.Verify\n"

-- ============================================================================
-- Combined pipeline: Module → Lean source
-- ============================================================================

/-- Extract model from IR Module and generate Lean verification source -/
def moduleToLean (m : Module) : String :=
  let model := extractModel m
  let assigns := collectAssigns m.body
  -- Inline wire references in all register next-expressions
  let model := { model with
    registers := model.registers.map fun r =>
      { r with nextExpr := inlineAssigns assigns r.nextExpr }
  }
  generateLean model

end Tools.SVParser.Verify
