/-
  SystemVerilog AST → Sparkle IR Lowering

  Converts parsed SV AST into Sparkle's native IR (Sparkle.IR.AST),
  enabling JIT execution without Verilator.

  Key transformations:
  - always @(posedge clk) with if/else reset → Stmt.register
  - assign lhs = rhs → Stmt.assign
  - SVExpr operators → Sparkle Expr.op with IR Operator
  - Port widths → HWType
-/

import Tools.SVParser.AST
import Tools.SVParser.Parser
import Sparkle.IR.AST
import Sparkle.IR.Type

open Tools.SVParser.AST
open Sparkle.IR.AST
open Sparkle.IR.Type

namespace Tools.SVParser.Lower

-- ============================================================================
-- Type conversion
-- ============================================================================

/-- Convert Verilog bit range to HWType -/
def widthToHWType : Option (Nat × Nat) → HWType
  | none => .bit
  | some (hi, lo) => .bitVector (hi - lo + 1)

/-- Get bit width from SV port/decl width -/
def widthToBits : Option (Nat × Nat) → Nat
  | none => 1
  | some (hi, lo) => hi - lo + 1

-- ============================================================================
-- Environment for tracking declarations
-- ============================================================================

structure LowerEnv where
  portWidths : List (String × Option (Nat × Nat))  -- port name → width
  wireWidths : List (String × Option (Nat × Nat))  -- wire name → width
  regNames   : List String                          -- names declared as reg

def LowerEnv.empty : LowerEnv := { portWidths := [], wireWidths := [], regNames := [] }

def LowerEnv.getWidth (env : LowerEnv) (name : String) : Option (Nat × Nat) :=
  (env.portWidths.find? (·.1 == name) |>.map (·.2)).join <|>
  (env.wireWidths.find? (·.1 == name) |>.map (·.2)).join

def LowerEnv.getHWType (env : LowerEnv) (name : String) : HWType :=
  widthToHWType (env.getWidth name)

def LowerEnv.isReg (env : LowerEnv) (name : String) : Bool :=
  env.regNames.any (· == name)

-- ============================================================================
-- Expression lowering
-- ============================================================================

def lowerUnaryOp : SVUnaryOp → Operator
  | .logNot    => .not
  | .bitNot    => .not
  | .neg       => .neg
  | .reductAnd => .and  -- reduction ops treated as bitwise for now
  | .reductOr  => .or

def lowerBinOp : SVBinOp → Operator
  | .add    => .add
  | .sub    => .sub
  | .mul    => .mul
  | .bitAnd => .and
  | .bitOr  => .or
  | .bitXor => .xor
  | .shl    => .shl
  | .shr    => .shr
  | .asr    => .asr
  | .eq     => .eq
  | .neq    => .eq  -- will need NOT wrapper
  | .lt     => .lt_u
  | .le     => .le_u
  | .gt     => .gt_u
  | .ge     => .ge_u
  | .logAnd => .and
  | .logOr  => .or

def literalToConst : SVLiteral → Expr
  | .decimal (some w) v => .const (Int.ofNat v) w
  | .decimal none v     => .const (Int.ofNat v) 32  -- Verilog default: 32 bits
  | .hex (some w) v     => .const (Int.ofNat v) w
  | .hex none v         => .const (Int.ofNat v) 32
  | .binary (some w) v  => .const (Int.ofNat v) w
  | .binary none v      => .const (Int.ofNat v) 32

private def indexToConst : SVExpr → Option Nat
  | .lit (.decimal _ n) => some n
  | .lit (.hex _ n) => some n
  | .lit (.binary _ n) => some n
  | _ => none

partial def lowerExpr (e : SVExpr) : Expr :=
  match e with
  | .lit l => literalToConst l
  | .ident name => .ref name
  | .unary .reductAnd arg => .op .not [.op .not [lowerExpr arg]]
  | .unary .reductOr arg => .op .not [.op .not [lowerExpr arg]]
  | .unary op arg => .op (lowerUnaryOp op) [lowerExpr arg]
  | .binary .neq lhs rhs => .op .not [.op .eq [lowerExpr lhs, lowerExpr rhs]]
  | .binary op lhs rhs => .op (lowerBinOp op) [lowerExpr lhs, lowerExpr rhs]
  | .ternary cond t el => .op .mux [lowerExpr cond, lowerExpr t, lowerExpr el]
  | .index arr idx =>
    match indexToConst idx with
    | some n => .slice (lowerExpr arr) n n  -- constant bit select
    | none => .index (lowerExpr arr) (lowerExpr idx)  -- dynamic
  | .slice expr hi lo => .slice (lowerExpr expr) hi lo
  | .concat args => .concat (args.map lowerExpr)
  | .repeat_ _count value => lowerExpr value

-- ============================================================================
-- Extract target name from LHS expression
-- ============================================================================

def exprToName : SVExpr → Option String
  | .ident name => some name
  | _ => none

-- ============================================================================
-- Register extraction from always @(posedge clk) blocks
-- ============================================================================

/-- A register assignment found inside an always block -/
structure RegInfo where
  name      : String
  initValue : Nat
  dataExpr  : Expr
  deriving Repr

/-- Extract register assignments from if/else reset pattern:
    if (!rst_n) begin reg <= init; end
    else begin reg <= expr; end -/
def extractRegisters (resetBranch dataBranch : List SVStmt) : List RegInfo :=
  let initMap := resetBranch.filterMap fun s => match s with
    | .nonblockAssign lhs (.lit (.decimal _ v)) => (exprToName lhs).map (·, v)
    | .nonblockAssign lhs (.lit (.hex _ v))     => (exprToName lhs).map (·, v)
    | .nonblockAssign lhs (.lit (.binary _ v))  => (exprToName lhs).map (·, v)
    | _ => none
  let dataMap := dataBranch.filterMap fun s => match s with
    | .nonblockAssign lhs rhs => (exprToName lhs).map (·, lowerExpr rhs)
    | _ => none
  initMap.filterMap fun (name, initVal) =>
    match dataMap.find? (·.1 == name) with
    | some (_, dataExpr) => some { name, initValue := initVal, dataExpr }
    | none => some { name, initValue := initVal, dataExpr := .ref name }

/-- Detect reset pattern in if/else:
    if (!rst_n) → active-low reset, returns (resetSignal, initBranch, dataBranch)
    if (rst)    → active-high reset -/
def detectReset (cond : SVExpr) (thenBranch elseBranch : List SVStmt)
    : Option (String × Bool × List SVStmt × List SVStmt) :=
  match cond with
  | .unary .logNot (.ident rst) =>
    -- if (!rst_n): active-low, then=init, else=data
    some (rst, false, thenBranch, elseBranch)
  | .unary .bitNot (.ident rst) =>
    some (rst, false, thenBranch, elseBranch)
  | .ident rst =>
    -- if (rst): active-high, then=init, else=data
    some (rst, true, thenBranch, elseBranch)
  | _ => none

-- ============================================================================
-- Deep statement collection helpers
-- ============================================================================

/-- Collect all non-blocking assigns from a flat statement list -/
def collectNonblockAssigns (stmts : List SVStmt) : List (String × Expr) :=
  stmts.filterMap fun s => match s with
    | .nonblockAssign lhs rhs => (exprToName lhs).map (·, lowerExpr rhs)
    | _ => none

/-- Recursively collect all non-blocking assigns (through if/else/case) -/
partial def collectNonblockAssignsDeep (stmts : List SVStmt) : List (String × Expr) :=
  stmts.flatMap fun s => match s with
    | .nonblockAssign lhs rhs =>
      match exprToName lhs with
      | some name => [(name, lowerExpr rhs)]
      | none => []
    | .ifElse _ thenB elseB =>
      collectNonblockAssignsDeep thenB ++ collectNonblockAssignsDeep elseB
    | .caseStmt _ arms default_ =>
      let armAssigns := arms.flatMap fun (_, body) => collectNonblockAssignsDeep body
      let defAssigns := match default_ with | some body => collectNonblockAssignsDeep body | none => []
      armAssigns ++ defAssigns
    | .forLoop _ _ _ body => collectNonblockAssignsDeep body
    | _ => []

/-- Recursively collect all blocking assigns as name→expr pairs -/
partial def collectBlockAssignsDeep (stmts : List SVStmt) : List (String × Expr) :=
  stmts.flatMap fun s => match s with
    | .blockAssign lhs rhs =>
      match exprToName lhs with
      | some name => [(name, lowerExpr rhs)]
      | none => []
    | .ifElse _ thenB elseB =>
      collectBlockAssignsDeep thenB ++ collectBlockAssignsDeep elseB
    | .caseStmt _ arms default_ =>
      let armAssigns := arms.flatMap fun (_, body) => collectBlockAssignsDeep body
      let defAssigns := match default_ with | some body => collectBlockAssignsDeep body | none => []
      armAssigns ++ defAssigns
    | _ => []

-- ============================================================================
-- Module lowering
-- ============================================================================

/-- Lower a single SVModule to Sparkle IR Module -/
def lowerModule (svMod : SVModule) : Except String Module := do
  -- Build environment
  let mut env := LowerEnv.empty
  for p in svMod.ports do
    env := { env with portWidths := env.portWidths ++ [(p.name, p.width)] }
  for item in svMod.items do
    match item with
    | .wireDecl name width _ => env := { env with wireWidths := env.wireWidths ++ [(name, width)] }
    | .regDecl name width _ =>
      env := { env with wireWidths := env.wireWidths ++ [(name, width)],
                         regNames := env.regNames ++ [name] }
    | _ => pure ()

  -- Build ports
  let inputs := svMod.ports.filter (·.dir == .input) |>.map fun p =>
    { name := p.name, ty := widthToHWType p.width : Port }
  let outputs := svMod.ports.filter (·.dir == .output) |>.map fun p =>
    { name := p.name, ty := widthToHWType p.width : Port }
  let allPortNames := inputs.map (·.name) ++ outputs.map (·.name)

  -- Helper: check if a wire name is already declared
  let wireExists := fun (wires : List Port) (name : String) =>
    wires.any (·.name == name) || allPortNames.any (· == name)

  -- Build wires list (from wire and reg declarations)
  let mut wires : List Port := []
  for item in svMod.items do
    match item with
    | .wireDecl name width _ => wires := wires ++ [{ name, ty := widthToHWType width }]
    | .regDecl name width arraySize =>
      match arraySize with
      | some size => wires := wires ++ [{ name, ty := .array size (widthToHWType width) }]
      | none => wires := wires ++ [{ name, ty := widthToHWType width }]
    | .integerDecl name => wires := wires ++ [{ name, ty := .bitVector 32 }]
    | _ => pure ()

  -- Add parameters as constant wires (track names to avoid duplicates)
  let mut paramNames : List String := []
  for p in svMod.params do
    let ty := widthToHWType p.width
    if !(paramNames.any (· == p.name)) then
      wires := wires ++ [{ name := p.name, ty }]
      paramNames := paramNames ++ [p.name]
  for item in svMod.items do
    match item with
    | .paramDecl param =>
      let ty := widthToHWType param.width
      if !(paramNames.any (· == param.name)) then
        wires := wires ++ [{ name := param.name, ty }]
        paramNames := paramNames ++ [param.name]
    | _ => pure ()

  -- Build body statements
  let mut body : List Stmt := []

  -- Emit parameter default values as constant assigns
  for p in svMod.params do
    body := body ++ [.assign p.name (lowerExpr p.value)]
  for item in svMod.items do
    match item with
    | .paramDecl param =>
      body := body ++ [.assign param.name (lowerExpr param.value)]
    | _ => pure ()

  for item in svMod.items do
    match item with
    | .contAssign lhs rhs =>
      match exprToName lhs with
      | some name => body := body ++ [.assign name (lowerExpr rhs)]
      | none => throw "continuous assign LHS must be an identifier"
    | .alwaysBlock (.posedge clock) stmts =>
      -- Sequential: try if/else reset pattern first
      match stmts with
      | [.ifElse cond thenB elseB] =>
        match detectReset cond thenB elseB with
        | some (resetSig, isActiveHigh, initBranch, dataBranch) =>
          let regs := extractRegisters initBranch dataBranch
          let resetName := if isActiveHigh then resetSig
                           else s!"_rst_{resetSig}_inv"
          if !isActiveHigh then
            wires := wires ++ [{ name := resetName, ty := .bit }]
            body := body ++ [.assign resetName (.op .not [.ref resetSig])]
          for reg in regs do
            let hwTy := env.getHWType reg.name
            body := body ++ [.register reg.name clock resetName
                              reg.dataExpr reg.initValue]
            if !(wireExists wires reg.name) then
              wires := wires ++ [{ name := reg.name, ty := hwTy }]
        | none =>
          -- No reset pattern: extract all non-blocking assigns as registers with init=0
          let dataMap := collectNonblockAssigns thenB ++ collectNonblockAssigns elseB
          for (name, dataExpr) in dataMap do
            let hwTy := env.getHWType name
            body := body ++ [.register name clock "rst" dataExpr 0]
            if !(wireExists wires name) then
              wires := wires ++ [{ name, ty := hwTy }]
      | _ =>
        -- No if/else wrapper: all non-blocking assigns become registers
        let assigns := collectNonblockAssignsDeep stmts
        for (name, dataExpr) in assigns do
          let hwTy := env.getHWType name
          body := body ++ [.register name clock "rst" dataExpr 0]
          if !(wireExists wires name) then
            wires := wires ++ [{ name, ty := hwTy }]
    | .alwaysBlock .star stmts =>
      -- Combinational: lower blocking assignments
      let assigns := collectBlockAssignsDeep stmts
      for (name, rhs) in assigns do
        body := body ++ [.assign name rhs]
    | .wireDecl name _ (some initExpr) =>
      -- wire x = expr; → assign
      body := body ++ [.assign name (lowerExpr initExpr)]
    | _ => pure ()

  -- Deduplicate wires
  let mut dedupWires : List Port := []
  let mut seenWireNames : List String := []
  let portNames := inputs.map (·.name) ++ outputs.map (·.name)
  for w in wires do
    if !(seenWireNames.any (· == w.name)) && !(portNames.any (· == w.name)) then
      dedupWires := dedupWires ++ [w]
      seenWireNames := seenWireNames ++ [w.name]

  -- Deduplicate registers and handle output reg ports
  let mut dedupBody : List Stmt := []
  let mut seenRegNames : List String := []
  let outputNames := outputs.map (·.name)
  for stmt in body.reverse do
    match stmt with
    | .register name clk rst input init =>
      if !(seenRegNames.any (· == name)) then
        -- For output reg: rename the register to _reg_name, add assign output = _reg_name
        if outputNames.any (· == name) then
          let regName := s!"_reg_{name}"
          dedupBody := [.register regName clk rst input init, .assign name (.ref regName)] ++ dedupBody
          seenRegNames := seenRegNames ++ [name]
          -- Add the internal register wire
          if !(dedupWires.any (·.name == regName)) then
            let hwTy := env.getHWType name
            dedupWires := dedupWires ++ [{ name := regName, ty := hwTy }]
        else
          dedupBody := [stmt] ++ dedupBody
          seenRegNames := seenRegNames ++ [name]
    | _ => dedupBody := [stmt] ++ dedupBody

  pure {
    name := svMod.name
    inputs := inputs
    outputs := outputs
    wires := dedupWires
    body := dedupBody
    isPrimitive := false
  }

/-- Lower a full SV design to Sparkle IR -/
def lowerDesign (svDesign : SVDesign) : Except String Design := do
  let mut modules : List Module := []
  for m in svDesign.modules do
    let lowered ← lowerModule m
    modules := modules ++ [lowered]
  let topName := match svDesign.modules.head? with
    | some m => m.name
    | none => "top"
  pure { topModule := topName, modules }

-- ============================================================================
-- Public API: parse + lower
-- ============================================================================

/-- Memory initialization info from $readmemh -/
structure ReadMemHInfo where
  filename : String
  memName  : String
  deriving Repr

/-- Extract $readmemh info from a parsed SV design -/
def extractReadMemH (svDesign : SVDesign) : List ReadMemHInfo :=
  svDesign.modules.flatMap fun m =>
    m.items.filterMap fun item =>
      match item with
      | .readmemh filename memName => some { filename, memName }
      | _ => none

def parseAndLower (input : String) : Except String Design := do
  let svDesign ← Tools.SVParser.Parser.parse input
  lowerDesign svDesign

def parseAndLowerWithMemInit (input : String) : Except String (Design × List ReadMemHInfo) := do
  let svDesign ← Tools.SVParser.Parser.parse input
  let design ← lowerDesign svDesign
  let memInits := extractReadMemH svDesign
  pure (design, memInits)

end Tools.SVParser.Lower
