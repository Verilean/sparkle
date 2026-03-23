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

/-- Set of array-typed register names for distinguishing bit-select vs array access -/
private def arrayNames : List String := []  -- populated per-module during lowering

private def indexToConst : SVExpr → Option Nat
  | .lit (.decimal _ n) => some n
  | .lit (.hex _ n) => some n
  | .lit (.binary _ n) => some n
  | _ => none

private def isArrayName (name : String) : Bool :=
  -- Heuristic: names ending in common array patterns or known PicoRV32 arrays
  name == "cpuregs" || name == "memory" || name.endsWith "_mem" || name.endsWith "_ram"

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
    | none =>
      -- Check if base is an array-typed register (real array access)
      -- vs scalar bit-select
      match arr with
      | .ident name =>
        if isArrayName name then
          .index (lowerExpr arr) (lowerExpr idx)  -- array access
        else
          .op .and [.op .shr [lowerExpr arr, lowerExpr idx], .const 1 1]  -- bit select
      | _ =>
        .op .and [.op .shr [lowerExpr arr, lowerExpr idx], .const 1 1]  -- dynamic
  | .slice expr hi lo => .slice (lowerExpr expr) hi lo
  | .concat args => .concat (args.map lowerExpr)
  | .repeat_ _count value => lowerExpr value

-- ============================================================================
-- Extract target name from LHS expression
-- ============================================================================

def exprToName : SVExpr → Option String
  | .ident name => if isArrayName name then none else some name
  | .index (.ident name) _ => if isArrayName name then none else some name
  | .slice (.ident name) _ _ => some name
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
-- Imperative → Dataflow conversion (if/else/case → mux chains)
-- ============================================================================

/-- Collect all register names assigned (non-blocking) anywhere in statements -/
partial def collectAllRegNames (stmts : List SVStmt) : List String :=
  stmts.flatMap fun s => match s with
    | .nonblockAssign lhs _ =>
      match exprToName lhs with | some n => [n] | none => []
    | .ifElse _ thenB elseB =>
      collectAllRegNames thenB ++ collectAllRegNames elseB
    | .caseStmt _ arms default_ =>
      let armNames := arms.flatMap fun (_, body) => collectAllRegNames body
      let defNames := match default_ with | some d => collectAllRegNames d | none => []
      armNames ++ defNames
    | .forLoop _ _ _ body => collectAllRegNames body
    | _ => []

/-- For a given register name, compute its next-value expression from
    imperative if/else/case statements by building mux chains.

    If reg is not assigned in a branch, the default is `Expr.ref reg` (hold value). -/
partial def stmtsToMuxExpr (regName : String) (stmts : List SVStmt) : Expr :=
  stmts.foldl (fun current s => stmtToMuxExpr regName s current) (.ref regName)
where
  stmtToMuxExpr (regName : String) (s : SVStmt) (current : Expr) : Expr :=
    match s with
    | .nonblockAssign lhs rhs =>
      match exprToName lhs with
      | some n => if n == regName then lowerExpr rhs else current
      | none => current
    | .ifElse cond thenB elseB =>
      let thenExpr := stmtsToMuxExpr regName thenB
      let elseExpr := stmtsToMuxExpr regName elseB
      -- Only emit mux if this register is assigned in either branch
      let thenHasReg := (collectAllRegNames thenB).any (· == regName)
      let elseHasReg := (collectAllRegNames elseB).any (· == regName)
      if thenHasReg || elseHasReg then
        let thenVal := if thenHasReg then thenExpr else current
        let elseVal := if elseHasReg then elseExpr else current
        .op .mux [lowerExpr cond, thenVal, elseVal]
      else current
    | .caseStmt sel arms default_ =>
      -- Build nested mux chain: case arm1 => val1, case arm2 => val2, ...
      let anyArm := arms.any fun (_, body) =>
        (collectAllRegNames body).any (· == regName)
      let defHasReg := match default_ with
        | some d => (collectAllRegNames d).any (· == regName) | none => false
      if anyArm || defHasReg then
        let defResult := match default_ with
          | some d => if defHasReg then stmtsToMuxExpr regName d else current
          | none => current
        -- Build mux chain from last arm to first using foldl
        arms.reverse.foldl (fun acc (labels, body) =>
          let bodyHasReg := (collectAllRegNames body).any (· == regName)
          if bodyHasReg then
            let bodyExpr := stmtsToMuxExpr regName body
            let selExpr := lowerExpr sel
            let cond := labels.foldl (fun acc label =>
              let eq := Expr.op .eq [selExpr, lowerExpr label]
              if acc == Expr.const 0 1 then eq
              else Expr.op .or [acc, eq]
            ) (Expr.const 0 1)
            .op .mux [cond, bodyExpr, acc]
          else acc
        ) defResult
      else current
    | _ => current

/-- Collect all blocking assigns as name→expr pairs (for combinational always) -/
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

/-- For combinational always, convert to mux expressions per signal -/
partial def stmtsToMuxExprBlocking (sigName : String) (stmts : List SVStmt) : Expr :=
  stmts.foldl (fun current s => stmtToMuxBlocking sigName s current) (.ref sigName)
where
  stmtToMuxBlocking (sigName : String) (s : SVStmt) (current : Expr) : Expr :=
    match s with
    | .blockAssign lhs rhs =>
      match exprToName lhs with
      | some n => if n == sigName then lowerExpr rhs else current
      | none => current
    | .ifElse cond thenB elseB =>
      let thenNames := collectBlockNames thenB
      let elseNames := collectBlockNames elseB
      if thenNames.any (· == sigName) || elseNames.any (· == sigName) then
        let thenVal := if thenNames.any (· == sigName) then stmtsToMuxExprBlocking sigName thenB else current
        let elseVal := if elseNames.any (· == sigName) then stmtsToMuxExprBlocking sigName elseB else current
        .op .mux [lowerExpr cond, thenVal, elseVal]
      else current
    | .caseStmt sel arms default_ =>
      let anyArm := arms.any fun (_, body) => (collectBlockNames body).any (· == sigName)
      let defHasReg := match default_ with | some d => (collectBlockNames d).any (· == sigName) | none => false
      if anyArm || defHasReg then
        let defResult := match default_ with
          | some d => if defHasReg then stmtsToMuxExprBlocking sigName d else current
          | none => current
        arms.reverse.foldl (fun acc (labels, body) =>
          if (collectBlockNames body).any (· == sigName) then
            let bodyExpr := stmtsToMuxExprBlocking sigName body
            let selExpr := lowerExpr sel
            let cond := labels.foldl (fun acc' label =>
              let eq := Expr.op .eq [selExpr, lowerExpr label]
              if acc' == Expr.const 0 1 then eq else Expr.op .or [acc', eq]
            ) (Expr.const 0 1)
            .op .mux [cond, bodyExpr, acc]
          else acc
        ) defResult
      else current
    | _ => current
  collectBlockNames (stmts : List SVStmt) : List String :=
    stmts.flatMap fun s => match s with
      | .blockAssign lhs _ => match exprToName lhs with | some n => [n] | none => []
      | .ifElse _ t e => collectBlockNames t ++ collectBlockNames e
      | .caseStmt _ arms d =>
        (arms.flatMap fun (_, b) => collectBlockNames b) ++
        (match d with | some b => collectBlockNames b | none => [])
      | _ => []

/-- Collect all blocking-assigned signal names recursively -/
partial def collectBlockNamesTop (stmts : List SVStmt) : List String :=
  stmts.flatMap fun s => match s with
    | .blockAssign lhs _ => match exprToName lhs with | some n => [n] | none => []
    | .ifElse _ t e => collectBlockNamesTop t ++ collectBlockNamesTop e
    | .caseStmt _ arms d =>
      (arms.flatMap fun (_, b) => collectBlockNamesTop b) ++
      (match d with | some b => collectBlockNamesTop b | none => [])
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
      -- Sequential: extract all register names, then build mux expression per register
      -- Detect reset pattern and extract init values
      let mut resetName := "rst"
      let mut initMap : List (String × Nat) := []
      let mut dataStmts := stmts
      match stmts with
      | [.ifElse cond thenB elseB] =>
        match detectReset cond thenB elseB with
        | some (resetSig, isActiveHigh, initBranch, dataBranch) =>
          resetName := if isActiveHigh then resetSig else s!"_rst_{resetSig}_inv"
          if !isActiveHigh then
            wires := wires ++ [{ name := resetName, ty := .bit }]
            body := body ++ [.assign resetName (.op .not [.ref resetSig])]
          initMap := initBranch.filterMap fun s => match s with
            | .nonblockAssign lhs (.lit (.decimal _ v)) => (exprToName lhs).map (·, v)
            | .nonblockAssign lhs (.lit (.hex _ v)) => (exprToName lhs).map (·, v)
            | .nonblockAssign lhs (.lit (.binary _ v)) => (exprToName lhs).map (·, v)
            | _ => none
          dataStmts := dataBranch
        | none => pure ()
      | _ => pure ()

      -- Collect all register names assigned in the data branch
      let regNames := (collectAllRegNames dataStmts).eraseDups

      -- For each register, build mux expression from the data branch
      for regName in regNames do
        let hwTy := env.getHWType regName
        let initVal := match initMap.find? (·.1 == regName) with
          | some (_, v) => v
          | none => 0
        let dataExpr := stmtsToMuxExpr regName dataStmts
        body := body ++ [.register regName clock resetName dataExpr initVal]
        if !(wireExists wires regName) then
          wires := wires ++ [{ name := regName, ty := hwTy }]

    | .alwaysBlock .star stmts =>
      -- Combinational: build mux expressions per signal
      let sigNames := collectBlockNamesTop stmts |>.eraseDups
      for sigName in sigNames do
        let expr := stmtsToMuxExprBlocking sigName stmts
        body := body ++ [.assign sigName expr]
    | .wireDecl name _ (some initExpr) =>
      -- wire x = expr; → assign
      body := body ++ [.assign name (lowerExpr initExpr)]
    | .regDecl name width (some arraySize) =>
      -- Array reg → Stmt.memory for JIT memory access
      let dataWidth := widthToBits width
      let addrWidth := Nat.log2 arraySize + (if Nat.isPowerOfTwo arraySize then 0 else 1)
      body := body ++ [.memory name addrWidth dataWidth "clk"
        (.const 0 addrWidth) (.const 0 dataWidth) (.const 0 1)  -- dummy write
        (.const 0 addrWidth) s!"{name}_rdata" true]              -- combo read (no register)
      -- Add read data wire
      wires := wires ++ [{ name := s!"{name}_rdata", ty := widthToHWType width }]
    | .instantiation modName instName conns =>
      -- Module instantiation → Stmt.inst
      let irConns := conns.map fun (portName, expr) => (portName, lowerExpr expr)
      body := body ++ [.inst modName instName irConns]
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
          dedupBody := [.assign name (.ref regName), .register regName clk rst input init] ++ dedupBody
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

/-- Prefix all wire/register names in an expression -/
partial def prefixExprNames (pfx : String) (nameSet : List String) : Expr → Expr
  | .ref name => if nameSet.any (· == name) then .ref s!"{pfx}_{name}" else .ref name
  | .op o args => .op o (args.map (prefixExprNames pfx nameSet))
  | .concat args => .concat (args.map (prefixExprNames pfx nameSet))
  | .slice e hi lo => .slice (prefixExprNames pfx nameSet e) hi lo
  | .index arr idx => .index (prefixExprNames pfx nameSet arr) (prefixExprNames pfx nameSet idx)
  | e => e

/-- Flatten a design: inline all sub-module instantiations into a single module -/
def flattenDesign (design : Design) : Design := Id.run do
  let moduleMap := design.modules
  match design.modules.find? fun (m : Module) => m.name == design.topModule with
  | none => return design
  | some top =>
    let mut flatWires := top.wires
    let mut flatBody : List Stmt := []

    for stmt in top.body do
      match stmt with
      | .inst modName instName conns =>
        -- Find the sub-module
        match moduleMap.find? fun (m : Module) => m.name == modName with
        | none => flatBody := flatBody ++ [stmt]  -- keep as-is if not found
        | some subMod =>
          -- Collect all internal names in sub-module
          let subNames := subMod.wires.map (·.name) ++
                          subMod.inputs.map (·.name) ++
                          subMod.outputs.map (·.name)

          -- Add prefixed wires from sub-module
          for w in subMod.wires do
            flatWires := flatWires ++ [{ name := s!"{instName}_{w.name}", ty := w.ty }]
          -- Add prefixed wires for sub-module's input/output ports (as internal wires)
          for p in subMod.inputs do
            flatWires := flatWires ++ [{ name := s!"{instName}_{p.name}", ty := p.ty }]
          for p in subMod.outputs do
            flatWires := flatWires ++ [{ name := s!"{instName}_{p.name}", ty := p.ty }]

          -- Wire port connections:
          -- Input ports: assign instName_portName = parentExpr
          -- Output ports: assign parentWire = instName_portName
          let inputNames := subMod.inputs.map (·.name)
          let outputNames := subMod.outputs.map (·.name)
          for (portName, expr) in conns do
            if inputNames.any (· == portName) then
              -- Input: parent drives sub-module's port
              flatBody := flatBody ++ [.assign s!"{instName}_{portName}" expr]
            else if outputNames.any (· == portName) then
              -- Output: sub-module drives parent's wire
              -- expr is typically .ref "parentWire"
              match expr with
              | .ref parentWire =>
                flatBody := flatBody ++ [.assign parentWire (.ref s!"{instName}_{portName}")]
              | _ => pure ()  -- complex expression, skip

          -- Add prefixed body statements from sub-module
          for s in subMod.body do
            let prefixed := match s with
              | .assign name rhs =>
                .assign s!"{instName}_{name}" (prefixExprNames instName subNames rhs)
              | .register name clk rst input init =>
                .register s!"{instName}_{name}" s!"{instName}_{clk}" s!"{instName}_{rst}"
                  (prefixExprNames instName subNames input) init
              | .inst subModName subInstName subConns =>
                -- Nested instantiation: prefix and keep
                .inst subModName s!"{instName}_{subInstName}"
                  (subConns.map fun (pn, e) => (pn, prefixExprNames instName subNames e))
              | other => other
            flatBody := flatBody ++ [prefixed]
      | other => flatBody := flatBody ++ [other]

    let flatModule : Module := {
      name := top.name
      inputs := top.inputs
      outputs := top.outputs
      wires := flatWires
      body := flatBody
      isPrimitive := false
    }
    return { topModule := design.topModule, modules := [flatModule] }

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

def parseAndLowerFlat (input : String) : Except String Design := do
  let svDesign ← Tools.SVParser.Parser.parse input
  let design ← lowerDesign svDesign
  pure (flattenDesign design)

def parseAndLowerWithMemInit (input : String) : Except String (Design × List ReadMemHInfo) := do
  let svDesign ← Tools.SVParser.Parser.parse input
  let design ← lowerDesign svDesign
  let memInits := extractReadMemH svDesign
  pure (design, memInits)

end Tools.SVParser.Lower
