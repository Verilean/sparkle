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
  | .logAnd => .and  -- unreachable: handled in lowerExpr as (a!=0) & (b!=0)
  | .logOr  => .or   -- unreachable: handled in lowerExpr as (a!=0) | (b!=0)

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
  | .unary .reductAnd arg =>
    -- Reduction AND: &x → all bits set → (x XOR 0xFF...FF) == 0
    -- Use XOR with -1 (all ones) for bitwise inversion, then compare with 0
    .op .eq [.op .xor [lowerExpr arg, .const (-1) 32], .const 0 32]
  | .unary .reductOr arg =>
    -- Reduction OR: |x → any bit set → x != 0
    .op .not [.op .eq [lowerExpr arg, .const 0 32]]
  | .unary .logNot arg =>
    -- Logical NOT: !x → (x == 0) — reduces multi-bit to bool
    .op .eq [lowerExpr arg, .const 0 32]
  | .unary op arg => .op (lowerUnaryOp op) [lowerExpr arg]
  | .binary .neq lhs rhs => .op .not [.op .eq [lowerExpr lhs, lowerExpr rhs]]
  | .binary .logAnd lhs rhs =>
    -- Logical AND: a && b → (a != 0) & (b != 0) — must reduce multi-bit operands to bool
    let la := .op .not [.op .eq [lowerExpr lhs, .const 0 32]]
    let lb := .op .not [.op .eq [lowerExpr rhs, .const 0 32]]
    .op .and [la, lb]
  | .binary .logOr lhs rhs =>
    -- Logical OR: a || b → (a != 0) | (b != 0)
    let la := .op .not [.op .eq [lowerExpr lhs, .const 0 32]]
    let lb := .op .not [.op .eq [lowerExpr rhs, .const 0 32]]
    .op .or [la, lb]
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
private def hasSubstr (s sub : String) : Bool := (s.splitOn sub).length > 1

def isResetName (name : String) : Bool :=
  name == "rst" || name == "reset" || name == "resetn" || name == "rst_n" ||
  name == "arst" || name == "arst_n" ||
  hasSubstr name "reset" || hasSubstr name "rst"

def detectReset (cond : SVExpr) (thenBranch elseBranch : List SVStmt)
    : Option (String × Bool × List SVStmt × List SVStmt) :=
  match cond with
  | .unary .logNot (.ident rst) =>
    -- if (!rst_n): active-low, then=init, else=data
    if isResetName rst then some (rst, false, thenBranch, elseBranch) else none
  | .unary .bitNot (.ident rst) =>
    if isResetName rst then some (rst, false, thenBranch, elseBranch) else none
  | .ident rst =>
    -- if (rst): active-high, then=init, else=data
    if isResetName rst then some (rst, true, thenBranch, elseBranch) else none
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
partial def stmtsToMuxExpr (regName : String) (stmts : List SVStmt) (base : Expr := .ref regName) : Expr :=
  stmts.foldl (fun current s => stmtToMuxExpr regName s current) base
where
  stmtToMuxExpr (regName : String) (s : SVStmt) (current : Expr) : Expr :=
    match s with
    | .nonblockAssign lhs rhs =>
      match exprToName lhs with
      | some n =>
        if n == regName then
          -- Skip don't-care ('bx) cleanup assigns
          match rhs with
          | .lit (.binary none 0) => current
          | .lit (.hex none 0) => current
          | _ => lowerExpr rhs
        else current
      | none => current
    | .ifElse cond thenB elseB =>
      let thenExpr := stmtsToMuxExpr regName thenB current
      let elseExpr := stmtsToMuxExpr regName elseB current
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
          | some d => if defHasReg then stmtsToMuxExpr regName d current else current
          | none => current
        -- Build mux chain from last arm to first using foldl
        arms.reverse.foldl (fun acc (labels, body) =>
          let bodyHasReg := (collectAllRegNames body).any (· == regName)
          if bodyHasReg then
            let bodyExpr := stmtsToMuxExpr regName body acc
            let selExpr := lowerExpr sel
            -- For case (1'b1), labels are conditions themselves (priority encoding)
            -- For normal case, labels are values to compare against sel
            let isCase1b1 := match sel with
              | .lit (.binary (some 1) 1) => true
              | .lit (.decimal (some 1) 1) => true
              | _ => false
            let cond := labels.foldl (fun acc label =>
              let c := if isCase1b1
                then lowerExpr label  -- label IS the condition
                else Expr.op .eq [selExpr, lowerExpr label]  -- sel == label
              if acc == Expr.const 0 1 then c
              else Expr.op .or [acc, c]
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

/-- For combinational/blocking assigns, convert to mux expressions per signal.
    The default is the first assignment value (not hold-value), since blocking
    assigns in always blocks typically start with `sig = 0;` as default. -/
partial def stmtsToMuxExprBlocking (sigName : String) (stmts : List SVStmt) : Expr :=
  let initDefault := stmts.findSome? fun s => match s with
    | .blockAssign lhs rhs =>
      match exprToName lhs with
      | some n => if n == sigName then some (lowerExpr rhs) else none
      | none => none
    | _ => none
  let base := initDefault.getD (.ref sigName)
  stmtsToMuxWithBase sigName stmts base
where
  stmtsToMuxWithBase (sigName : String) (stmts : List SVStmt) (base : Expr) : Expr :=
    stmts.foldl (fun current s => stmtToMuxBlocking sigName s current base) base
  stmtToMuxBlocking (sigName : String) (s : SVStmt) (current base : Expr) : Expr :=
    match s with
    | .blockAssign lhs rhs =>
      match exprToName lhs with
      | some n =>
        if n == sigName then
          -- Skip don't-care ('bx) assignments — they're cleanup, not logic
          match rhs with
          | .lit (.binary none 0) => current  -- 'bx → keep current value
          | .lit (.hex none 0) => current     -- 'hx → keep current value
          | _ => lowerExpr rhs
        else current
      | none => current
    | .ifElse cond thenB elseB =>
      let thenNames := collectBlockNames thenB
      let elseNames := collectBlockNames elseB
      if thenNames.any (· == sigName) || elseNames.any (· == sigName) then
        let thenVal := if thenNames.any (· == sigName) then stmtsToMuxWithBase sigName thenB base else base
        let elseVal := if elseNames.any (· == sigName) then stmtsToMuxWithBase sigName elseB base else base
        .op .mux [lowerExpr cond, thenVal, elseVal]
      else current
    | .caseStmt sel arms default_ =>
      let anyArm := arms.any fun (_, body) => (collectBlockNames body).any (· == sigName)
      let defHasReg := match default_ with | some d => (collectBlockNames d).any (· == sigName) | none => false
      if anyArm || defHasReg then
        -- Use current (accumulated from prior statements) as default, not base
        let defResult := match default_ with
          | some d => if defHasReg then stmtsToMuxWithBase sigName d base else current
          | none => current
        arms.reverse.foldl (fun acc (labels, body) =>
          if (collectBlockNames body).any (· == sigName) then
            let bodyExpr := stmtsToMuxWithBase sigName body base
            let selExpr := lowerExpr sel
            let isCase1b1 := match sel with
              | .lit (.binary (some 1) 1) => true
              | .lit (.decimal (some 1) 1) => true
              | _ => false
            let cond := labels.foldl (fun acc' label =>
              let c := if isCase1b1 then lowerExpr label
                       else Expr.op .eq [selExpr, lowerExpr label]
              if acc' == Expr.const 0 1 then c else Expr.op .or [acc', c]
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

/-- Collect array element writes: arr[idx] <= data, with optional condition -/
partial def collectArrayWrites (arrName : String) (stmts : List SVStmt)
    : List (SVExpr × SVExpr × Option SVExpr) :=
  stmts.flatMap fun s => match s with
    | .nonblockAssign (.index (.ident name) idx) rhs =>
      if name == arrName then [(idx, rhs, none)] else []
    | .ifElse cond thenB elseB =>
      let thenWrites := (collectArrayWrites arrName thenB).map
        fun (i, d, _) => (i, d, some cond)
      let elseWrites := collectArrayWrites arrName elseB
      thenWrites ++ elseWrites
    | .caseStmt _ arms default_ =>
      let armWrites := arms.flatMap fun (_, body) => collectArrayWrites arrName body
      let defWrites := match default_ with | some body => collectArrayWrites arrName body | none => []
      armWrites ++ defWrites
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
-- Topological sort of IR statements
-- ============================================================================

/-- Collect all Expr.ref names used in an expression -/
partial def collectRefs : Expr → List String
  | .ref name => [name]
  | .op _ args => args.flatMap collectRefs
  | .concat args => args.flatMap collectRefs
  | .slice e _ _ => collectRefs e
  | .index a i => collectRefs a ++ collectRefs i
  | _ => []

/-- Topologically sort assign statements so each wire is computed after its dependencies.
    Registers are placed after all assigns (they read current register values). -/
def topoSortBody (body : List Stmt) : List Stmt := Id.run do
  let mut assigns : List (String × Expr) := []
  let mut registers : List Stmt := []
  let mut memories : List Stmt := []
  let mut others : List Stmt := []
  for s in body do
    match s with
    | .assign name rhs => assigns := assigns ++ [(name, rhs)]
    | .register _ _ _ _ _ => registers := registers ++ [s]
    | .memory _ _ _ _ _ _ _ _ _ _ => memories := memories ++ [s]
    | _ => others := others ++ [s]
  let assignNames := assigns.map (·.1)
  let mut sorted : List Stmt := []
  let mut emitted : List String := []
  let mut remaining := assigns
  -- Kahn's algorithm
  let mut changed := true
  while changed do
    changed := false
    let mut nextRemaining : List (String × Expr) := []
    for (name, rhs) in remaining do
      let deps := collectRefs rhs
      let depsReady := deps.all fun dep =>
        !(assignNames.any (· == dep)) || emitted.any (· == dep)
      if depsReady then
        sorted := sorted ++ [.assign name rhs]
        emitted := emitted ++ [name]
        changed := true
      else
        nextRemaining := nextRemaining ++ [(name, rhs)]
    remaining := nextRemaining
  for (name, rhs) in remaining do
    sorted := sorted ++ [.assign name rhs]
  return memories ++ sorted ++ registers ++ others

-- ============================================================================
-- Generate block evaluation
-- ============================================================================

/-- Try to evaluate an SVExpr to a constant Nat using parameter values.
    Returns `none` if the expression is too complex to evaluate statically. -/
partial def evalConstExpr (paramVals : List (String × Nat)) : SVExpr → Option Nat
  | .lit (.decimal _ v) => some v
  | .lit (.hex _ v) => some v
  | .lit (.binary _ v) => some v
  | .ident name => paramVals.find? (·.1 == name) |>.map (·.2)
  | .binary .logOr a b => do
    let va ← evalConstExpr paramVals a
    let vb ← evalConstExpr paramVals b
    some (if va != 0 || vb != 0 then 1 else 0)
  | .binary .logAnd a b => do
    let va ← evalConstExpr paramVals a
    let vb ← evalConstExpr paramVals b
    some (if va != 0 && vb != 0 then 1 else 0)
  | .binary .bitOr a b => do
    let va ← evalConstExpr paramVals a
    let vb ← evalConstExpr paramVals b
    some (va ||| vb)
  | .unary .logNot a => do
    let va ← evalConstExpr paramVals a
    some (if va == 0 then 1 else 0)
  | _ => none

/-- Extract parameter default values as (name, value) pairs -/
def extractParamDefaults (svMod : SVModule) : List (String × Nat) :=
  let fromParams := svMod.params.filterMap fun p =>
    match p.value with
    | .lit (.decimal _ v) => some (p.name, v)
    | .lit (.hex _ v) => some (p.name, v)
    | .lit (.binary _ v) => some (p.name, v)
    | _ => none
  let fromItems := svMod.items.filterMap fun item =>
    match item with
    | .paramDecl p => match p.value with
      | .lit (.decimal _ v) => some (p.name, v)
      | .lit (.hex _ v) => some (p.name, v)
      | .lit (.binary _ v) => some (p.name, v)
      | _ => none
    | _ => none
  fromParams ++ fromItems

/-- Expand generate blocks by evaluating conditions against parameter defaults.
    Returns the items from the selected branch (recursively for nested generates). -/
partial def expandGenerateBlocks (paramVals : List (String × Nat))
    (items : List SVModuleItem) : List SVModuleItem :=
  items.flatMap fun item =>
    match item with
    | .generateBlock cond ifItems elseItems =>
      let condVal := evalConstExpr paramVals cond |>.getD 0
      let selectedItems := if condVal != 0 then ifItems else elseItems
      -- Recursively expand in case of nested generate blocks
      expandGenerateBlocks paramVals selectedItems
    | other => [other]

-- ============================================================================
-- Module lowering
-- ============================================================================

/-- Lower a single SVModule to Sparkle IR Module -/
def lowerModule (svMod : SVModule) : Except String Module := do
  -- Expand generate blocks using parameter defaults
  let paramVals := extractParamDefaults svMod
  let expandedItems := expandGenerateBlocks paramVals svMod.items
  let svMod := { svMod with items := expandedItems }

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
      | some _ => pure ()  -- Array regs handled by Stmt.memory (not wires)
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
      -- Detect reset pattern: find first if/else that looks like a reset check
      -- PicoRV32 has flat assigns before the reset check, so we scan for it
      let mut resetName := "rst"
      let mut initMap : List (String × Nat) := []
      let resetCheck := stmts.findSome? fun s => match s with
        | .ifElse cond thenB elseB => detectReset cond thenB elseB
        | _ => none
      match resetCheck with
      | some (resetSig, isActiveHigh, initBranch, _dataBranch) =>
        resetName := if isActiveHigh then resetSig else s!"_rst_{resetSig}_inv"
        if !isActiveHigh then
          wires := wires ++ [{ name := resetName, ty := .bit }]
          body := body ++ [.assign resetName (.op .not [.ref resetSig])]
        initMap := initBranch.filterMap fun s => match s with
          | .nonblockAssign lhs rhs =>
            match exprToName lhs with
            | some n => match evalConstExpr paramVals rhs with
              | some v => some (n, v)
              | none => none
            | none => none
          | _ => none
      | none => pure ()

      -- Extract blocking assigns as combinational intermediates (from full always body)
      let blockingNames := (collectBlockNamesTop stmts).eraseDups
      for sigName in blockingNames do
        let expr := stmtsToMuxExprBlocking sigName stmts
        body := body ++ [.assign sigName expr]
        if !(wireExists wires sigName) then
          wires := wires ++ [{ name := sigName, ty := .bitVector 32 }]  -- default 32-bit

      -- Collect all register names and build mux from full always body
      let regNames := (collectAllRegNames stmts).eraseDups
      for regName in regNames do
        let hwTy := env.getHWType regName
        let initVal := match initMap.find? (·.1 == regName) with
          | some (_, v) => v
          | none => 0
        let dataExpr := stmtsToMuxExpr regName stmts
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
      -- Do NOT add to wires list — Stmt.memory creates the class member.
      let dataWidth := widthToBits width
      let addrWidth := Nat.log2 arraySize + (if Nat.isPowerOfTwo arraySize then 0 else 1)
      -- Extract array writes from always blocks: arr[idx] <= expr
      -- Build write enable, address, and data mux expressions
      let mut writeAddr : Expr := .const 0 addrWidth
      let mut writeData : Expr := .const 0 dataWidth
      let mut writeEnable : Expr := .const 0 1
      for prevItem in svMod.items do
        match prevItem with
        | .alwaysBlock (.posedge _) stmts =>
          -- Find non-blocking assigns to this array: arr[idx] <= data
          let arrayWrites := collectArrayWrites name stmts
          for (idx, data, cond) in arrayWrites do
            writeAddr := lowerExpr idx
            writeData := lowerExpr data
            writeEnable := match cond with
              | some c => lowerExpr c
              | none => .const 1 1
        | _ => pure ()
      body := body ++ [.memory name addrWidth dataWidth "clk"
        writeAddr writeData writeEnable
        (.const 0 addrWidth) s!"{name}_rdata" true]
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
  let exprDepthSimple := fun (e : Expr) =>
    let rec go : Expr → Nat
      | .op _ args => 1 + (args.map go).foldl max 0
      | .slice e _ _ => 1 + go e
      | .index a i => 1 + max (go a) (go i)
      | _ => 0
    go e

  -- For registers assigned in multiple always blocks, keep the one
  -- with deeper mux expression (more logic). This handles the PicoRV32
  -- pattern where the decode block sets a flag and the execution block clears it.
  let mut regDepthMap : List (String × Nat) := []
  for stmt in body do
    match stmt with
    | .register name _ _ input _ =>
      let depth := exprDepthSimple input
      regDepthMap := regDepthMap ++ [(name, depth)]
    | _ => pure ()
  let bestDepth (name : String) : Nat :=
    (regDepthMap.filter (·.1 == name)).foldl (fun acc (_, d) => max acc d) 0

  -- Process in FORWARD order — first occurrence wins.
  -- For PicoRV32, the decode block (always[9]) comes before the execution
  -- block (always[17]). The decode block sets flags; the execution block clears them.
  -- We keep the decode block's version which has the meaningful logic.
  for stmt in body do
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
    body := topoSortBody dedupBody
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
          -- Collect all internal names in sub-module (including memory names)
          let memNames := subMod.body.filterMap fun s => match s with
            | .memory n _ _ _ _ _ _ _ _ _ => some n | _ => none
          let subNames := subMod.wires.map (·.name) ++
                          subMod.inputs.map (·.name) ++
                          subMod.outputs.map (·.name) ++
                          memNames

          -- Add prefixed wires from sub-module
          for w in subMod.wires do
            flatWires := flatWires ++ [{ name := s!"{instName}_{w.name}", ty := w.ty }]
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
                .inst subModName s!"{instName}_{subInstName}"
                  (subConns.map fun (pn, e) => (pn, prefixExprNames instName subNames e))
              | .memory name aw dw clk wa wd we ra rd combo =>
                .memory s!"{instName}_{name}" aw dw s!"{instName}_{clk}"
                  (prefixExprNames instName subNames wa)
                  (prefixExprNames instName subNames wd)
                  (prefixExprNames instName subNames we)
                  (prefixExprNames instName subNames ra)
                  s!"{instName}_{rd}" combo
            flatBody := flatBody ++ [prefixed]
      | other => flatBody := flatBody ++ [other]

    -- Prefix internal wire names with _gen_ to prevent CppSim local shadowing.
    -- Exclude: input/output port names, register names, memory names.
    let portNames := top.inputs.map (·.name) ++ top.outputs.map (·.name)
    let regNames := flatBody.filterMap fun s => match s with
      | .register n _ _ _ _ => some n | _ => none
    let memNames := flatBody.filterMap fun s => match s with
      | .memory n _ _ _ _ _ _ _ _ _ => some n | _ => none
    let internalWireNames := flatWires.map (·.name) |>.filter fun n =>
      !(portNames.any (· == n)) && !(regNames.any (· == n)) && !(memNames.any (· == n))
    let addGen (n : String) : String :=
      if n.startsWith "_gen_" then n
      else if internalWireNames.any (· == n) then s!"_gen_{n}"
      else n
    let genWires := flatWires.map fun w => { w with name := addGen w.name }
    let genExpr := genExprRefs internalWireNames
    let genBody := flatBody.map fun s => match s with
      | .assign n rhs => .assign (addGen n) (genExpr rhs)
      | .register n clk rst input init => .register n clk rst (genExpr input) init
      | .inst mn in_ conns => .inst mn in_ (conns.map fun (p, e) => (p, genExpr e))
      | .memory n aw dw clk wa wd we ra rd combo =>
        .memory n aw dw clk (genExpr wa) (genExpr wd) (genExpr we) (genExpr ra) rd combo

    let flatModule : Module := {
      name := top.name
      inputs := top.inputs
      outputs := top.outputs
      wires := genWires
      body := topoSortBody genBody
      isPrimitive := false
    }
    return { topModule := design.topModule, modules := [flatModule] }
  where
    genExprRefs (wireNames : List String) : Expr → Expr
      | .ref n => if wireNames.any (· == n) && !n.startsWith "_gen_"
                  then .ref s!"_gen_{n}" else .ref n
      | .op o args => .op o (args.map (genExprRefs wireNames))
      | .concat args => .concat (args.map (genExprRefs wireNames))
      | .slice e hi lo => .slice (genExprRefs wireNames e) hi lo
      | .index a i => .index (genExprRefs wireNames a) (genExprRefs wireNames i)
      | e => e

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
