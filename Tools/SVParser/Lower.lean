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
import Sparkle.IR.Optimize

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
  | .signed    => .not  -- unreachable: handled in lowerExpr

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
  -- Heuristic: names matching common array patterns
  -- Extended for LiteX (regs, sram, rom, storage) + PicoRV32 (cpuregs, memory)
  name == "cpuregs" || name == "memory" || name == "mem" ||
  name == "regs" || name == "sram" || name == "rom" ||
  name.endsWith "_mem" || name.endsWith "_ram" ||
  -- Note: _storage suffix (timer_en_storage) are scalar registers, not arrays.
  -- LiteX preprocessing renames these to _stor to avoid this heuristic.
  name.endsWith "_storage" || name == "storage" ||
  -- LiteX FIFO storage: storage, storage_1, storage_2, ...
  (name.startsWith "storage" && name.length <= 12)

/-- Evaluate a simple SVExpr to a Nat constant (handles literals, add, sub). -/
private partial def svExprToNat : SVExpr → Option Nat
  | .lit (.decimal _ v) => some v
  | .lit (.hex _ v) => some v
  | .lit (.binary _ v) => some v
  | .binary .add a b => do let va ← svExprToNat a; let vb ← svExprToNat b; some (va + vb)
  | .binary .sub a b => do let va ← svExprToNat a; let vb ← svExprToNat b; some (va - vb)
  | .binary .mul a b => do let va ← svExprToNat a; let vb ← svExprToNat b; some (va * vb)
  | .unary .neg a => do let va ← svExprToNat a; some (0 - va)
  | _ => none

private def concatWidth : SVExpr → Nat
  | .concat args => args.foldl (fun acc a => acc + concatWidth a) 0
  | .slice _ hi lo => hi - lo + 1
  | .partSelectPlus _ _ widthExpr => svExprToNat widthExpr |>.getD 1
  | .index _ _ => 1  -- single bit select
  | .lit (.decimal (some w) _) => w
  | .lit (.hex (some w) _) => w
  | .lit (.binary (some w) _) => w
  | .lit (.decimal none _) => 32
  | .lit (.hex none _) => 32
  | .lit (.binary none _) => 1
  | _ => 32  -- default: assume 32-bit

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
  | .unary .bitNot arg =>
    -- Bitwise NOT: ~x → XOR with all-ones (avoids confusion with logical NOT in IR)
    .op .xor [lowerExpr arg, .const (-1) 32]
  | .unary .signed arg =>
    -- $signed(x): sign-extend concat immediates from their natural width to 32.
    -- For single wire refs (already 32-bit), pass through unchanged.
    let innerWidth := concatWidth arg
    let lowered := lowerExpr arg
    if innerWidth >= 32 || innerWidth == 0 then lowered
    else
      -- Sign extend: shift left then arithmetic shift right
      let shiftAmt := 32 - innerWidth
      .op .asr [.op .shl [lowered, .const (Int.ofNat shiftAmt) 32], .const (Int.ofNat shiftAmt) 32]
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
  | .partSelectPlus expr base widthExpr =>
    -- [base +: width] = (expr >> base) & ((1 << width) - 1)
    let width := svExprToNat widthExpr |>.getD 1
    let mask := (1 <<< width) - 1
    .op .and [.op .shr [lowerExpr expr, lowerExpr base], .const (Int.ofNat mask) width]
  | .concat args => .concat (args.map lowerExpr)
  | .repeat_ count value =>
    -- {N{expr}}: replicate expr N times (bit replication)
    -- For 1-bit expr repeated N times: result = (0 - expr) & ((1 << N) - 1)
    -- For multi-bit expr: concatenate N copies via shift-and-OR.
    let n := match svExprToNat count with | some v => v | none => 1
    let valExpr := lowerExpr value
    if n <= 1 then valExpr
    else
      let elemWidth := match value with
        | .lit (.decimal (some w) _) => w
        | .lit (.hex (some w) _) => w
        | .lit (.binary (some w) _) => w
        | .slice _ hi lo => hi - lo + 1
        | .ident _ => 0  -- unknown width: use concat path
        | _ => 1  -- default: assume 1-bit
      if elemWidth == 1 then
        -- Special case: 1-bit replication → (0 - val) & mask
        let totalBits := n * 1
        let mask := (1 <<< totalBits) - 1
        .op .and [.op .sub [.const 0 totalBits, valExpr], .const (Int.ofNat mask) totalBits]
      else
        -- Multi-bit or unknown width: build concat of N copies
        .concat (List.replicate n valExpr)

-- ============================================================================
-- Extract target name from LHS expression
-- ============================================================================

def exprToName : SVExpr → Option String
  | .ident name => if isArrayName name then none else some name
  | .index (.ident name) _ => if isArrayName name then none else some name
  | .slice (.ident name) _ _ => some name
  -- Concat LHS handled separately by lowerConcatLhsAssign (needs bit scatter)
  | _ => none

/-- Extract target name from concat LHS (all elements must reference same register) -/
def concatLhsName : SVExpr → Option String
  | .concat elems =>
    let names := elems.filterMap fun e => match e with
      | .ident name => some name
      | .index (.ident name) _ => some name
      | .slice (.ident name) _ _ => some name
      | _ => none
    match names with
    | name :: rest => if rest.all (· == name) then some name else none
    | [] => none
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
-- Imperative → Dataflow conversion (If-Conversion / Guarded Assignments)
--
-- Walk the statement tree tracking the current guard condition. Each
-- assignment produces (guard, target, value). Then chain them as a flat
-- priority mux: last-write-wins, matching Verilog semantics.
-- ============================================================================

/-- A guarded assignment: under `guard`, signal `target` gets `value`. -/
structure GuardedAssign where
  guard  : Expr
  target : String
  value  : Expr

/-- Conjunction helper: true & x = x, else AND -/
private def mkAnd (a b : Expr) : Expr :=
  match a with
  | .const 1 _ => b
  | _ => match b with
    | .const 1 _ => a
    | _ => .op .and [a, b]

/-- Is this a don't-care literal ('bx / 'hx)? -/
private def isDontCare : SVExpr → Bool
  | .lit (.binary none 0) => true
  | .lit (.hex none 0) => true
  | _ => false

/-- For a concat-LHS assignment like {a[31:20], a[10:1], a[11], a[19:12], a[0]} <= rhs,
    build the value expression that scatters RHS bits to the correct positions.
    Returns (targetName, scatteredExpr) or none if not applicable. -/
private def lowerConcatLhsAssign (lhs : SVExpr) (rhs : SVExpr) : Option (String × Expr) :=
  match lhs, concatLhsName lhs with
  | .concat elems, some name =>
    let fields := elems.filterMap fun e => match e with
      | .slice (.ident _) hi lo => some (hi, lo)
      | .index (.ident _) (.lit (.decimal _ idx)) => some (idx, idx)
      | .ident _ => some (31, 0)
      | _ => none
    if fields.length != elems.length then none
    else
      let rhsExpr := lowerExpr rhs
      let totalWidth := fields.foldl (fun acc (hi, lo) => acc + (hi - lo + 1)) 0
      let (terms, _) := fields.foldl (fun (acc, rhsOff) (hi, lo) =>
        let w := hi - lo + 1
        let rhsBit := totalWidth - rhsOff - w
        let extracted := Expr.slice rhsExpr (rhsBit + w - 1) rhsBit
        let shifted := if lo == 0 then extracted
                       else Expr.op .shl [extracted, Expr.const (Int.ofNat lo) 32]
        (acc ++ [shifted], rhsOff + w)
      ) ([], 0)
      let result := terms.foldl (fun acc t =>
        if acc == Expr.const 0 32 then t else Expr.op .or [acc, t]
      ) (Expr.const 0 32)
      some (name, result)
  | _, _ => none

/-- Decompose a multi-variable concat-LHS blocking assignment into per-variable assignments.
    `{a[hi1:lo1], b[base +: width], ...} = rhs` →
    [(a, rhs_slice_for_a), (b, rhs_slice_for_b), ...]
    Each target gets the corresponding bits from the RHS expression. -/
private def decomposeMultiConcatLhs (lhs : SVExpr) (rhs : SVExpr) : List (String × Expr) :=
  match lhs with
  | .concat elems =>
    -- Compute field widths and target names for each element
    let fields : List (String × Nat × Nat) := elems.filterMap fun e => match e with
      | .slice (.ident name) hi lo => some (name, hi - lo + 1, lo)
      | .index (.ident name) idxExpr =>
        -- Evaluate index expression (may be constant expr like 0+4-1=3)
        match svExprToNat idxExpr with
        | some idx => some (name, 1, idx)
        | none => none
      | .partSelectPlus (.ident name) baseExpr widthExpr =>
        let base := match svExprToNat baseExpr with
          | some v => v | none => 0
        let width := svExprToNat widthExpr |>.getD 1
        some (name, width, base)
      | .ident name => some (name, 32, 0)
      | _ => none
    if fields.length != elems.length then []
    else
      let rhsExpr := lowerExpr rhs
      let totalWidth := fields.foldl (fun acc (_, w, _) => acc + w) 0
      -- Collect all (name, width, lo, rhsBit) with shifted RHS bits
      let (rawFields, _) := fields.foldl (fun (acc, rhsOff) (name, width, lo) =>
        let rhsBit := totalWidth - rhsOff - width
        (acc ++ [(name, width, lo, rhsBit)], rhsOff + width)
      ) ([], 0)
      -- Group by variable name: for each variable, produce a read-modify-write expression.
      -- Uses "__RMW_BASE__" as a placeholder for the old value, which is replaced by
      -- stmtsToMuxExprBlocking with the actual SSA base (previous iteration's output).
      let varNames := rawFields.map (·.1) |>.eraseDups
      varNames.flatMap fun varName =>
        let myFields := rawFields.filter (·.1 == varName)
        -- Compute combined mask for all fields
        let combinedMask := myFields.foldl (fun acc (_, width, lo, _) =>
          acc ||| (((1 <<< width) - 1) <<< lo)
        ) 0
        let invMask := combinedMask ^^^ 0xFFFFFFFFFFFFFFFF
        -- Build new bits: OR all shifted+masked fields
        let newBits := myFields.foldl (fun acc (_, width, lo, rhsBit) =>
          let extracted := Expr.slice rhsExpr (rhsBit + width - 1) rhsBit
          -- Force 64-bit promotion to avoid C++ UB on shifts >= 32
          let extracted64 := Expr.op .or [extracted, Expr.const 0 64]
          let shifted := if lo == 0 then extracted64
                         else Expr.op .shl [extracted64, Expr.const (Int.ofNat lo) 64]
          let maskVal := ((1 <<< width) - 1) <<< lo
          let masked := Expr.op .and [shifted, Expr.const (Int.ofNat maskVal) 64]
          if acc == Expr.const 0 64 then masked
          else Expr.op .or [acc, masked]
        ) (Expr.const 0 64)
        -- RMW: (varName & ~mask) | newBits
        -- Uses Expr.ref varName directly. For SSA variables, stmtsToMuxExprBlocking
        -- replaces self-references with the ssaBase (previous SSA iteration).
        -- This ensures topoSortBody's collectRefs sees the correct dependency.
        let cleared := Expr.op .and [Expr.ref varName, Expr.const (Int.ofNat invMask) 64]
        [(varName, Expr.op .or [cleared, newBits])]
  | _ => []

/-- Build a case arm condition from labels and selector.
    For case(1'b1), labels are direct conditions (priority encoding).
    For normal case, labels are compared against sel. -/
private def mkCaseCond (sel : SVExpr) (labels : List SVExpr) : Expr :=
  let isCase1b1 := match sel with
    | .lit (.binary (some 1) 1) => true
    | .lit (.decimal (some 1) 1) => true
    | _ => false
  labels.foldl (fun acc label =>
    let c := if isCase1b1 then lowerExpr label
             else Expr.op .eq [lowerExpr sel, lowerExpr label]
    if acc == Expr.const 0 1 then c else Expr.op .or [acc, c]
  ) (Expr.const 0 1)

/-- Process case arms: collect guarded assigns and track covered conditions.
    Verilog case semantics: first matching arm wins (no fall-through).
    Each arm's guard is AND-ed with !covered to exclude prior matches. -/
private def processCaseArms (sel : SVExpr) (arms : List (List SVExpr × List SVStmt))
    (guard : Expr) (collectFn : List SVStmt → Expr → List GuardedAssign)
    : List GuardedAssign × Expr :=
  arms.foldl (fun (result, covered) (labels, body) =>
    let armCond := mkCaseCond sel labels
    -- Guard this arm with !covered to enforce first-match-wins priority
    let activeGuard := if covered == .const 0 1 then mkAnd guard armCond
                       else mkAnd guard (mkAnd (.op .not [covered]) armCond)
    let armAssigns := collectFn body activeGuard
    let newCovered := if covered == .const 0 1 then armCond else .op .or [covered, armCond]
    (result ++ armAssigns, newCovered)
  ) ([], .const 0 1)

/-- Try to evaluate an IR expression as a compile-time constant.
    Returns some value if the expression is a constant (including
    constant comparisons like `eq(0, 0)` → 1). -/
private def tryEvalConst : Expr → Option Nat
  | .const v _ => some v.toNat
  | .op .eq [.const a _, .const b _] => some (if a == b then 1 else 0)
  | .op .not [e] => do let v ← tryEvalConst e; some (if v == 0 then 1 else 0)
  | _ => none

/-- Collect all guarded non-blocking assignments from statements.
    `guard` is the current path condition (true = Expr.const 1 1). -/
partial def collectGuardedNB (stmts : List SVStmt) (guard : Expr := .const 1 1)
    : List GuardedAssign :=
  stmts.flatMap fun s => match s with
    | .nonblockAssign lhs rhs =>
      if isDontCare rhs then []
      else match exprToName lhs with
        | some name => [{ guard, target := name, value := lowerExpr rhs }]
        | none =>
          -- Try concat-LHS (bit-scatter) assignment
          match lowerConcatLhsAssign lhs rhs with
          | some (name, value) => [{ guard, target := name, value }]
          | none => []
    | .ifElse cond thenB elseB =>
      let c := lowerExpr cond
      -- No constant folding for non-blocking assigns (posedge always blocks):
      -- tryEvalConst can change guard priority in the decoder's case statements,
      -- causing incorrect instruction decode when WITH_PCPI=1.
      collectGuardedNB thenB (mkAnd guard c) ++
      collectGuardedNB elseB (mkAnd guard (.op .not [c]))
    | .caseStmt sel arms default_ =>
      let (armAssigns, covered) := processCaseArms sel arms guard (fun s g => collectGuardedNB s g)
      let defAssigns := match default_ with
        | some d => collectGuardedNB d (mkAnd guard (.op .not [covered]))
        | none => []
      armAssigns ++ defAssigns
    | .forLoop _ _ _ body => collectGuardedNB body guard
    | _ => []

/-- Collect guarded assertions from statements.
    Each assertion becomes (guard, condition_expr). -/
partial def collectGuardedAsserts (stmts : List SVStmt) (guard : Expr := .const 1 1)
    : List (Expr × Expr) :=
  stmts.flatMap fun s => match s with
    | .assertStmt cond => [(guard, lowerExpr cond)]
    | .ifElse cond thenB elseB =>
      let c := lowerExpr cond
      collectGuardedAsserts thenB (mkAnd guard c) ++
      collectGuardedAsserts elseB (mkAnd guard (.op .not [c]))
    | .caseStmt sel arms default_ =>
      let (armAsserts, covered) := arms.foldl (fun (result, cov) (labels, body) =>
        let armCond := mkCaseCond sel labels
        let asserts := collectGuardedAsserts body (mkAnd guard armCond)
        let newCov := if cov == .const 0 1 then armCond else .op .or [cov, armCond]
        (result ++ asserts, newCov)
      ) ([], Expr.const 0 1)
      let defAsserts := match default_ with
        | some d => collectGuardedAsserts d (mkAnd guard (.op .not [covered]))
        | none => []
      armAsserts ++ defAsserts
    | _ => []

/-- Collect all guarded blocking assignments from statements. -/
partial def collectGuardedBlock (stmts : List SVStmt) (guard : Expr := .const 1 1)
    : List GuardedAssign :=
  stmts.flatMap fun s => match s with
    | .blockAssign lhs rhs =>
      if isDontCare rhs then []
      else match exprToName lhs with
        | some name => [{ guard, target := name, value := lowerExpr rhs }]
        | none =>
          -- Try single-variable concat-LHS
          match lowerConcatLhsAssign lhs rhs with
          | some (name, value) => [{ guard, target := name, value }]
          | none =>
            -- Multi-variable concat-LHS decomposition
            -- Group by variable name and OR-combine the shifted bit fields
            let assigns := decomposeMultiConcatLhs lhs rhs
            let names := assigns.map (·.1) |>.eraseDups
            names.flatMap fun name =>
              let fields := assigns.filter (·.1 == name) |>.map (·.2)
              match fields with
              | [] => []
              | [single] => [{ guard, target := name, value := single }]
              | first :: rest =>
                let combined := rest.foldl (fun acc f => Expr.op .or [acc, f]) first
                [{ guard, target := name, value := combined }]
    | .ifElse cond thenB elseB =>
      let c := lowerExpr cond
      -- No constant folding here — it corrupts decoder case priority in posedge blocks.
      -- Constant folding is only safe in emitBlockingStmtsSequential (always @*).
      collectGuardedBlock thenB (mkAnd guard c) ++
      collectGuardedBlock elseB (mkAnd guard (.op .not [c]))
    | .caseStmt sel arms default_ =>
      let (armAssigns, covered) := processCaseArms sel arms guard (fun s g => collectGuardedBlock s g)
      let defAssigns := match default_ with
        | some d => collectGuardedBlock d (mkAnd guard (.op .not [covered]))
        | none => []
      armAssigns ++ defAssigns
    | .forLoop _ _ _ body => collectGuardedBlock body guard
    | _ => []

/-- Collect all Expr.ref names used in an expression -/
partial def collectRefs : Expr → List String
  | .ref name => [name]
  | .op _ args => args.flatMap collectRefs
  | .concat args => args.flatMap collectRefs
  | .slice e _ _ => collectRefs e
  | .index a i => collectRefs a ++ collectRefs i
  | _ => []

/-- Chain guarded assignments into a flat priority mux (last-write-wins).
    `base` is the default when no guard is active (hold value for registers,
    first flat assign for blocking signals). -/
def guardedToMux (assigns : List GuardedAssign) (base : Expr) : Expr :=
  assigns.foldl (fun acc ga => .op .mux [ga.guard, ga.value, acc]) base

/-- Build mux expression for a non-blocking register from full always body. -/
def stmtsToMuxExpr (regName : String) (stmts : List SVStmt) : Expr :=
  let all := collectGuardedNB stmts
  let filtered := all.filter (·.target == regName)
  guardedToMux filtered (.ref regName)

/-- Build mux expression for a blocking combinational signal.
    Base is the first flat assignment (default value). -/
def stmtsToMuxExprBlocking (sigName : String) (stmts : List SVStmt) : Expr :=
  let initDefault := stmts.findSome? fun s => match s with
    | .blockAssign lhs rhs =>
      match exprToName lhs with
      | some n => if n == sigName then some (lowerExpr rhs) else none
      | none => none
    | _ => none
  -- For SSA variables (e.g., next_rd_ssa0_1), use the previous SSA version as base
  -- This avoids self-reference when no initDefault exists
  let ssaBase : Option Expr := do
    -- Extract the LAST _ssaD_N segment to handle nested SSA.
    -- "foo_ssa0_1_ssa1_2" → prefix="foo_ssa0_1", depth="1", idx=2 → base="foo_ssa0_1_ssa1_1"
    -- "foo_ssa0_0" → prefix="foo", depth="0", idx=0 → base="foo"
    let parts := sigName.splitOn "_ssa"
    if parts.length < 2 then none
    else
      -- Reconstruct: prefix = all parts except last, joined by "_ssa"
      let lastSuffix := parts[parts.length - 1]!  -- e.g., "1_2"
      let ssaPrefix := String.intercalate "_ssa" (parts.take (parts.length - 1))
      let suffParts := lastSuffix.splitOn "_"
      if suffParts.length < 2 then none
      else
        let depth := suffParts[0]!
        let idxStr := suffParts[1]!
        match idxStr.toNat? with
        | some 0 => some (.ref ssaPrefix)  -- ssa_0 reads from the prefix (original or outer SSA)
        | some n => some (.ref s!"{ssaPrefix}_ssa{depth}_{n - 1}")
        | none => none
  let base := initDefault.getD (ssaBase.getD (.ref sigName))
  let all := collectGuardedBlock stmts
  let filtered := all.filter (·.target == sigName)
  -- For SSA variables, replace self-references (Expr.ref sigName) in guarded assign
  -- values with the actual base (ssaBase = previous SSA iteration's output).
  -- This is needed for concat-LHS read-modify-write: (self & ~mask) | newBits
  -- where "self" should actually read from the previous SSA step.
  let resolved := if ssaBase.isSome then
      let rec substSelf (e : Expr) : Expr := match e with
        | .ref n => if n == sigName then base else .ref n
        | .op o args => .op o (args.map substSelf)
        | .concat args => .concat (args.map substSelf)
        | .slice inner hi lo => .slice (substSelf inner) hi lo
        | .index arr idx => .index (substSelf arr) (substSelf idx)
        | other => other
      filtered.map fun ga => { ga with value := substSelf ga.value }
    else filtered
  guardedToMux resolved base

/-- Collect all register names assigned (non-blocking) anywhere in statements -/
partial def collectAllRegNames (stmts : List SVStmt) : List String :=
  stmts.flatMap fun s => match s with
    | .nonblockAssign lhs _ =>
      match exprToName lhs with
      | some n => [n]
      | none => match concatLhsName lhs with | some n => [n] | none => []
    | .ifElse _ thenB elseB =>
      collectAllRegNames thenB ++ collectAllRegNames elseB
    | .caseStmt _ arms default_ =>
      let armNames := arms.flatMap fun (_, body) => collectAllRegNames body
      let defNames := match default_ with | some d => collectAllRegNames d | none => []
      armNames ++ defNames
    | .forLoop _ _ _ body => collectAllRegNames body
    | _ => []

/-- A byte-lane write: under `cond`, write `data[hi:lo]` to `arr[addr][hi:lo]` -/
structure ByteLaneWrite where
  addr : SVExpr
  data : SVExpr
  cond : SVExpr
  hi   : Nat
  lo   : Nat

/-- Collect array element writes: arr[idx] <= data, with optional condition.
    Also detects byte-strobe patterns: if (wstrb[n]) arr[idx][hi:lo] <= data[hi:lo] -/
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

/-- Collect byte-lane writes: if (cond) arr[addr][hi:lo] <= data[hi:lo] -/
partial def collectByteLaneWrites (arrName : String) (stmts : List SVStmt)
    : List ByteLaneWrite :=
  stmts.flatMap fun s => match s with
    | .nonblockAssign (.slice (.index (.ident name) addr) hi lo) rhs =>
      if name == arrName then [{ addr, data := rhs, cond := .lit (.decimal none 1), hi, lo }] else []
    | .ifElse cond thenB elseB =>
      -- Recurse into both branches, propagating condition for then-branch
      let thenWrites := (collectByteLaneWrites arrName thenB).map
        fun w => { w with cond := if w.cond == .lit (.decimal none 1) then cond else w.cond }
      let elseWrites := collectByteLaneWrites arrName elseB
      thenWrites ++ elseWrites
    | .caseStmt _ arms default_ =>
      let armWrites := arms.flatMap fun (_, body) => collectByteLaneWrites arrName body
      let defWrites := match default_ with | some body => collectByteLaneWrites arrName body | none => []
      armWrites ++ defWrites
    | _ => []

/-- Build a read-modify-write expression for byte-lane writes.
    Combines multiple byte-strobe writes into: for each lane,
    if (cond) use new_byte else use old_byte. -/
def buildByteStrobeWrite (arrName : String) (addrExpr : Expr) (lanes : List ByteLaneWrite) : Expr :=
  -- Start with the old value: arr[addr]
  let oldVal := Expr.index (.ref arrName) addrExpr
  -- For each lane, apply a mux: cond ? (old & ~mask) | (new & mask) : old
  lanes.foldl (fun acc lane =>
    let condExpr := lowerExpr lane.cond
    let dataExpr := lowerExpr lane.data
    let width := lane.hi - lane.lo + 1
    let mask : Nat := ((1 <<< width) - 1) <<< lane.lo  -- e.g., 0xFF for [7:0], 0xFF00 for [15:8]
    let notMask : Nat := 0xFFFFFFFF ^^^ mask
    let maskConst := Expr.const (Int.ofNat mask) 32
    let notMaskConst := Expr.const (Int.ofNat notMask) 32
    -- Shift data to the correct bit position before masking
    -- dataExpr is already sliced (e.g., mem_wdata[15:8] → 8-bit value at bit 0)
    -- Need to shift it to lane.lo position before ANDing with mask
    let shiftedData := if lane.lo == 0 then dataExpr
      else Expr.op .shl [dataExpr, Expr.const (Int.ofNat lane.lo) 32]
    -- new_val = (old & ~mask) | (shifted_data & mask)
    let newVal := Expr.op .or [
      Expr.op .and [acc, notMaskConst],
      Expr.op .and [shiftedData, maskConst]
    ]
    Expr.op .mux [condExpr, newVal, acc]
  ) oldVal

/-- Collect all blocking-assigned signal names recursively -/
partial def collectBlockNamesTop (stmts : List SVStmt) : List String :=
  let extractName (lhs : SVExpr) : List String :=
    match exprToName lhs with
    | some n => [n]
    | none =>
      match lhs with
      | .concat elems => elems.filterMap fun e => match e with
        | .ident n => some n
        | .index (.ident n) _ => some n
        | .slice (.ident n) _ _ => some n
        | .partSelectPlus (.ident n) _ _ => some n
        | _ => none
      | _ => []
  stmts.flatMap fun s => match s with
    | .blockAssign lhs _ => extractName lhs
    -- Non-blocking assigns in always @(*) are combinational (LiteX/Migen pattern)
    | .nonblockAssign lhs _ => extractName lhs
    | .ifElse _ t e => collectBlockNamesTop t ++ collectBlockNamesTop e
    | .caseStmt _ arms d =>
      (arms.flatMap fun (_, b) => collectBlockNamesTop b) ++
      (match d with | some b => collectBlockNamesTop b | none => [])
    | .forLoop _ _ _ body => collectBlockNamesTop body
    | _ => []

-- ============================================================================
-- Sequential SSA emitter for always @* blocks (MemorySSA approach)
-- ============================================================================

/-- Environment mapping variable names to their latest SSA wire name.
    Used by emitSequentialSSA to track the "current value" of each variable
    as statements are processed top-to-bottom. -/
abbrev SeqSSAEnv := List (String × String)

private def seqEnvLookup (env : SeqSSAEnv) (name : String) : String :=
  match env.find? (·.1 == name) with
  | some (_, latest) => latest
  | none => name

private def seqEnvUpdate (env : SeqSSAEnv) (name latest : String) : SeqSSAEnv :=
  if env.any (·.1 == name) then
    env.map fun (k, v) => if k == name then (k, latest) else (k, v)
  else
    env ++ [(name, latest)]

/-- Replace all Expr.ref names using the current SSA environment.
    Looks up each ref in env and substitutes with the latest SSA name. -/
private partial def substExprEnv (env : SeqSSAEnv) : Expr → Expr
  | .ref name => .ref (seqEnvLookup env name)
  | .op o args => .op o (args.map (substExprEnv env))
  | .concat args => .concat (args.map (substExprEnv env))
  | .slice e hi lo => .slice (substExprEnv env e) hi lo
  | .index arr idx => .index (substExprEnv env arr) (substExprEnv env idx)
  | other => other

/-- Emit IR assigns for an always @* block by processing statements sequentially.
    Each variable write creates a new SSA wire; reads use the latest SSA name.
    This correctly handles "read-then-overwrite" patterns like:
      next_rdx = rdx;            // read initial
      for (...) use(next_rdx);   // reads initial value
      next_rdx = next_rdt << 1;  // overwrite with loop result
    which cannot be expressed as a single MUX without cyclic dependency.
    Returns (assigns, new_wires, final_env, step_counter). -/
partial def emitSequentialSSA (stmts : List SVStmt)
    (env : SeqSSAEnv) (stepCounter : Nat)
    : List Stmt × List Port × SeqSSAEnv × Nat :=
  stmts.foldl (fun (result, wires, curEnv, step) s =>
    match s with
    | .blockAssign lhs rhs | .nonblockAssign lhs rhs =>
      -- Note: nonblockAssign (<=) in always @(*) is treated as combinational
      -- (LiteX/Migen generates this pattern for bus muxes)
      if isDontCare rhs then (result, wires, curEnv, step)
      else
        -- Check for bit-index assign first: x[idx] = expr → read-modify-write
        -- (must be before exprToName which would treat index as simple name)
        match lhs with
        | .index (.ident name) idxExpr =>
          if !isArrayName name then
            let idx := match idxExpr with
              | .lit (.decimal _ v) => v | _ => 0
            let curRef := Expr.ref (seqEnvLookup curEnv name)
            let rhsExpr := substExprEnv curEnv (lowerExpr rhs)
            let mask := Expr.const (Int.ofNat (1 <<< idx)) 32
            let clearMask := Expr.op .xor [mask, .const (-1) 32]
            let cleared := Expr.op .and [curRef, clearMask]
            let shifted := Expr.op .shl [.op .and [rhsExpr, .const 1 1], .const (Int.ofNat idx) 32]
            let newVal := Expr.op .or [cleared, shifted]
            let wireName := s!"{name}_seq{step}"
            ( result ++ [.assign wireName newVal]
            , wires ++ [{ name := wireName, ty := .bitVector 32 }]
            , seqEnvUpdate curEnv name wireName
            , step + 1 )
          else
            -- Array index: fall through to normal handling
            (result, wires, curEnv, step)
        | _ =>
        match exprToName lhs with
        | some name =>
          let rhsExpr := substExprEnv curEnv (lowerExpr rhs)
          let wireName := s!"{name}_seq{step}"
          ( result ++ [.assign wireName rhsExpr]
          , wires ++ [{ name := wireName, ty := .bitVector 64 }]
          , seqEnvUpdate curEnv name wireName
          , step + 1 )
        | none =>
          -- Concat-LHS: decompose and create SSA wires for each target
          let assigns := decomposeMultiConcatLhs lhs rhs
          assigns.foldl (fun (r, w, e, st) (name, value) =>
            let substValue := substExprEnv e value
            let wireName := s!"{name}_seq{st}"
            ( r ++ [.assign wireName substValue]
            , w ++ [{ name := wireName, ty := .bitVector 64 }]
            , seqEnvUpdate e name wireName
            , st + 1 )
          ) (result, wires, curEnv, step)
    | .ifElse cond thenB elseB =>
      let condExpr := substExprEnv curEnv (lowerExpr cond)
      let (thenStmts, thenWires, thenEnv, thenStep) := emitSequentialSSA thenB curEnv step
      let (elseStmts, elseWires, elseEnv, elseStep) := emitSequentialSSA elseB curEnv thenStep
      -- Merge: MUX for each variable changed in either branch
      let allChanged := ((thenEnv ++ elseEnv).filter fun (k, v) =>
        seqEnvLookup curEnv k != v).map (·.1) |>.eraseDups
      let (muxStmts, muxWires, mergedEnv, muxStep) := allChanged.foldl
        (fun (r, w, e, st) name =>
          let preIfVal := seqEnvLookup curEnv name
          let thenLookup := seqEnvLookup thenEnv name
          let elseLookup := seqEnvLookup elseEnv name
          let thenChanged := thenLookup != preIfVal
          let elseChanged := elseLookup != preIfVal
          if thenChanged && elseChanged then
            -- Both branches modified: MUX between branch results
            let muxName := s!"{name}_seq{st}"
            ( r ++ [.assign muxName (.op .mux [condExpr, .ref thenLookup, .ref elseLookup])]
            , w ++ [{ name := muxName, ty := .bitVector 64 }]
            , seqEnvUpdate e name muxName
            , st + 1 )
          else if thenChanged then
            -- Only then-branch modified: MUX with pre-if value
            -- If preIfVal is the raw variable name (no _seq wire), it means the variable
            -- was never assigned before this if-else. Use the then-branch result directly
            -- guarded by condition, to avoid self-referencing the final output.
            let hasSeqWire := (preIfVal.splitOn "_seq").length > 1
            if hasSeqWire then
              let muxName := s!"{name}_seq{st}"
              ( r ++ [.assign muxName (.op .mux [condExpr, .ref thenLookup, .ref preIfVal])]
              , w ++ [{ name := muxName, ty := .bitVector 64 }]
              , seqEnvUpdate e name muxName
              , st + 1 )
            else
              -- No prior seq wire: just use the then-branch value (condition always true
              -- for constant-folded parameters, or the variable is don't-care otherwise)
              (r, w, seqEnvUpdate e name thenLookup, st)
          else
            -- Only else-branch modified
            let hasSeqWire := (preIfVal.splitOn "_seq").length > 1
            if hasSeqWire then
              let muxName := s!"{name}_seq{st}"
              ( r ++ [.assign muxName (.op .mux [condExpr, .ref preIfVal, .ref elseLookup])]
              , w ++ [{ name := muxName, ty := .bitVector 64 }]
              , seqEnvUpdate e name muxName
              , st + 1 )
            else
              (r, w, seqEnvUpdate e name elseLookup, st)
        ) ([], [], curEnv, elseStep)
      ( result ++ thenStmts ++ elseStmts ++ muxStmts
      , wires ++ thenWires ++ elseWires ++ muxWires
      , mergedEnv, muxStep )
    | .caseStmt sel arms default_ =>
      let selExpr := substExprEnv curEnv (lowerExpr sel)
      -- Process default first for base values
      let (defStmts, defWires, defEnv, defStep) := match default_ with
        | some d => emitSequentialSSA d curEnv step
        | none => ([], [], curEnv, step)
      -- Short-circuit: if no arms, default is the only path → use defEnv directly
      if arms.isEmpty then
        (result ++ defStmts, wires ++ defWires, defEnv, defStep)
      else
      -- Process arms
      let (armStmts, armWires, armEnvs, armStep) := arms.foldl
        (fun (r, w, envs, st) (labels, body) =>
          let (aStmts, aWires, aEnv, aStep) := emitSequentialSSA body curEnv st
          (r ++ aStmts, w ++ aWires, envs ++ [(labels, aEnv)], aStep)
        ) (defStmts, defWires, [], defStep)
      -- Merge with priority MUX
      -- Include default branch changes only when all arms are empty/unchanged
      let armChangedNames := armEnvs.flatMap fun (_, aEnv) =>
        aEnv.filter (fun (k, v) => seqEnvLookup curEnv k != v) |>.map (·.1)
      let allArmsEmpty := armChangedNames.isEmpty
      let defChangedNames := if allArmsEmpty then
        defEnv.filter (fun (k, v) => seqEnvLookup curEnv k != v) |>.map (·.1)
      else []
      let allChangedNames := (defChangedNames ++ armChangedNames).eraseDups
      let (muxStmts, muxWires, mergedEnv, muxStep) := allChangedNames.foldl
        (fun (r, w, e, st) name =>
          let preVal := seqEnvLookup curEnv name
          let defLookup := seqEnvLookup defEnv name
          let hasSeqWire := (preVal.splitOn "_seq").length > 1
          -- If variable had no _seq wire before (e.g., initialized with 'bx / don't-care),
          -- and only some arms assign it, use the arm values directly without a default
          -- that would self-reference the final output.
          if !hasSeqWire && defLookup == preVal then
            -- No prior seq wire and default didn't change it: build MUX without default ref
            -- If only one arm changed it, just use that arm's value directly
            let armsThatChanged := armEnvs.filter fun (_, aEnv) =>
              seqEnvLookup aEnv name != preVal
            match armsThatChanged with
            | [(_, aEnv)] =>
              -- Single arm: just use its value
              let armVal := seqEnvLookup aEnv name
              (r, w, seqEnvUpdate e name armVal, st)
            | _ =>
              -- Multiple arms: build MUX chain, use const 0 as base (don't-care variable)
              let muxExpr := armEnvs.foldr (fun (labels, aEnv) acc =>
                let armLookup := seqEnvLookup aEnv name
                if armLookup == preVal then acc  -- arm didn't change: skip
                else
                  let cond := mkCaseCond sel labels
                  .op .mux [cond, .ref armLookup, acc]
              ) (.const 0 64)  -- don't-care base
              let muxName := s!"{name}_seq{st}"
              ( r ++ [.assign muxName muxExpr]
              , w ++ [{ name := muxName, ty := .bitVector 64 }]
              , seqEnvUpdate e name muxName
              , st + 1 )
          else
            -- Normal case: variable has a prior value
            let defVal := Expr.ref defLookup
            let muxExpr := armEnvs.foldr (fun (labels, aEnv) acc =>
              let armVal := Expr.ref (seqEnvLookup aEnv name)
              let cond := mkCaseCond sel labels
              .op .mux [cond, armVal, acc]
            ) defVal
            let muxName := s!"{name}_seq{st}"
            ( r ++ [.assign muxName muxExpr]
            , w ++ [{ name := muxName, ty := .bitVector 64 }]
            , seqEnvUpdate e name muxName
            , st + 1 )
        ) ([], [], curEnv, armStep)
      (result ++ armStmts ++ muxStmts, wires ++ armWires ++ muxWires, mergedEnv, muxStep)
    | .forLoop _ _ _ body =>
      let (innerStmts, innerWires, innerEnv, innerStep) := emitSequentialSSA body curEnv step
      (result ++ innerStmts, wires ++ innerWires, innerEnv, innerStep)
    | _ => (result, wires, curEnv, step)
  ) ([], [], env, stepCounter)

-- ============================================================================
-- Topological sort of IR statements
-- ============================================================================

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
  -- SSA prologues (name_ssa0_0 = original) should not depend on the
  -- epilogue assignment of 'original' — they read the initial value.
  -- Detect SSA prologues: "foo_ssaD_0" where the LAST segment after _ssa is "D_0"
  -- (not "D_10", "D_20", etc.)
  let isSsaPrologueName (name : String) : Bool :=
    let parts := name.splitOn "_ssa"
    if parts.length < 2 then false
    else
      let lastSeg := parts[parts.length - 1]!  -- e.g., "1_0" or "1_10"
      let segParts := lastSeg.splitOn "_"
      segParts.length >= 2 && segParts[segParts.length - 1]! == "0"
  let ssaPrologueBase (name : String) : Option String :=
    let parts := name.splitOn "_ssa"
    if parts.length < 2 then none
    else
      let lastSeg := parts[parts.length - 1]!
      let segParts := lastSeg.splitOn "_"
      if segParts.length >= 2 && segParts[segParts.length - 1]! == "0" then
        some (String.intercalate "_ssa" (parts.take (parts.length - 1)))
      else none
  let ssaPrologueOriginals := assigns.filterMap fun (name, _rhs) =>
    if isSsaPrologueName name then ssaPrologueBase name else none
  let mut changed := true
  while changed do
    changed := false
    let mut nextRemaining : List (String × Expr) := []
    for (name, rhs) in remaining do
      let deps := collectRefs rhs
      let isSsaPrologue := isSsaPrologueName name
      let prologueBase := if isSsaPrologue then ssaPrologueBase name else none
      let depsReady := deps.all fun dep =>
        dep == name ||
        !(assignNames.any (· == dep)) || emitted.any (· == dep) ||
        (isSsaPrologue && prologueBase.any (· == dep))
      if depsReady then
        sorted := sorted ++ [.assign name rhs]
        emitted := emitted ++ [name]
        changed := true
      else
        nextRemaining := nextRemaining ++ [(name, rhs)]
    remaining := nextRemaining
  if !remaining.isEmpty then
    dbg_trace s!"[TOPO WARNING] {remaining.length} assigns have cyclic deps (of {assigns.length} total). Names: {remaining.map (·.1) |>.take 20}"
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

/-- Substitute parameter references with constant values in SV expressions -/
partial def substParamExpr (params : List (String × SVExpr)) : SVExpr → SVExpr
  | .ident name => match params.find? fun (n, _) => n == name with
    | some (_, v) => v | none => .ident name
  | .unary op e => .unary op (substParamExpr params e)
  | .binary op a b => .binary op (substParamExpr params a) (substParamExpr params b)
  | .ternary c t e => .ternary (substParamExpr params c) (substParamExpr params t) (substParamExpr params e)
  | .index a i => .index (substParamExpr params a) (substParamExpr params i)
  | .slice e hi lo => .slice (substParamExpr params e) hi lo
  | .partSelectPlus e base w => .partSelectPlus (substParamExpr params e) (substParamExpr params base) (substParamExpr params w)
  | .concat es => .concat (es.map (substParamExpr params))
  | e => e

partial def substParamStmt (params : List (String × SVExpr)) : SVStmt → SVStmt
  | .blockAssign lhs rhs => .blockAssign (substParamExpr params lhs) (substParamExpr params rhs)
  | .nonblockAssign lhs rhs => .nonblockAssign (substParamExpr params lhs) (substParamExpr params rhs)
  | .ifElse cond thenB elseB =>
    .ifElse (substParamExpr params cond)
      (thenB.map (substParamStmt params)) (elseB.map (substParamStmt params))
  | .caseStmt sel arms dflt =>
    .caseStmt (substParamExpr params sel)
      (arms.map fun (labels, body) => (labels.map (substParamExpr params), body.map (substParamStmt params)))
      (dflt.map fun d => d.map (substParamStmt params))
  | .forLoop init cond step body =>
    .forLoop (substParamStmt params init) (substParamExpr params cond) (substParamStmt params step)
      (body.map (substParamStmt params))
  | .assertStmt cond => .assertStmt (substParamExpr params cond)

/-- Collect all variable names read in expressions. -/
private partial def collectReadNamesExpr : SVExpr → List String
  | .ident n => [n]
  | .unary _ e => collectReadNamesExpr e
  | .binary _ a b => collectReadNamesExpr a ++ collectReadNamesExpr b
  | .ternary c t e => collectReadNamesExpr c ++ collectReadNamesExpr t ++ collectReadNamesExpr e
  | .index a i => collectReadNamesExpr a ++ collectReadNamesExpr i
  | .slice e _ _ => collectReadNamesExpr e
  | .partSelectPlus e base _ => collectReadNamesExpr e ++ collectReadNamesExpr base
  | .concat es => es.flatMap collectReadNamesExpr
  | _ => []

private partial def collectReadNamesStmt : List SVStmt → List String
  | stmts => stmts.flatMap fun s => match s with
    | .blockAssign _ rhs => collectReadNamesExpr rhs
    | .ifElse c t e => collectReadNamesExpr c ++ collectReadNamesStmt t ++ collectReadNamesStmt e
    | .forLoop _ _ _ body => collectReadNamesStmt body
    | _ => []

/-- Collect all variable names written in blocking assignments (including concat-LHS). -/
private partial def collectWriteNames : List SVStmt → List String
  | stmts => stmts.flatMap fun s => match s with
    | .blockAssign lhs _ => match lhs with
      | .ident name => [name]
      | .index (.ident name) _ => [name]
      | .slice (.ident name) _ _ => [name]
      | .partSelectPlus (.ident name) _ _ => [name]
      | .concat elems => elems.filterMap fun e => match e with
        | .ident n => some n | .index (.ident n) _ => some n
        | .slice (.ident n) _ _ => some n | .partSelectPlus (.ident n) _ _ => some n
        | _ => none
      | _ => []
    | .ifElse _ t e => collectWriteNames t ++ collectWriteNames e
    | .forLoop _ _ _ body => collectWriteNames body
    | _ => []

/-- Rename all occurrences of `oldName` to `newName` in an SVExpr. -/
private partial def renameExpr (oldName newName : String) : SVExpr → SVExpr
  | .ident n => if n == oldName then .ident newName else .ident n
  | .unary op e => .unary op (renameExpr oldName newName e)
  | .binary op a b => .binary op (renameExpr oldName newName a) (renameExpr oldName newName b)
  | .ternary c t e => .ternary (renameExpr oldName newName c) (renameExpr oldName newName t) (renameExpr oldName newName e)
  | .index a i => .index (renameExpr oldName newName a) (renameExpr oldName newName i)
  | .slice e hi lo => .slice (renameExpr oldName newName e) hi lo
  | .partSelectPlus e base w => .partSelectPlus (renameExpr oldName newName e) (renameExpr oldName newName base) (renameExpr oldName newName w)
  | .concat es => .concat (es.map (renameExpr oldName newName))
  | e => e

/-- Rename all occurrences of `oldName` to `newName` in an SVStmt. -/
private partial def renameStmt (oldName newName : String) : SVStmt → SVStmt
  | .blockAssign lhs rhs => .blockAssign (renameExpr oldName newName lhs) (renameExpr oldName newName rhs)
  | .nonblockAssign lhs rhs => .nonblockAssign (renameExpr oldName newName lhs) (renameExpr oldName newName rhs)
  | .ifElse c t e => .ifElse (renameExpr oldName newName c) (t.map (renameStmt oldName newName)) (e.map (renameStmt oldName newName))
  | .caseStmt sel arms d =>
    .caseStmt (renameExpr oldName newName sel)
      (arms.map fun (ls, b) => (ls.map (renameExpr oldName newName), b.map (renameStmt oldName newName)))
      (d.map fun ds => ds.map (renameStmt oldName newName))
  | .forLoop i c s b => .forLoop (renameStmt oldName newName i) (renameExpr oldName newName c) (renameStmt oldName newName s) (b.map (renameStmt oldName newName))
  | .assertStmt c => .assertStmt (renameExpr oldName newName c)

/-- Rename in LHS of blockAssign only, recursing into ifElse/forLoop/case. -/
private partial def renameLhsOnly (oldName newName : String) : SVStmt → SVStmt
  | .blockAssign lhs rhs => .blockAssign (renameExpr oldName newName lhs) rhs
  | .ifElse c t e => .ifElse c (t.map (renameLhsOnly oldName newName)) (e.map (renameLhsOnly oldName newName))
  | .forLoop i c s body => .forLoop i c s (body.map (renameLhsOnly oldName newName))
  | .caseStmt sel arms d =>
    .caseStmt sel (arms.map fun (ls, b) => (ls, b.map (renameLhsOnly oldName newName)))
      (d.map fun ds => ds.map (renameLhsOnly oldName newName))
  | other => other

/-- Unroll for loops with constant bounds in SV statements.
    Uses SSA-style renaming: variables written in the loop body get
    iteration-specific names (e.g., next_rd → next_rd_ssa0_0, next_rd_ssa0_1, ...)
    to correctly handle sequential blocking assignment dependencies.
    `depth` distinguishes nested loops (ssa0_, ssa1_, ...). -/
partial def unrollForLoops (paramVals : List (String × Nat)) (depth : Nat := 0) : List SVStmt → List SVStmt :=
  fun stmts => stmts.flatMap fun s => match s with
  | .forLoop (.blockAssign (.ident var) initExpr) condExpr (.blockAssign (.ident stepVar) stepExpr) body =>
    if var != stepVar then [s]
    else
      let initVal := evalConstExpr paramVals initExpr |>.getD 0
      let bound := match condExpr with
        | .binary .lt (.ident v) limitExpr =>
          if v == var then evalConstExpr paramVals limitExpr else none
        | _ => none
      let stepVal := match stepExpr with
        | .binary .add (.ident v) incExpr =>
          if v == var then evalConstExpr paramVals incExpr else none
        | _ => none
      match bound, stepVal with
      | some b, some inc =>
        if inc == 0 || b <= initVal then [s]
        else Id.run do
          let ssaTag := s!"_ssa{depth}_"
          -- SSA-rename ALL variables written in the loop.
          -- Even non-self-referential variables need SSA when updated via non-overlapping
          -- part-selects across iterations (e.g., next_rdt[j+3] = ...). Without SSA,
          -- MUX last-write-wins would discard previous iterations' bit fields.
          let writeNames := collectWriteNames body |>.eraseDups
          let readNames := collectReadNamesStmt body |>.eraseDups
          -- For nested SSA, unify read/write names that share the same base
          -- (e.g., write=foo_ssa0_1, read=foo_ssa0_0 → rename reads to write name)
          let stripSsa (n : String) : String :=
            let parts := n.splitOn "_ssa"
            if parts.length >= 2 then parts[0]! else n
          let mut unifiedBody := body
          for wn in writeNames do
            if stripSsa wn != wn then
              for rn in readNames do
                if rn != wn && stripSsa rn == stripSsa wn then
                  unifiedBody := unifiedBody.map (renameStmt rn wn)
          let selfRefNames := collectWriteNames unifiedBody |>.eraseDups
          let numIters := (b - initVal + inc - 1) / inc

          -- SSA in unrollForLoops is disabled: emitSequentialSSA handles ordering.
          if true then
            -- Simple unroll without SSA (sequential emitter handles variable tracking)
            let mut result : List SVStmt := []
            let mut j := initVal
            while j < b do
              let substituted := unifiedBody.map (substParamStmt [(var, .lit (.decimal (some 32) j))])
              let unrolled := unrollForLoops ((var, j) :: paramVals) (depth + 1) substituted
              result := result ++ unrolled
              j := j + inc
            result
          else
            -- SSA rename only self-referential variables
            let mut result : List SVStmt := []
            -- Prologue: capture initial values
            for name in selfRefNames do
              result := result ++ [.blockAssign (.ident s!"{name}{ssaTag}0") (.ident name)]

            let mut j := initVal
            let mut iterIdx : Nat := 0
            while j < b do
              let substituted := unifiedBody.map (substParamStmt [(var, .lit (.decimal (some 32) j))])
              -- SSA rename FIRST (before recursive unroll)
              let mut renamed := substituted
              for name in selfRefNames do
                renamed := renamed.map (renameStmt name s!"{name}{ssaTag}{iterIdx}")
              for name in selfRefNames do
                -- Rename LHS of ALL blockAssigns (including nested in ifElse/forLoop)
                let readName := s!"{name}{ssaTag}{iterIdx}"
                let writeName := s!"{name}{ssaTag}{iterIdx + 1}"
                renamed := renamed.map (renameLhsOnly readName writeName)
              -- THEN recursively unroll nested loops (they see renamed SSA names)
              let unrolled := unrollForLoops ((var, j) :: paramVals) (depth + 1) renamed
              result := result ++ unrolled
              j := j + inc
              iterIdx := iterIdx + 1

            -- Epilogue: write final SSA value back
            for name in selfRefNames do
              result := result ++ [.blockAssign (.ident name) (.ident s!"{name}{ssaTag}{numIters}")]
            result
      | _, _ => [s]
  | .ifElse cond thenB elseB =>
    [.ifElse cond (unrollForLoops paramVals depth thenB) (unrollForLoops paramVals depth elseB)]
  | .caseStmt sel arms dflt =>
    [.caseStmt sel
      (arms.map fun (labels, body) => (labels, unrollForLoops paramVals depth body))
      (dflt.map (unrollForLoops paramVals depth))]
  | other => [other]

def substituteParamsInItem (params : List (String × SVExpr)) (paramVals : List (String × Nat))
    : SVModuleItem → SVModuleItem
  | .alwaysBlock sens stmts =>
    let substituted := stmts.map (substParamStmt params)
    let unrolled := unrollForLoops paramVals 0 substituted
    .alwaysBlock sens unrolled
  | .contAssign lhs rhs => .contAssign (substParamExpr params lhs) (substParamExpr params rhs)
  | item => item

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

/-- Lower a single SVModule to Sparkle IR Module, optionally overriding parameters. -/
def lowerModule (svMod : SVModule) (paramOverrides : List (String × Nat) := []) : Except String Module := do
  -- Expand generate blocks using parameter defaults + overrides
  let paramDefaults := extractParamDefaults svMod
  -- Overrides take priority: replace defaults with overridden values
  let paramVals := paramDefaults.map fun (n, v) =>
    match paramOverrides.find? fun (on, _) => on == n with
    | some (_, ov) => (n, ov)
    | none => (n, v)
  let expandedItems := expandGenerateBlocks paramVals svMod.items
  -- Replace parameter references with constants in all SV expressions
  let paramLits : List (String × SVExpr) := paramVals.map fun (n, v) =>
    (n, .lit (.decimal (some 32) v))
  let expandedItems := expandedItems.map (substituteParamsInItem paramLits paramVals)
  -- Also substitute in module-level params
  let svParams := svMod.params.map fun p =>
    match paramVals.find? fun (n, _) => n == p.name with
    | some (_, v) => { p with value := .lit (.decimal (some 32) v) }
    | none => p
  let svMod := { svMod with items := expandedItems, params := svParams }

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

  -- Collect array register names (memory arrays, not scalar registers)
  let arrayRegNames := svMod.items.filterMap fun item => match item with
    | .regDecl name _ (some _) => some name
    | _ => none

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
  -- All always @* blocks now use MUX mode (SSA handles loop dependencies)

  -- Emit parameter values as constant assigns (with overrides applied)
  let paramWidth (w : Option (Nat × Nat)) : Nat :=
    match w with | some (hi, lo) => hi - lo + 1 | none => 32
  for p in svMod.params do
    let val := match paramVals.find? fun (n, _) => n == p.name with
      | some (_, v) => .const (Int.ofNat v) (paramWidth p.width)
      | none => lowerExpr p.value
    body := body ++ [.assign p.name val]
  for item in svMod.items do
    match item with
    | .paramDecl param =>
      let val := match paramVals.find? fun (n, _) => n == param.name with
        | some (_, v) => .const (Int.ofNat v) (paramWidth param.width)
        | none => lowerExpr param.value
      body := body ++ [.assign param.name val]
    | _ => pure ()

  for item in svMod.items do
    match item with
    | .contAssign lhs rhs =>
      match exprToName lhs with
      | some name => body := body ++ [.assign name (lowerExpr rhs)]
      | none =>
        -- Concat-LHS continuous assign: assign {a, b, c} = expr;
        -- Decompose into individual assigns for each target variable
        let assigns := decomposeMultiConcatLhs lhs rhs
        if assigns.isEmpty then
          -- Try single-variable concat (all elements same variable)
          match lowerConcatLhsAssign lhs rhs with
          | some (name, value) => body := body ++ [.assign name value]
          | none => throw s!"continuous assign LHS not supported: {repr lhs}"
        else
          for (name, value) in assigns do
            body := body ++ [.assign name value]
            if !(wireExists wires name) then
              wires := wires ++ [{ name, ty := env.getHWType name }]
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

      -- Collect all register names (exclude array regs handled by Stmt.memory)
      let regNames := (collectAllRegNames stmts).eraseDups.filter
        fun n => !arrayRegNames.any (· == n)
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
      -- Sequential SSA: process statements top-to-bottom, creating SSA wires
      -- for each variable write. This correctly handles read-then-overwrite patterns.
      let (seqStmts, seqWires, finalEnv, _) := emitSequentialSSA stmts [] 0
      body := body ++ seqStmts
      -- Fix wire types: _seqN wires inherit type from their base variable
      let typedSeqWires := seqWires.map fun w =>
        -- Extract base name: "foo_seq3" → "foo"
        let parts := w.name.splitOn "_seq"
        let baseName := if parts.length >= 2 then parts[0]! else w.name
        -- Look up base wire type from existing wires or env
        let baseType := match wires.find? (fun p => p.name == baseName) with
          | some p => p.ty
          | none => match env.getHWType baseName with
            | .bitVector n => if n > 0 then .bitVector n else w.ty
            | other => other
        { w with ty := baseType }
      wires := wires ++ typedSeqWires
      -- Create final assigns: map original variable names to their latest SSA wire
      let sigNames := collectBlockNamesTop stmts |>.eraseDups
      for sigName in sigNames do
        let latestWire := seqEnvLookup finalEnv sigName
        if latestWire != sigName then
          body := body ++ [.assign sigName (.ref latestWire)]
          if !wireExists wires sigName then
            let sigTy := env.getHWType sigName
            wires := wires ++ [{ name := sigName, ty := sigTy }]
    | .wireDecl name _ (some initExpr) =>
      -- wire x = expr; → assign
      body := body ++ [.assign name (lowerExpr initExpr)]
    | .regDecl name width (some arraySize) =>
      -- Array reg → Stmt.memory for JIT memory access
      -- Do NOT add to wires list — Stmt.memory creates the class member.
      let dataWidth := widthToBits width
      let addrWidth := Nat.log2 arraySize + (if Nat.isPowerOfTwo arraySize then 0 else 1)
      -- Extract array writes from always blocks
      let mut writeAddr : Expr := .const 0 addrWidth
      let mut writeData : Expr := .const 0 dataWidth
      let mut writeEnable : Expr := .const 0 1
      for prevItem in svMod.items do
        match prevItem with
        | .alwaysBlock (.posedge _) stmts =>
          -- Try full-word writes first: arr[idx] <= data
          let arrayWrites := collectArrayWrites name stmts
          if !arrayWrites.isEmpty then
            for (idx, data, cond) in arrayWrites do
              writeAddr := lowerExpr idx
              writeData := lowerExpr data
              writeEnable := match cond with
                | some c => lowerExpr c
                | none => .const 1 1
          else
            -- Try byte-lane writes: if (wstrb[n]) arr[addr][hi:lo] <= data[hi:lo]
            let byteLanes := collectByteLaneWrites name stmts
            match byteLanes with
            | lane0 :: _ =>
              let addr := lowerExpr lane0.addr
              writeAddr := addr
              writeData := buildByteStrobeWrite name addr byteLanes
              -- Enable if any strobe bit is set
              let enableExpr := byteLanes.foldl (fun acc lane =>
                let c := lowerExpr lane.cond
                if acc == Expr.const 0 1 then c else Expr.op .or [acc, c]
              ) (Expr.const 0 1)
              writeEnable := enableExpr
            | [] => pure ()
        | _ => pure ()
      -- Extract read port: continuous assign (combo) or registered read (sync)
      let mut readAddr : Expr := .const 0 addrWidth
      let mut readDataName := s!"{name}_rdata"
      let mut comboRead := true
      for prevItem in svMod.items do
        match prevItem with
        | .contAssign lhs (.index (.ident arrN) idx) =>
          if arrN == name then
            match exprToName lhs with
            | some rdName => readDataName := rdName; readAddr := lowerExpr idx
            | none => pure ()
        | .alwaysBlock (.posedge _) innerStmts =>
          for s in innerStmts do
            match s with
            | .nonblockAssign (.ident rdName) (.index (.ident arrN) idx) =>
              if arrN == name then
                readDataName := rdName; readAddr := lowerExpr idx; comboRead := false
            | _ => pure ()
        | _ => pure ()
      body := body ++ [.memory name addrWidth dataWidth "clk"
        writeAddr writeData writeEnable
        readAddr readDataName comboRead]
      wires := wires ++ [{ name := readDataName, ty := widthToHWType width }]
    | .instantiation modName instName conns _paramOvr =>
      -- Module instantiation → Stmt.inst (parameter overrides resolved at flatten time)
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

  -- Collect assertions from all always blocks
  -- Helper: collect blocking assigns from SV stmts for inlining
  let collectAssignsFromStmts := fun (stmts : List SVStmt) =>
    stmts.filterMap fun s => match s with
      | .blockAssign lhs rhs =>
        match exprToName lhs with
        | some n => some (n, lowerExpr rhs)
        | none => none
      | _ => none
  let mut assertions : List (String × Expr) := []
  let mut assertIdx : Nat := 0
  for item in svMod.items do
    match item with
    | .alwaysBlock _ stmts =>
      let guarded := collectGuardedAsserts stmts
      for (guard, cond) in guarded do
        let inlined := cond  -- assertions reference registers/inputs directly
        let guardedCond := if guard == .const 1 1 then inlined
          else .op .mux [guard, inlined, .const 1 1]
        assertions := assertions ++ [(s!"auto_assert_{assertIdx}", guardedCond)]
        assertIdx := assertIdx + 1
    | _ => pure ()

  pure {
    name := svMod.name
    inputs := inputs
    outputs := outputs
    wires := dedupWires
    body := topoSortBody dedupBody
    assertions := assertions
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

/-- Flatten a design: inline all sub-module instantiations into a single module.
    The optional `svDesign` parameter provides access to the original SV AST
    for re-lowering sub-modules with parameter overrides (e.g., ENABLE_MUL=1). -/
def flattenDesign (design : Design) (svDesign : SVDesign := { modules := [] }) : Design := Id.run do
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
        | none =>
          -- Sub-module not found: emit warning wire and skip
          flatBody := flatBody ++ [.assign s!"_warn_missing_{modName}_{instName}" (.const 0 1)]
        | some subMod =>
          -- Find the SV AST for this instantiation to get parameter overrides
          -- Walk the SV top module items to find the matching instantiation
          let svTopMod? := svDesign.modules.find? fun m => m.name == design.topModule
          let paramOvr : List (String × Nat) := match svTopMod? with
            | some svTop =>
              let expanded := expandGenerateBlocks (extractParamDefaults svTop) svTop.items
              match expanded.findSome? fun item =>
                match item with
                | .instantiation mn _ _ pOvr =>
                  if mn == modName then
                    some (pOvr.filterMap fun (name, expr) =>
                      match expr with
                      | .lit (.decimal _ v) => some (name, v)
                      | .lit (.hex _ v) => some (name, v)
                      | .lit (.binary _ v) => some (name, v)
                      | _ => none)
                  else none
                | _ => none
              with
              | some ovr => ovr
              | none => []
            | none => []

          -- Re-lower the sub-module with parameter overrides applied
          -- This ensures generate-if blocks are expanded with the correct values
          let svSubMod? := svDesign.modules.find? fun m => m.name == modName
          let effectiveSubMod ← match svSubMod? with
            | some svSub =>
              match lowerModule svSub paramOvr with
              | .ok m => pure m
              | .error _ => pure subMod
            | none => pure subMod

          -- Collect all internal names in sub-module (including memory names)
          let memNames := effectiveSubMod.body.filterMap fun s => match s with
            | .memory n _ _ _ _ _ _ _ _ _ => some n | _ => none
          let subNames := effectiveSubMod.wires.map (·.name) ++
                          effectiveSubMod.inputs.map (·.name) ++
                          effectiveSubMod.outputs.map (·.name) ++
                          memNames

          -- Add prefixed wires from sub-module
          for w in effectiveSubMod.wires do
            flatWires := flatWires ++ [{ name := s!"{instName}_{w.name}", ty := w.ty }]
          for p in effectiveSubMod.inputs do
            flatWires := flatWires ++ [{ name := s!"{instName}_{p.name}", ty := p.ty }]
          for p in effectiveSubMod.outputs do
            flatWires := flatWires ++ [{ name := s!"{instName}_{p.name}", ty := p.ty }]

          -- Wire port connections:
          -- Input ports: assign instName_portName = parentExpr
          -- Output ports: assign parentWire/expr = instName_portName
          let inputNames := effectiveSubMod.inputs.map (·.name)
          let outputNames := effectiveSubMod.outputs.map (·.name)
          for (portName, expr) in conns do
            if inputNames.any (· == portName) then
              -- Input: parent drives sub-module's port
              flatBody := flatBody ++ [.assign s!"{instName}_{portName}" expr]
            else if outputNames.any (· == portName) then
              -- Output: sub-module drives parent's wire
              match expr with
              | .ref parentWire =>
                flatBody := flatBody ++ [.assign parentWire (.ref s!"{instName}_{portName}")]
              | _ =>
                -- Complex output expression (array index, bit slice, concat, etc.)
                -- Create a temporary wire and assign the sub-module output to it.
                -- The parent can read from this wire.
                let tmpWire := s!"{instName}_{portName}_out"
                flatWires := flatWires ++ [{ name := tmpWire, ty := .bitVector 32 }]
                flatBody := flatBody ++ [.assign tmpWire (.ref s!"{instName}_{portName}")]

          -- Add prefixed body statements from sub-module
          for s in effectiveSubMod.body do
            let prefixed := match s with
              | .assign name rhs =>
                .assign s!"{instName}_{name}" (prefixExprNames instName subNames rhs)
              | .register name clk rst input init =>
                .register s!"{instName}_{name}" s!"{instName}_{clk}" s!"{instName}_{rst}"
                  (prefixExprNames instName subNames input) init
              | .inst subModName subInstName subConns =>
                -- Keep nested .inst with prefixed names — will be flattened in next iteration
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
  -- Use first module as top (flat wrapper is first, sub-modules follow)
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
  -- Iteratively flatten until no .inst remains (handles nested sub-modules)
  let hasInst (d : Design) : Bool :=
    match d.modules.head? with
    | some m => m.body.any fun s => match s with | .inst .. => true | _ => false
    | none => false
  let mut result := flattenDesign design svDesign
  -- For nested hierarchies: re-flatten with all original modules available
  for _ in [:5] do
    if hasInst result then
      -- Re-add all original sub-modules so the flattener can find them
      let enriched := { result with modules := result.modules ++ design.modules }
      result := flattenDesign enriched svDesign
    else break
  -- Remove debug/trace statements from IR before optimization.
  -- PicoRV32 debug wires (dbg_ascii, dbg_insn, new_ascii_instr, trace,
  -- cached_insn, q_insn) don't affect simulation and waste ~36% of eval time.
  let isDebug (name : String) : Bool :=
    (name.splitOn "dbg_ascii").length > 1 || (name.splitOn "dbg_insn").length > 1 ||
    (name.splitOn "new_ascii_instr").length > 1 || (name.splitOn "trace_data").length > 1 ||
    (name.splitOn "trace_valid").length > 1 || (name.splitOn "dbg_next").length > 1 ||
    (name.splitOn "q_insn_").length > 1 || (name.splitOn "cached_insn_").length > 1 ||
    (name.splitOn "dbg_insn_opcode").length > 1 || (name.splitOn "dbg_rs").length > 1
  -- Also replace refs to debug wires with const 0 in all expressions
  let rec stripDebugRefs : Expr → Expr
    | .ref name => if isDebug name then .const 0 32 else .ref name
    | .const v w => .const v w
    | .slice e hi lo => .slice (stripDebugRefs e) hi lo
    | .concat args => .concat (args.map stripDebugRefs)
    | .op op args => .op op (args.map stripDebugRefs)
    | .index arr idx => .index (stripDebugRefs arr) (stripDebugRefs idx)
  let stripStmt : Stmt → Stmt
    | .assign lhs rhs => .assign lhs (stripDebugRefs rhs)
    | .register o c r input iv => .register o c r (stripDebugRefs input) iv
    | .memory n aw dw clk wa wd we ra rd cr =>
      .memory n aw dw clk (stripDebugRefs wa) (stripDebugRefs wd) (stripDebugRefs we) (stripDebugRefs ra) rd cr
    | s => s
  let stripped := { result with modules := result.modules.map fun m =>
    { m with
      body := (m.body.filter fun s => match s with
        | .assign lhs _ => !isDebug lhs
        | .register output _ _ _ _ => !isDebug output
        | _ => true).map stripStmt
      wires := m.wires.filter fun w => !isDebug w.name } }
  -- Optimize: constant folding, DCE, single-use wire inlining
  let optimized := Sparkle.IR.Optimize.optimizeDesign stripped
  pure optimized

def parseAndLowerWithMemInit (input : String) : Except String (Design × List ReadMemHInfo) := do
  let svDesign ← Tools.SVParser.Parser.parse input
  let design ← lowerDesign svDesign
  let memInits := extractReadMemH svDesign
  pure (design, memInits)

end Tools.SVParser.Lower
