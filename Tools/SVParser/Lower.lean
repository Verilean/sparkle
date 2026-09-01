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

-- HashMap-backed: these tables were `List` with linear `find?`/`any`
-- per lookup AND `++ [x]` per insertion — O(decls²) to build and
-- O(decls) per query.  XiangShan's Rob (12,804 registers, ~30k decls)
-- spent ~85% of its 100 s lower phase in `isReg` scans and list copies.
structure LowerEnv where
  portWidths  : Std.HashMap String (Option (Nat × Nat))  -- port name → width
  wireWidths  : Std.HashMap String (Option (Nat × Nat))  -- wire name → width
  regNames    : Std.HashMap String Bool                  -- names declared as reg
  signedNames : Std.HashMap String Bool := {}            -- ports declared `signed`

def LowerEnv.empty : LowerEnv :=
  { portWidths := {}, wireWidths := {}, regNames := {}, signedNames := {} }

def LowerEnv.getWidth (env : LowerEnv) (name : String) : Option (Nat × Nat) :=
  (env.portWidths.get? name).join <|> (env.wireWidths.get? name).join

def LowerEnv.getHWType (env : LowerEnv) (name : String) : HWType :=
  widthToHWType (env.getWidth name)

def LowerEnv.isReg (env : LowerEnv) (name : String) : Bool :=
  env.regNames.contains name

/-- Conservative signedness inference for SV expressions: an expression
    is *signed* iff its top-level operand reaches a declared-`signed`
    port or wire.  Mirrors Verilog's "context-determined" signedness
    only in the common operand-ref case; sub-expressions involving
    arithmetic are treated as unsigned (matches IR `op` semantics). -/
def LowerEnv.isSignedRef (env : LowerEnv) (name : String) : Bool :=
  env.signedNames.contains name

/-- `staticExprWidth` with an ENVIRONMENT: identifiers resolve through the
    module's declarations.  `^{mshrInfo_blkPAddr[41:6], wire_a, wire_b, …}`
    (ICacheMissUnit's meta-entry parity) has no static width — every bare
    ident defeated `expandReductXor`, the sentinel wire was then declared
    by `declareOrphanRefs` and const-folded, and the parity silently
    became 0.  With the environment the width is exact. -/
partial def envExprWidth (env : LowerEnv) : SVExpr → Option Nat
  | .ident n =>
    if env.portWidths.contains n || env.wireWidths.contains n then
      some (match env.getWidth n with
        | some (hi, lo) => hi - lo + 1
        | none => 1)
    else none
  | .slice _ hi lo => some (hi - lo + 1)
  | .sizeCast w _ => some w
  | .index _ _ => some 1
  | .partSelectPlus _ _ (.lit (.decimal none w)) => some w
  | .lit (.decimal (some w) _) => some w
  | .lit (.hex (some w) _) => some w
  | .lit (.binary (some w) _) => some w
  | .concat args => args.foldl (fun acc a =>
      match acc, envExprWidth env a with
      | some x, some y => some (x + y)
      | _, _ => none) (some 0)
  | .ternary _ t e =>
    match envExprWidth env t, envExprWidth env e with
    | some wt, some we => some (max wt we)
    | some wt, none => some wt
    | none, some we => some we
    | none, none => none
  | .repeat_ (.lit (.decimal _ n)) v => (envExprWidth env v).map (n * ·)
  | .unary .bitNot a => envExprWidth env a
  | .unary .neg a => envExprWidth env a
  | .unary .signed a => envExprWidth env a
  | .unary .reductAnd _ | .unary .reductOr _ | .unary .reductXor _
  | .unary .logNot _ => some 1
  | .binary .eq _ _ | .binary .neq _ _ | .binary .lt _ _ | .binary .le _ _
  | .binary .gt _ _ | .binary .ge _ _
  | .binary .logAnd _ _ | .binary .logOr _ _ => some 1
  | .binary .bitAnd a b | .binary .bitOr a b | .binary .bitXor a b =>
    match envExprWidth env a, envExprWidth env b with
    | some wa, some wb => some (max wa wb)
    | some wa, none => some wa
    | none, some wb => some wb
    | none, none => none
  | _ => none

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
  | .reductXor => .not  -- unreachable: expanded in lowerExpr

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
  -- `binaryWild` outside a `casez` arm: drop the mask (Verilog semantics
  -- for `?`/`x`/`z` in plain expressions are undefined; treat as 0).
  | .binaryWild w v _   => .const (Int.ofNat v) w

/-- Set of array-typed register names for distinguishing bit-select vs array access -/
private def arrayNames : List String := []  -- populated per-module during lowering

private def indexToConst : SVExpr → Option Nat
  | .lit (.decimal _ n) => some n
  | .lit (.hex _ n) => some n
  | .lit (.binary _ n) => some n
  | _ => none

def isArrayName (name : String) : Bool :=
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
  | .sizeCast w _ => w
  | .slice _ hi lo => hi - lo + 1
  | .partSelectPlus _ _ widthExpr => svExprToNat widthExpr |>.getD 1
  | .index _ _ => 1  -- single bit select
  | .lit (.decimal (some w) _) => w
  | .lit (.hex (some w) _) => w
  | .lit (.binary (some w) _) => w
  | .lit (.decimal none _) => 32
  | .lit (.hex none _) => 32
  | .lit (.binary none _) => 1
  | .lit (.binaryWild w _ _) => w  -- casez wildcard: width is always explicit
  | _ => 32  -- default: assume 32-bit

/-- Static (env-free) width of an SVExpr, where determinable. -/
private def staticExprWidth : SVExpr → Option Nat
  | .slice _ hi lo => some (hi - lo + 1)
  | .sizeCast w _ => some w
  | .index _ _ => some 1
  | .partSelectPlus _ _ (.lit (.decimal none w)) => some w
  | .lit (.decimal (some w) _) => some w
  | .lit (.hex (some w) _) => some w
  | .lit (.binary (some w) _) => some w
  | .concat args => args.foldl (fun acc a =>
      match acc, staticExprWidth a with
      | some x, some y => some (x + y)
      | _, _ => none) (some 0)
  -- A ternary is as wide as its arms.  Without this, `^(cond ? 8'h0 :
  -- beat[255:248])` had no static width, so the parity expansion bailed
  -- to the undeclared-wire sentinel and `io_out_bits_dataCheck` collapsed
  -- to a constant — XiangShan's TXDAT computes 32 parity bytes exactly
  -- this way.  Prefer whichever arm resolves; if both do and they differ,
  -- decline rather than guess.
  | .ternary _ t e =>
    match staticExprWidth t, staticExprWidth e with
    | some wt, some we => if wt == we then some wt else some (max wt we)
    | some wt, none => some wt
    | none, some we => some we
    | none, none => none
  -- `{n{expr}}` is n copies of a statically-known operand.
  | .repeat_ (.lit (.decimal _ n)) v =>
    (staticExprWidth v).map (n * ·)
  -- These pass their operand's width through unchanged.
  | .unary .bitNot a => staticExprWidth a
  | .unary .neg a => staticExprWidth a
  | .unary .signed a => staticExprWidth a
  -- Reductions and logical negation are always one bit.
  | .unary .reductAnd _ | .unary .reductOr _ | .unary .reductXor _
  | .unary .logNot _ => some 1
  | .binary .eq _ _ | .binary .neq _ _ | .binary .lt _ _ | .binary .le _ _
  | .binary .gt _ _ | .binary .ge _ _
  | .binary .logAnd _ _ | .binary .logOr _ _ => some 1
  -- Bitwise binaries are as wide as their widest operand.
  | .binary .bitAnd a b | .binary .bitOr a b | .binary .bitXor a b =>
    match staticExprWidth a, staticExprWidth b with
    | some wa, some wb => some (max wa wb)
    | some wa, none => some wa
    | none, some wb => some wb
    | none, none => none
  | _ => none

/-- Annotate every `^expr` whose width is NOT statically visible with a
    size cast resolved from the environment, so `expandReductXor` can
    expand it instead of bailing to its sentinel. -/
partial def annotateRXExpr (env : LowerEnv) : SVExpr → SVExpr
  | .unary .reductXor a =>
    let a' := annotateRXExpr env a
    if (staticExprWidth a').isSome then .unary .reductXor a'
    else match envExprWidth env a' with
      | some w => .unary .reductXor (.sizeCast w a')
      | none => .unary .reductXor a'
  | .unary op a => .unary op (annotateRXExpr env a)
  | .binary op a b => .binary op (annotateRXExpr env a) (annotateRXExpr env b)
  | .ternary c t e =>
    .ternary (annotateRXExpr env c) (annotateRXExpr env t) (annotateRXExpr env e)
  | .index a i => .index (annotateRXExpr env a) (annotateRXExpr env i)
  | .slice e hi lo => .slice (annotateRXExpr env e) hi lo
  | .partSelectPlus e b w =>
    .partSelectPlus (annotateRXExpr env e) (annotateRXExpr env b) (annotateRXExpr env w)
  | .concat args => .concat (args.map (annotateRXExpr env))
  | .repeat_ c v => .repeat_ c (annotateRXExpr env v)
  | .sizeCast w a => .sizeCast w (annotateRXExpr env a)
  | e => e

partial def annotateRXStmt (env : LowerEnv) : SVStmt → SVStmt
  | .blockAssign l r => .blockAssign l (annotateRXExpr env r)
  | .nonblockAssign l r => .nonblockAssign l (annotateRXExpr env r)
  | .ifElse c t e =>
    .ifElse (annotateRXExpr env c) (t.map (annotateRXStmt env)) (e.map (annotateRXStmt env))
  -- Every statement form that can hold an expression: Directory's ECC
  -- syndrome parities sat inside a case arm and stayed unannotated.
  | .caseStmt e arms dflt =>
    .caseStmt (annotateRXExpr env e)
      (arms.map fun (gs, ss) => (gs.map (annotateRXExpr env), ss.map (annotateRXStmt env)))
      (dflt.map (·.map (annotateRXStmt env)))
  | .forLoop i c st body =>
    .forLoop (annotateRXStmt env i) (annotateRXExpr env c)
      (annotateRXStmt env st) (body.map (annotateRXStmt env))
  | .assertStmt c => .assertStmt (annotateRXExpr env c)

partial def annotateRXItem (env : LowerEnv) : SVModuleItem → SVModuleItem
  | .contAssign l r => .contAssign l (annotateRXExpr env r)
  | .alwaysBlock trig stmts => .alwaysBlock trig (stmts.map (annotateRXStmt env))
  | .wireDecl n w (some e) => .wireDecl n w (some (annotateRXExpr env e))
  | .packedArrayDecl n d (some e) => .packedArrayDecl n d (some (annotateRXExpr env e))
  | .generateBlock c b eb =>
    .generateBlock (annotateRXExpr env c)
      (b.map (annotateRXItem env)) (eb.map (annotateRXItem env))
  | it => it


/-- Expand `^expr` (reduction XOR / parity) into an explicit bit fold when
    the operand width is statically known — firtool's uses are all slices
    (`~(^(data[255:248]))` parity bytes), so this covers them without any
    width environment.  For a slice, bits index the BASE directly to avoid
    nested slices. -/
private def expandReductXor (a : SVExpr) : Option SVExpr := do
  let w ← staticExprWidth a
  if w == 0 then return .lit (.binary (some 1) 0)
  let bit := fun (i : Nat) =>
    match a with
    | .slice base _ lo => SVExpr.slice base (lo + i) (lo + i)
    | _ => SVExpr.slice a i i
  return (List.range (w - 1)).foldl
    (fun acc i => SVExpr.binary .bitXor acc (bit (i + 1))) (bit 0)

/-- Signedness marker checks for comparison lowering: `$signed(x)` and `'s`
    literals wrap their expression in `.unary .signed`; a leading unary minus
    (`-7'sh1`) sits above the marker. -/
private def hasSignedMark : SVExpr → Bool
  | .unary .signed _ => true
  | .unary .neg a => hasSignedMark a
  | _ => false

private def stripSignedMark : SVExpr → SVExpr
  | .unary .signed a => a
  | .unary .neg a => .unary .neg (stripSignedMark a)
  | e => e

partial def lowerExpr (e : SVExpr) : Expr :=
  match e with
  | .lit l => literalToConst l
  | .ident name => .ref name
  | .sizeCast w arg =>
    -- N'(expr): resize to exactly w bits without needing the operand's
    -- width — prepend w zero bits, take the low w.  Zero-extends narrow
    -- operands, truncates wide ones; `resolveSliceOfConcat` in the IR
    -- optimizer folds the indirection away.
    .slice (.concat [.const 0 w, lowerExpr arg]) (w - 1) 0
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
  | .unary .reductXor arg =>
    -- Parity: expanded to an explicit XOR fold when the width is static;
    -- otherwise fail LOUDLY downstream via an undeclared wire rather than
    -- guessing a width (a wrong parity is a silent miscompile).
    match expandReductXor arg with
    | some e => lowerExpr e
    | none => .ref "__reduction_xor_unknown_width__"
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
  | .binary .lt lhs rhs =>
    -- Comparisons: a `$signed(…)`/`'s`-literal marker on EITHER side selects
    -- the signed IR operator; markers are stripped so both sides compare at
    -- their native width (firtool always emits same-width operands here).
    let sgn := hasSignedMark lhs || hasSignedMark rhs
    .op (if sgn then .lt_s else .lt_u)
      [lowerExpr (stripSignedMark lhs), lowerExpr (stripSignedMark rhs)]
  | .binary .le lhs rhs =>
    let sgn := hasSignedMark lhs || hasSignedMark rhs
    .op (if sgn then .le_s else .le_u)
      [lowerExpr (stripSignedMark lhs), lowerExpr (stripSignedMark rhs)]
  | .binary .gt lhs rhs =>
    let sgn := hasSignedMark lhs || hasSignedMark rhs
    .op (if sgn then .gt_s else .gt_u)
      [lowerExpr (stripSignedMark lhs), lowerExpr (stripSignedMark rhs)]
  | .binary .ge lhs rhs =>
    let sgn := hasSignedMark lhs || hasSignedMark rhs
    .op (if sgn then .ge_s else .ge_u)
      [lowerExpr (stripSignedMark lhs), lowerExpr (stripSignedMark rhs)]
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
          -- Wrapped in `.slice … 0 0` for the same reason as
          -- `.partSelectPlus` below: the bare and-mask's inferred width
          -- is the CONTAINER's, so as a self-determined concat element it
          -- inflated and shifted its siblings out (VpnTable's
          -- `{_GEN_35[i], _GEN_34[i], …}` subValid vector).
          .slice (.op .and [.op .shr [lowerExpr arr, lowerExpr idx], .const 1 1]) 0 0
      | _ =>
        .slice (.op .and [.op .shr [lowerExpr arr, lowerExpr idx], .const 1 1]) 0 0
  | .slice expr hi lo => .slice (lowerExpr expr) hi lo
  | .partSelectPlus expr base widthExpr =>
    -- [base +: width] = (expr >> base) & ((1 << width) - 1), wrapped in
    -- an explicit `.slice … (width-1) 0`.  The bare and-mask carries NO
    -- width metadata — both backends infer the CONTAINER's width from
    -- the shift, so as a self-determined concat element it inflated to
    -- 64 bits and pushed every element above it out of the target
    -- (MiscModule's 16-nibble xperm gather kept only its LAST nibble).
    -- The slice pins the width; the Verilog emitter renders it as a
    -- size cast, and CSim's slice arm truncates.
    let width := svExprToNat widthExpr |>.getD 1
    let mask := (1 <<< width) - 1
    .slice (.op .and [.op .shr [lowerExpr expr, lowerExpr base],
                      .const (Int.ofNat mask) width]) (width - 1) 0
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

/-- Bit/part-select bounds of an assignment LHS, when it writes only PART
    of its target: `gnt[0]` → `(0, 0)`, `gnt[3:1]` → `(3, 1)`.  A bare
    identifier writes the whole vector and yields `none`, as does a
    non-constant index (a dynamic write, which cannot be merged
    statically). -/
def lhsSelectBounds : SVExpr → Option (Nat × Nat)
  | .index (.ident name) (.lit (.decimal _ idx)) =>
    if isArrayName name then none else some (idx, idx)
  | .slice (.ident name) hi lo => if isArrayName name then none else some (hi, lo)
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
    For normal case, labels are compared against sel.
    For `casez`-style wildcard literals (`SVLiteral.binaryWild`) the
    comparison ignores bits marked as don't-care in the mask:
        ((sel ^ value) & ~mask) == 0 -/
private def mkCaseCond (sel : SVExpr) (labels : List SVExpr) : Expr :=
  let isCase1b1 := match sel with
    | .lit (.binary (some 1) 1) => true
    | .lit (.decimal (some 1) 1) => true
    | _ => false
  let selExpr := lowerExpr sel
  let oneCond : SVExpr → Expr := fun label =>
    match label with
    | .lit (.binaryWild w v m) =>
      -- (sel ^ value) & ~mask == 0
      let notMask := (2^w - 1).xor m  -- ~mask, sized to w
      let valExpr := Expr.const (Int.ofNat v) w
      let maskExpr := Expr.const (Int.ofNat notMask) w
      Expr.op .eq
        [Expr.op .and [Expr.op .xor [selExpr, valExpr], maskExpr],
         Expr.const 0 w]
    | _ =>
      if isCase1b1 then lowerExpr label
      else Expr.op .eq [selExpr, lowerExpr label]
  labels.foldl (fun acc label =>
    let c := oneCond label
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
      -- A write to a BIT RANGE is not a whole-signal value: `exprToName`
      -- answers `q` for `q[35]`, which used to capture the bare RHS and
      -- lose the position.  Leave those to the partial-assign merge.
      else if (lhsSelectBounds lhs).isSome then []
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
-- Accumulator form — the flatMap version re-copied child result lists at
-- every ancestor, O(nodes × depth) on XiangShan-scale mux chains (see
-- Optimize.collectExprRefsAux).
partial def collectRefsAux (acc : List String) : Expr → List String
  | .ref name => name :: acc
  | .op _ args => args.foldl collectRefsAux acc
  | .concat args => args.foldl collectRefsAux acc
  | .slice e _ _ => collectRefsAux acc e
  | .sliceDim e _ _ => collectRefsAux acc e
  | .index a i => collectRefsAux (collectRefsAux acc a) i
  | _ => acc

def collectRefs (e : Expr) : List String := collectRefsAux [] e

/-- Does this lowered condition mean `¬reset`?  Sparkle's own emission
    of the register mux produces several encodings of the same guard
    (`~(reset)` → xor -1/32, `reset ^ 1'h1` → xor 1/1, and the same
    under a 1-bit cast encode).  All agree OUT of reset (reset = 0 →
    nonzero → the mux picks its then-branch), which is the only case
    the strip below needs: under reset the register's own (rst, init)
    fields win. -/
partial def isNotOfReset (rst : String) : Expr → Bool
  | .op .not [.ref r] => r == rst
  | .op .xor [.ref r, .const 1 1] => r == rst
  | .op .xor [.ref r, .const (-1) _] => r == rst
  | .slice (.concat [.const 0 1, inner]) 0 0 => isNotOfReset rst inner
  | _ => false

/-- Strip the redundant reset mux from a register's reconstructed input.
    Sparkle emits a register as `if (rst) r <= init; else r <= X;` where
    the register statement ALSO carries (rst, init) — so the
    reconstruction wrapped X in `mux(¬rst, X, init)` (and `mux(rst,
    init, X)`) once more per reparse, and the roundtrip grew one mux
    layer per generation (certified-roundtrip idempotence check).
    Semantically inert: under reset the register's own init wins; out of
    reset every encoding of the guard picks X. -/
partial def stripResetMux (rst : String) (init : Int) : Expr → Expr
  | e@(.op .mux [c, x, .const iv _]) =>
    if isNotOfReset rst c && iv == init then stripResetMux rst init x else e
  | e@(.op .mux [.ref r, .const iv _, x]) =>
    if r == rst && iv == init then stripResetMux rst init x else e
  | e => e

/-- Apply `stripResetMux` to every register input in a design.  Runs
    AFTER `Optimize.optimizeDesign`: the redundant layer only reaches
    the strippable `mux(¬rst, x, init)` shape once the optimizer folds
    the dead `rst ? init : q` arm out of its else branch. -/
def stripResetMuxDesign (d : Design) : Design :=
  { d with modules := d.modules.map fun m =>
      { m with body := m.body.map fun st => match st with
          | .register out clk (rst, kind) input init =>
            .register out clk (rst, kind) (stripResetMux rst init input) init
          | st => st } }

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
def stmtsToMuxExprBlocking (sigName : String) (stmts : List SVStmt)
    (pre : Option (List GuardedAssign) := none) : Expr :=
  -- A blocking write to a BIT RANGE of the signal (`q[35] = d`) is not
  -- a whole-signal assignment: taking `lowerExpr rhs` alone dropped the
  -- position entirely, so `q[35] = d; q[3] = d;` on a 40-bit `q`
  -- lowered to `q = d` — the scatter lost and a 1-bit value driving a
  -- 40-bit target.  Such a write needs a read-modify-write, which this
  -- whole-signal mux builder cannot express, so it is refused here and
  -- left to the partial-assign merge (`lhsSelectBounds`).
  let initDefault := stmts.findSome? fun s => match s with
    | .blockAssign lhs rhs =>
      match lhsSelectBounds lhs with
      | some _ => none          -- bit-range write: not a whole-signal value
      | none =>
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
  -- `collectGuardedBlock` re-lowers every RHS in the block; callers that
  -- loop over many signals precompute it ONCE and pass it in (Rob: this
  -- was quadratic in block size × signal count).
  let all := pre.getD (collectGuardedBlock stmts)
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
        | .sliceDim inner hi lo => .sliceDim (substSelf inner) hi lo
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

/-- All nonblocking assigns to plain idents, RAW (un-lowered) RHS,
    recursing through if/case — for recognising sync-read targets. -/
partial def collectNBRaw : List SVStmt → List (String × SVExpr)
  | [] => []
  | .nonblockAssign (.ident n) rhs :: rest => (n, rhs) :: collectNBRaw rest
  | .ifElse _ t e :: rest => collectNBRaw t ++ collectNBRaw e ++ collectNBRaw rest
  | .caseStmt _ arms default_ :: rest =>
    arms.flatMap (fun (_, b) => collectNBRaw b)
      ++ (match default_ with | some b => collectNBRaw b | none => [])
      ++ collectNBRaw rest
  | _ :: rest => collectNBRaw rest

mutual
/-- Extract reads of ONE array (`arr[idx]`) from a raw SVExpr, replacing
    each with a fresh placeholder ident.  The regDecl memory scan lowers
    write data through `lowerExpr`, which without module context turned
    `Memory[addr]` into a bit-select of the ARRAY (the isArrayName
    heuristic misses names like "Memory") — a silent self-reparse
    miscompile of byte-strobe RMW write data.  The scan KNOWS its own
    array name, so reads of it are pulled out first and re-attached as
    proper `.index` nodes after lowering.  TOTAL, so the certified-
    roundtrip twin can reuse it verbatim. -/
def extractArrayReads (arr : String) :
    SVExpr → Nat → (SVExpr × List (String × SVExpr) × Nat)
  | .index (.ident a) idx, k =>
    if a == arr then
      let ph := s!"__memread_{arr}_{k}"
      (.ident ph, [(ph, idx)], k + 1)
    else
      let (idx', l, k') := extractArrayReads arr idx k
      (.index (.ident a) idx', l, k')
  | .index a idx, k =>
    let (a', l1, k1) := extractArrayReads arr a k
    let (idx', l2, k2) := extractArrayReads arr idx k1
    (.index a' idx', l1 ++ l2, k2)
  | .unary op a, k =>
    let (a', l, k') := extractArrayReads arr a k
    (.unary op a', l, k')
  | .binary op a b, k =>
    let (a', l1, k1) := extractArrayReads arr a k
    let (b', l2, k2) := extractArrayReads arr b k1
    (.binary op a' b', l1 ++ l2, k2)
  | .ternary c t e, k =>
    let (c', l1, k1) := extractArrayReads arr c k
    let (t', l2, k2) := extractArrayReads arr t k1
    let (e', l3, k3) := extractArrayReads arr e k2
    (.ternary c' t' e', l1 ++ l2 ++ l3, k3)
  | .slice x hi lo, k =>
    let (x', l, k') := extractArrayReads arr x k
    (.slice x' hi lo, l, k')
  | .partSelectPlus x b w, k =>
    let (x', l1, k1) := extractArrayReads arr x k
    let (b', l2, k2) := extractArrayReads arr b k1
    let (w', l3, k3) := extractArrayReads arr w k2
    (.partSelectPlus x' b' w', l1 ++ l2 ++ l3, k3)
  | .concat args, k =>
    let (args', l, k') := extractArrayReadsList arr args k
    (.concat args', l, k')
  | .repeat_ c v, k =>
    let (v', l, k') := extractArrayReads arr v k
    (.repeat_ c v', l, k')
  | .sizeCast w a, k =>
    let (a', l, k') := extractArrayReads arr a k
    (.sizeCast w a', l, k')
  | e, k => (e, [], k)

/-- List version of `extractArrayReads` (kept separate for totality). -/
def extractArrayReadsList (arr : String) :
    List SVExpr → Nat → (List SVExpr × List (String × SVExpr) × Nat)
  | [], k => ([], [], k)
  | a :: rest, k =>
    let (a', l1, k1) := extractArrayReads arr a k
    let (rest', l2, k2) := extractArrayReadsList arr rest k1
    (a' :: rest', l1 ++ l2, k2)
end

/-- Substitute placeholder refs back as proper array-read nodes.  TOTAL
    (twin-reusable). -/
def substArrayReads (subs : List (String × Expr)) : Expr → Expr
  | .ref n =>
    match subs.find? (·.1 == n) with
    | some (_, e) => e
    | none => .ref n
  | .op o args => .op o (args.map (substArrayReads subs))
  | .concat args => .concat (args.map (substArrayReads subs))
  | .slice x hi lo => .slice (substArrayReads subs x) hi lo
  | .sliceDim x hi lo => .sliceDim (substArrayReads subs x) hi lo
  | .index a i => .index (substArrayReads subs a) (substArrayReads subs i)
  | e => e

/-- Lower a memory-write payload with reads of the memory's OWN array
    preserved as `.index` nodes (see `extractArrayReads`). -/
def lowerMemPayload (arr : String) (e : SVExpr) : Expr :=
  let (e', reads, _) := extractArrayReads arr e 0
  substArrayReads
    (reads.map fun (ph, ix) => (ph, .index (.ref arr) (lowerExpr ix)))
    (lowerExpr e')

/-- Literal-only constant evaluator (for part-select bases/widths in
    memory-write patterns; full `evalConstExpr` is defined later). -/
private def evalConstExprSimple : SVExpr → Option Nat
  | .lit (.decimal _ v) => some v
  | .lit (.hex _ v) => some v
  | .lit (.binary _ v) => some v
  | _ => none

/-- Collect byte-lane writes: if (cond) arr[addr][hi:lo] <= data[hi:lo] -/
partial def collectByteLaneWrites (arrName : String) (stmts : List SVStmt)
    : List ByteLaneWrite :=
  stmts.flatMap fun s => match s with
    | .nonblockAssign (.slice (.index (.ident name) addr) hi lo) rhs =>
      if name == arrName then [{ addr, data := rhs, cond := .lit (.decimal none 1), hi, lo }] else []
    | .nonblockAssign (.partSelectPlus (.index (.ident name) addr) base wExpr) rhs =>
      -- firtool SRAM macros write mask chunks as
      -- `Memory[addr][32'h1D +: 29] <= wdata[57:29]` — a constant-base
      -- indexed part-select.
      if name == arrName then
        match evalConstExprSimple base, evalConstExprSimple wExpr with
        | some lo, some w =>
          if w == 0 then []
          else [{ addr, data := rhs, cond := .lit (.decimal none 1), hi := lo + w - 1, lo }]
        | _, _ => []
      else []
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
def buildByteStrobeWrite (arrName : String) (addrExpr : Expr)
    (lanes : List ByteLaneWrite) (dataWidth : Nat := 32) : Expr :=
  -- Start with the old value: arr[addr]
  let oldVal := Expr.index (.ref arrName) addrExpr
  let allOnes : Int := Int.ofNat ((1 <<< dataWidth) - 1)
  -- Per lane: acc' = (acc & ~effMask) | (data<<lo & effMask), where
  -- effMask = cond ? laneMask : 0.  The condition selects between two
  -- CONSTANTS, so `acc` appears exactly ONCE per lane — the previous
  -- `cond ? f(acc) : acc` form referenced it twice and the tree doubled
  -- per lane: firtool's per-BIT write masks (array_128x38: 38 lanes)
  -- made lowering build a 2^38-node expression.  (The old constants were
  -- also hardcoded 32-bit, corrupting words wider than 32.)
  lanes.foldl (fun acc lane =>
    let condExpr := lowerExpr lane.cond
    let dataExpr := lowerExpr lane.data
    let width := lane.hi - lane.lo + 1
    let mask : Nat := ((1 <<< width) - 1) <<< lane.lo
    let notMask : Int := Int.ofNat (((1 <<< dataWidth) - 1) ^^^ mask)
    let effMask := Expr.op .mux [condExpr,
      Expr.const (Int.ofNat mask) dataWidth, Expr.const 0 dataWidth]
    let effNotMask := Expr.op .mux [condExpr,
      Expr.const notMask dataWidth, Expr.const allOnes dataWidth]
    -- The shift AMOUNT is declared at `dataWidth`, not 32.  A shift's
    -- IR width is the max of its operands, so a 32-bit amount forced
    -- the whole payload to 32 bits regardless of the memory's data
    -- width — a 10-bit `Memory` got a 32-bit write value, disagreeing
    -- with its own declaration.  (Every other constant in this
    -- function already uses `dataWidth`; this one was missed.)
    let shiftedData := if lane.lo == 0 then dataExpr
      else Expr.op .shl [dataExpr,
             Expr.const (Int.ofNat lane.lo) dataWidth]
    Expr.op .or [
      Expr.op .and [acc, effNotMask],
      Expr.op .and [shiftedData, effMask]
    ]
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
  | .sliceDim e hi lo => .sliceDim (substExprEnv env e) hi lo
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

-- Array/HashMap Kahn: the List version appended per statement (O(n²))
-- and did LINEAR `assignNames.any` / `emitted.any` per DEPENDENCY per
-- PASS — 71% of the whole lower phase on XiangShan's Rob (~30k assigns).
def topoSortBody (body : List Stmt) : List Stmt := Id.run do
  let mut assigns : Array (String × Expr) := #[]
  let mut registers : Array Stmt := #[]
  let mut memories : Array Stmt := #[]
  let mut others : Array Stmt := #[]
  for s in body do
    match s with
    | .assign name rhs => assigns := assigns.push (name, rhs)
    | .register _ _ _ _ _ => registers := registers.push s
    | .memory _ _ _ _ _ _ _ _ _ _ .. => memories := memories.push s
    | _ => others := others.push s
  let assignNameSet : Std.HashMap String Bool :=
    assigns.foldl (fun h (n, _) => h.insert n true) {}
  let mut sorted : Array Stmt := #[]
  let mut emitted : Std.HashMap String Bool := {}
  let mut remaining := assigns.toList
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
  let mut changed := true
  while changed do
    changed := false
    let mut nextRemaining : Array (String × Expr) := #[]
    for (name, rhs) in remaining do
      let deps := collectRefs rhs
      let isSsaPrologue := isSsaPrologueName name
      let prologueBase := if isSsaPrologue then ssaPrologueBase name else none
      let depsReady := deps.all fun dep =>
        dep == name ||
        !(assignNameSet.contains dep) || emitted.contains dep ||
        (isSsaPrologue && prologueBase.any (· == dep))
      if depsReady then
        sorted := sorted.push (.assign name rhs)
        emitted := emitted.insert name true
        changed := true
      else
        nextRemaining := nextRemaining.push (name, rhs)
    remaining := nextRemaining.toList
  if !remaining.isEmpty then
    dbg_trace s!"[TOPO WARNING] {remaining.length} assigns have cyclic deps (of {assigns.size} total). Names: {remaining.map (·.1) |>.take 20}"
  for (name, rhs) in remaining do
    sorted := sorted.push (.assign name rhs)
  return memories.toList ++ sorted.toList ++ registers.toList ++ others.toList

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
  | .binary .add a b => do
    let va ← evalConstExpr paramVals a
    let vb ← evalConstExpr paramVals b
    some (va + vb)
  | .binary .sub a b => do
    let va ← evalConstExpr paramVals a
    let vb ← evalConstExpr paramVals b
    -- Nat subtraction is saturating at 0, which is exactly what we want
    -- for bit-range bounds (negative widths are nonsensical anyway).
    some (va - vb)
  | .binary .mul a b => do
    let va ← evalConstExpr paramVals a
    let vb ← evalConstExpr paramVals b
    some (va * vb)
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
-- Post-pass: narrow the 32-bit all-ones mask that `lowerExpr` emits for
-- bitwise-NOT (`~x`).  When the operand `x` is a known port/wire/reg, we
-- can replace the 32-bit constant with one matching the operand's actual
-- width.  Without this pass, `~a + 1` with `a : [3:0]` (Test 37 of
-- `Tests/SVParser/ParserTest.lean`) returns 0 instead of 16 because the
-- upper 28 bits of `~a` are set and the +1 carry propagates through them.
--
-- The pass is a *strict refinement*: any expression shape it does not
-- recognise (or any operand whose width cannot be determined from the
-- existing `LowerEnv`) falls through unchanged, so the rest of the IR
-- corpus cannot regress.
--
-- We intentionally do NOT also narrow the matching reductAnd / logNot /
-- logAnd / logOr constants — they share the same 32-bit-constant family
-- (issue #41) but require narrowing both an XOR mask and a separate
-- equality comparator together to stay sound.  That is a follow-up PR.
-- ============================================================================

/-- Best-effort width inference for an IR `Expr` against the lowering
    environment.  Returns `none` when the operand's width can't be
    determined locally; the caller treats `none` as "leave the constant
    alone". -/
private def exprWidthForNarrow (env : LowerEnv) : Expr → Option Nat
  | .ref name =>
    match env.getWidth name with
    | some (hi, lo) => some (hi - lo + 1)
    | none =>
      -- `getWidth` can't distinguish "declared without a range" from
      -- "unknown name".  A range-less SV declaration IS a 1-bit scalar,
      -- and 1-bit operands are exactly where the un-narrowed 32-bit mask
      -- does the most damage (XiangShan: `countingEn ^ 32'hffffffff`
      -- makes every enclosing ternary condition 32-bit non-zero, so
      -- `~w_wen` reads as TRUE even when `w_wen` is 1).
      if env.portWidths.contains name || env.wireWidths.contains name
      then some 1 else none
  | .const _ w => some w
  | .slice _ hi lo => some (hi - lo + 1)
  | .concat args =>
    -- Sum of member widths (self-determined in Verilog).  Needed for the
    -- reduction-AND shape over a concat of slices, e.g. AgeDetector's
    -- `&{T[5:5], T[3:0]}` → `({…} ^ 32'hffffffff) == 32'd0`, which is
    -- constantly false unless the mask narrows to the concat's width.
    args.foldl (fun acc a =>
      match acc, exprWidthForNarrow env a with
      | some x, some y => some (x + y)
      | _, _ => none) (some 0)
  | .op op args =>
    -- Comparison/reduction-shaped results are 1-bit by construction.
    match op with
    | .eq | .lt_u | .lt_s | .le_u | .le_s | .gt_u | .gt_s | .ge_u | .ge_s => some 1
    | .and | .or | .xor | .not =>
      -- Bitwise ops: result width = max operand width (Verilog
      -- context-determined sizing).  Needed so `~(valid & issue)` on
      -- 1-bit wires narrows its all-ones mask too, not just `~ref`
      -- (XiangShan ICacheMshr.io_wfi_wfiSafe).  Recursion is safe:
      -- `narrowMaskConstants` rewrites innermost masks first.
      args.foldl (fun acc a =>
        match acc, exprWidthForNarrow env a with
        | some x, some y => some (max x y)
        | _, _ => none) (some 1)
    | .mux =>
      match args with
      | [_, t, e] =>
        match exprWidthForNarrow env t, exprWidthForNarrow env e with
        | some x, some y => some (max x y)
        | _, _ => none
      | _ => none
    | _ => none
  | _ => none

/-- Rewrite the `(x XOR <32-bit -1>)` shape emitted by `lowerExpr` for
    bitwise-NOT so the all-ones constant matches the inferred width of
    `x`.  Recurse structurally so the rewrite reaches nested
    sub-expressions. -/
private partial def narrowMaskConstants (env : LowerEnv) : Expr → Expr
  | .op .xor [a, .const (-1) 32] =>
    let a' := narrowMaskConstants env a
    match exprWidthForNarrow env a' with
    | some w => .op .xor [a', .const (-1) w]
    | none   => .op .xor [a', .const (-1) 32]
  | .op o args => .op o (args.map (narrowMaskConstants env))
  | .concat args => .concat (args.map (narrowMaskConstants env))
  | .slice e hi lo => .slice (narrowMaskConstants env e) hi lo
  | .sliceDim e hi lo => .sliceDim (narrowMaskConstants env e) hi lo
  | .index arr idx => .index (narrowMaskConstants env arr) (narrowMaskConstants env idx)
  | e => e

/-- Apply `narrowMaskConstants` to every `Expr` field stored in a `Stmt`. -/
private def narrowMaskStmt (env : LowerEnv) : Stmt → Stmt
  | .assign lhs rhs => .assign lhs (narrowMaskConstants env rhs)
  | .register output clk rst input init =>
    .register output clk rst (narrowMaskConstants env input) init
  | .memory name aw dw clk wa wd we ra rd cr ew er =>
    .memory name aw dw clk
      (narrowMaskConstants env wa)
      (narrowMaskConstants env wd)
      (narrowMaskConstants env we)
      (narrowMaskConstants env ra)
      rd cr
      -- extra ports get the same rewrite; dropping them here silently
      -- reduced a multi-port memory to port 0
      (ew.map fun (a, d, e) =>
        (narrowMaskConstants env a, narrowMaskConstants env d, narrowMaskConstants env e))
      (er.map fun (a, r) => (narrowMaskConstants env a, r))
  | .inst modName instName conns =>
    .inst modName instName
      (conns.map fun (p, e) => (p, narrowMaskConstants env e))

-- ============================================================================
-- Post-pass: promote unsigned relational ops (`<`, `<=`, `>`, `>=`) to
-- their signed counterparts when at least one operand is a reference to
-- a port declared with the SystemVerilog `signed` keyword.
--
-- `lowerExpr` always emits `.lt_u` / `.le_u` / `.gt_u` / `.ge_u` because
-- it can't see the surrounding `LowerEnv`.  Without this fix-up, a
-- comparison of two `signed [7:0]` ports is performed as unsigned and
-- e.g. `(-106) < 127` returns 0 (issue #43, Test 32).
-- ============================================================================

/-- Does this IR expression reach a signed port reference at its leaf
    operand position?  Conservative — only `.ref` chains and trivial
    slices propagate signedness; arithmetic mixes lose it (which
    matches the IR's own context-determined arithmetic semantics). -/
private partial def exprHasSignedLeaf (env : LowerEnv) : Expr → Bool
  | .ref name => env.isSignedRef name
  | .slice e _ _ => exprHasSignedLeaf env e
  | .sliceDim e _ _ => exprHasSignedLeaf env e
  | _ => false

/-- Rewrite each `lt_u`/`le_u`/`gt_u`/`ge_u` to the signed counterpart
    when either argument references a signed port. -/
private partial def promoteSignedComparisons (env : LowerEnv) : Expr → Expr
  | .op .lt_u [a, b] =>
    let a' := promoteSignedComparisons env a
    let b' := promoteSignedComparisons env b
    let op := if exprHasSignedLeaf env a' || exprHasSignedLeaf env b' then
              Sparkle.IR.AST.Operator.lt_s else Sparkle.IR.AST.Operator.lt_u
    .op op [a', b']
  | .op .le_u [a, b] =>
    let a' := promoteSignedComparisons env a
    let b' := promoteSignedComparisons env b
    let op := if exprHasSignedLeaf env a' || exprHasSignedLeaf env b' then
              Sparkle.IR.AST.Operator.le_s else Sparkle.IR.AST.Operator.le_u
    .op op [a', b']
  | .op .gt_u [a, b] =>
    let a' := promoteSignedComparisons env a
    let b' := promoteSignedComparisons env b
    let op := if exprHasSignedLeaf env a' || exprHasSignedLeaf env b' then
              Sparkle.IR.AST.Operator.gt_s else Sparkle.IR.AST.Operator.gt_u
    .op op [a', b']
  | .op .ge_u [a, b] =>
    let a' := promoteSignedComparisons env a
    let b' := promoteSignedComparisons env b
    let op := if exprHasSignedLeaf env a' || exprHasSignedLeaf env b' then
              Sparkle.IR.AST.Operator.ge_s else Sparkle.IR.AST.Operator.ge_u
    .op op [a', b']
  | .op o args => .op o (args.map (promoteSignedComparisons env))
  | .concat args => .concat (args.map (promoteSignedComparisons env))
  | .slice e hi lo => .slice (promoteSignedComparisons env e) hi lo
  | .sliceDim e hi lo => .sliceDim (promoteSignedComparisons env e) hi lo
  | .index arr idx =>
    .index (promoteSignedComparisons env arr) (promoteSignedComparisons env idx)
  | e => e

/-- Apply `promoteSignedComparisons` to every `Expr` stored in a `Stmt`. -/
private def promoteSignedStmt (env : LowerEnv) : Stmt → Stmt
  | .assign lhs rhs => .assign lhs (promoteSignedComparisons env rhs)
  | .register output clk rst input init =>
    .register output clk rst (promoteSignedComparisons env input) init
  | .memory name aw dw clk wa wd we ra rd cr ew er =>
    .memory name aw dw clk
      (promoteSignedComparisons env wa)
      (promoteSignedComparisons env wd)
      (promoteSignedComparisons env we)
      (promoteSignedComparisons env ra)
      rd cr
      (ew.map fun (a, d, e) =>
        (promoteSignedComparisons env a, promoteSignedComparisons env d,
         promoteSignedComparisons env e))
      (er.map fun (a, r) => (promoteSignedComparisons env a, r))
  | .inst modName instName conns =>
    .inst modName instName
      (conns.map fun (p, e) => (p, promoteSignedComparisons env e))

-- ============================================================================
-- Module lowering
-- ============================================================================

/-! ### Multi-dim packed arrays — flattened before lowering

`wire [3:0][1:0] g = {…}` becomes an 8-bit wire, and every `g[i]` becomes
the dynamic part-select `g[i*2 +: 2]` (which the existing lowering already
handles on both sides of assignments).  firtool uses these as case-mux
tables (`_GEN[state]`), so this runs before anything else sees the items. -/

private def pDimW (d : Nat × Nat) : Nat := d.1 - d.2 + 1

private partial def expandPackedExpr (tbl : List (String × Nat)) : SVExpr → SVExpr
  | .index (.ident n) i =>
    let i' := expandPackedExpr tbl i
    match tbl.find? (·.1 == n) with
    | some (_, ew) =>
      if ew == 1 then .index (.ident n) i'
      else .partSelectPlus (.ident n)
             (.binary .mul i' (.lit (.decimal none ew)))
             (.lit (.decimal none ew))
    | none => .index (.ident n) i'
  | .index a i => .index (expandPackedExpr tbl a) (expandPackedExpr tbl i)
  | .unary op a => .unary op (expandPackedExpr tbl a)
  | .binary op a b => .binary op (expandPackedExpr tbl a) (expandPackedExpr tbl b)
  | .ternary c t f =>
    .ternary (expandPackedExpr tbl c) (expandPackedExpr tbl t) (expandPackedExpr tbl f)
  | .slice e hi lo => .slice (expandPackedExpr tbl e) hi lo
  | .partSelectPlus e b w =>
    .partSelectPlus (expandPackedExpr tbl e) (expandPackedExpr tbl b) (expandPackedExpr tbl w)
  | .concat args => .concat (args.map (expandPackedExpr tbl))
  | .repeat_ c v => .repeat_ (expandPackedExpr tbl c) (expandPackedExpr tbl v)
  | .sizeCast w a => .sizeCast w (expandPackedExpr tbl a)
  | e => e

private partial def expandPackedStmt (tbl : List (String × Nat)) : SVStmt → SVStmt
  | .blockAssign l r => .blockAssign (expandPackedExpr tbl l) (expandPackedExpr tbl r)
  | .nonblockAssign l r => .nonblockAssign (expandPackedExpr tbl l) (expandPackedExpr tbl r)
  | .ifElse c t e =>
    .ifElse (expandPackedExpr tbl c) (t.map (expandPackedStmt tbl)) (e.map (expandPackedStmt tbl))
  | .caseStmt e arms dflt =>
    .caseStmt (expandPackedExpr tbl e)
      (arms.map fun (gs, ss) => (gs.map (expandPackedExpr tbl), ss.map (expandPackedStmt tbl)))
      (dflt.map (·.map (expandPackedStmt tbl)))
  | .forLoop i c st b =>
    .forLoop (expandPackedStmt tbl i) (expandPackedExpr tbl c)
      (expandPackedStmt tbl st) (b.map (expandPackedStmt tbl))
  | .assertStmt c => .assertStmt (expandPackedExpr tbl c)

private partial def expandPackedItem (tbl : List (String × Nat)) : SVModuleItem → SVModuleItem
  | .packedArrayDecl n dims init =>
    let total := dims.foldl (fun a d => a * pDimW d) 1
    .wireDecl n (some (total - 1, 0)) (init.map (expandPackedExpr tbl))
  | .wireDecl n w init => .wireDecl n w (init.map (expandPackedExpr tbl))
  | .contAssign l r => .contAssign (expandPackedExpr tbl l) (expandPackedExpr tbl r)
  | .alwaysBlock sens body => .alwaysBlock sens (body.map (expandPackedStmt tbl))
  | .generateBlock c b e =>
    .generateBlock (expandPackedExpr tbl c)
      (b.map (expandPackedItem tbl)) (e.map (expandPackedItem tbl))
  | .instantiation m i conns po =>
    .instantiation m i (conns.map fun (p, e) => (p, expandPackedExpr tbl e)) po
  | .taskDecl n body => .taskDecl n (body.map (expandPackedStmt tbl))
  | it => it

private def preprocessPackedItems (items : List SVModuleItem) : List SVModuleItem :=
  let tbl := items.filterMap fun it => match it with
    | .packedArrayDecl n dims _ =>
      some (n, (dims.drop 1).foldl (fun a d => a * pDimW d) 1)
    | _ => none
  if tbl.isEmpty then items else items.map (expandPackedItem tbl)

/-- Names procedurally assigned by a statement (recursively through
    if/case/for) — see the register-initializer note in `lowerModule`. -/
private partial def collectProcTargets
    (acc : Std.HashMap String Bool) (st : SVStmt) :
    Std.HashMap String Bool :=
  match st with
  | .nonblockAssign lhs _ | .blockAssign lhs _ =>
    (match exprToName lhs with
     | some n => acc.insert n true
     | none => acc)
  | .ifElse _ t e => e.foldl collectProcTargets (t.foldl collectProcTargets acc)
  | .caseStmt _ arms dflt =>
    let acc1 := arms.foldl (fun a (p : List SVExpr × List SVStmt) =>
      p.2.foldl collectProcTargets a) acc
    (dflt.getD []).foldl collectProcTargets acc1
  | .forLoop _ _ _ b => b.foldl collectProcTargets acc
  | _ => acc

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
  -- Resolve symbolic port widths (e.g. `[W-1:0]`) against the resolved
  -- parameter values.  Without this, the parser's `bitRange` falls back
  -- to a 32-bit placeholder for any identifier-bearing bound, which
  -- breaks parameters that were intended to size ports (issue #44).
  let resolvedPorts := svMod.ports.map fun p =>
    match p.widthExpr with
    | none => p  -- already concrete
    | some (hiE, loE) =>
      match evalConstExpr paramVals hiE, evalConstExpr paramVals loE with
      | some hiV, some loV => { p with width := some (hiV, loV) }
      | _, _ => p  -- couldn't resolve; keep the parser's fallback
  let svMod := { svMod with items := preprocessPackedItems expandedItems, params := svParams, ports := resolvedPorts }

  -- Build environment
  let mut env := LowerEnv.empty
  for p in svMod.ports do
    env := { env with portWidths :=
      if env.portWidths.contains p.name then env.portWidths
      else env.portWidths.insert p.name p.width }
    if p.isSigned then
      env := { env with signedNames := env.signedNames.insert p.name true }
  for item in svMod.items do
    match item with
    | .wireDecl name width _ =>
      env := { env with wireWidths :=
        if env.wireWidths.contains name then env.wireWidths
        else env.wireWidths.insert name width }
    | .regDecl name width _ =>
      env := { env with
        wireWidths :=
          if env.wireWidths.contains name then env.wireWidths
          else env.wireWidths.insert name width,
        regNames := env.regNames.insert name true }
    | _ => pure ()

  -- With the environment complete, resolve reduction-XOR widths that are
  -- invisible statically (bare idents inside the parity concat).
  let svMod := { svMod with items := svMod.items.map (annotateRXItem env) }

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
  let portNameSet : Std.HashMap String Bool :=
    allPortNames.foldl (fun h n => h.insert n true) {}

  -- Build wires list (from wire and reg declarations)
  let mut wires : Array Port := #[]
  let mut wireSet : Std.HashMap String Bool := {}
  for item in svMod.items do
    match item with
    | .wireDecl name width _ => wires := wires.push { name, ty := widthToHWType width }; wireSet := wireSet.insert name true
    | .regDecl name width arraySize =>
      match arraySize with
      | some _ => pure ()  -- Array regs handled by Stmt.memory (not wires)
      | none => wires := wires.push { name, ty := widthToHWType width }; wireSet := wireSet.insert name true
    | .integerDecl name => wires := wires.push { name, ty := .bitVector 32 }; wireSet := wireSet.insert name true
    | _ => pure ()

  -- Add parameters as constant wires (track names to avoid duplicates)
  let mut paramNames : List String := []
  for p in svMod.params do
    let ty := widthToHWType p.width
    if !(paramNames.any (· == p.name)) then
      wires := wires.push { name := p.name, ty }; wireSet := wireSet.insert p.name true
      paramNames := paramNames ++ [p.name]
  for item in svMod.items do
    match item with
    | .paramDecl param =>
      let ty := widthToHWType param.width
      if !(paramNames.any (· == param.name)) then
        wires := wires.push { name := param.name, ty }; wireSet := wireSet.insert param.name true
        paramNames := paramNames ++ [param.name]
    | _ => pure ()

  -- Names procedurally assigned inside ANY always block: a
  -- `logic name = init;` for such a name is a REGISTER INITIALIZER
  -- (SystemVerilog variable init), not a continuous assign — emitting
  -- `assign name = init` created a competing constant driver, the
  -- register-vs-assign dedup kept the assign, and the register
  -- CONSTANT-FOLDED away.  firtool never writes this shape (it uses
  -- RANDOMIZE initial blocks), so only re-parsing Sparkle's OWN emitted
  -- registers hit it — silently, including in the roundtrip metric.
  let alwaysTargets : Std.HashMap String Bool := Id.run do
    let mut acc : Std.HashMap String Bool := {}
    for it in svMod.items do
      match it with
      | .alwaysBlock _ stmts => acc := stmts.foldl collectProcTargets acc
      | _ => pure ()
    return acc

  -- Build body statements
  let mut body : Array Stmt := #[]
  -- Continuous assigns that write only PART of a vector, collected so
  -- they can be merged into one driver per target (see `lhsSelectBounds`).
  let mut partialAssigns : Array (String × Nat × Nat × Expr) := #[]
  -- All always @* blocks now use MUX mode (SSA handles loop dependencies)

  -- Emit parameter values as constant assigns (with overrides applied)
  let paramWidth (w : Option (Nat × Nat)) : Nat :=
    match w with | some (hi, lo) => hi - lo + 1 | none => 32
  for p in svMod.params do
    let val := match paramVals.find? fun (n, _) => n == p.name with
      | some (_, v) => .const (Int.ofNat v) (paramWidth p.width)
      | none => lowerExpr p.value
    body := body.push (.assign p.name val)
  for item in svMod.items do
    match item with
    | .paramDecl param =>
      let val := match paramVals.find? fun (n, _) => n == param.name with
        | some (_, v) => .const (Int.ofNat v) (paramWidth param.width)
        | none => lowerExpr param.value
      body := body.push (.assign param.name val)
    | _ => pure ()

  for item in svMod.items do
    match item with
    | .contAssign lhs rhs =>
      -- Memory-array reads (`assign rd = Memory[addr]`) are handled by
      -- the array-reg arm (Stmt.memory read port / extra `.index`
      -- assigns).  Lowering them here TOO emitted a second, bogus
      -- driver (`(Memory >> addr) & 1`) — iverilog: "multiple drivers".
      let isMemRead := match rhs with
        | .index (.ident arrN) _ => arrayRegNames.any (· == arrN)
        | _ => false
      if isMemRead then pure ()
      else
      match exprToName lhs with
      | some name =>
        -- A bit/part-select LHS (`assign gnt[0] = …`) carries a POSITION
        -- that `exprToName` discards.  Several such statements to one
        -- vector are legal Verilog (XiangShan's arbiters drive `gnt` one
        -- bit per statement) but collapsed to competing `assign gnt = …`
        -- drivers: the emitted Verilog was rejected for multiple drivers
        -- and, worse, the IR kept only the last write.  Record the bounds
        -- so the partial writes can be merged after the item loop.
        match lhsSelectBounds lhs with
        | some (hi, lo) =>
          partialAssigns := partialAssigns.push (name, hi, lo, lowerExpr rhs)
        | none => body := body.push (.assign name (lowerExpr rhs))
      | none =>
        -- Concat-LHS continuous assign: assign {a, b, c} = expr;
        -- Decompose into individual assigns for each target variable
        let assigns := decomposeMultiConcatLhs lhs rhs
        if assigns.isEmpty then
          -- Try single-variable concat (all elements same variable)
          match lowerConcatLhsAssign lhs rhs with
          | some (name, value) => body := body.push (.assign name value)
          | none => throw s!"continuous assign LHS not supported: {repr lhs}"
        else
          for (name, value) in assigns do
            body := body.push (.assign name value)
            if !((wireSet.contains name || portNameSet.contains name)) then
              wires := wires.push { name, ty := env.getHWType name }; wireSet := wireSet.insert name true
    | .alwaysBlock (.posedge clock) stmts =>
      -- Sequential: extract all register names, then build mux expression per register
      -- Detect reset pattern: find first if/else that looks like a reset check
      -- PicoRV32 has flat assigns before the reset check, so we scan for it
      let mut resetName := "rst"
      let mut resetKind : Sparkle.IR.Type.ResetKind := .asynchronous
      let mut initMap : List (String × Nat) := []
      let resetCheck := stmts.findSome? fun s => match s with
        | .ifElse cond thenB elseB => detectReset cond thenB elseB
        | _ => none
      match resetCheck with
      | some (resetSig, isActiveHigh, initBranch, _dataBranch) =>
        resetName := if isActiveHigh then resetSig else s!"_rst_{resetSig}_inv"
        if !isActiveHigh then
          wires := wires.push { name := resetName, ty := .bit }; wireSet := wireSet.insert resetName true
          body := body.push (.assign resetName (.op .not [.ref resetSig]))
        initMap := initBranch.filterMap fun s => match s with
          | .nonblockAssign lhs rhs =>
            match exprToName lhs with
            | some n => match evalConstExpr paramVals rhs with
              | some v => some (n, v)
              | none => none
            | none => none
          | _ => none
      | none =>
        -- No reset pattern in this block (XiangShan `Hstateen*`: plain
        -- `always @(posedge clock)` with enable-only updates).  The old
        -- default referenced a phantom `rst` wire that exists in no such
        -- module — the re-emitted Verilog then fails elaboration
        -- ("Unable to bind wire/reg/memory `rst'").  Drive a shared
        -- constant-0 reset instead and mark the register synchronous so
        -- the sensitivity list stays clock-only.
        resetName := "_no_rst"
        resetKind := .synchronous
        if !((wireSet.contains "_no_rst" || portNameSet.contains "_no_rst")) then
          wires := wires.push { name := "_no_rst", ty := .bit }; wireSet := wireSet.insert "_no_rst" true
          body := body.push (.assign "_no_rst" (.const 0 1))

      -- Extract blocking assigns as combinational intermediates (from full always body)
      -- Array regs are Stmt.memory, not combinational intermediates —
      -- without this filter a nonblocking `Memory[addr] <= x` write made
      -- `Memory` a phantom 32-bit wire + assign (duplicate declaration
      -- in the emitted Verilog, dt_352x1).
      let blockingNames := (collectBlockNamesTop stmts).eraseDups.filter
        fun n => !arrayRegNames.any (· == n)
      let preBlocking := collectGuardedBlock stmts
      -- Bit-range blocking writes (`q[35] = d`) are a read-modify-write,
      -- which `stmtsToMuxExprBlocking` cannot express — it builds a
      -- WHOLE-signal value.  Collect them here and scatter each piece to
      -- its position, at the TARGET's declared width so nothing is
      -- shifted out (the same discipline as the combinational path's
      -- `partialAssigns` merge).
      let bitWrites : List (String × Nat × Nat × SVExpr) :=
        stmts.filterMap fun st => match st with
          | .blockAssign lhs rhs =>
            match lhsSelectBounds lhs, exprToName lhs with
            | some (hi, lo), some n => some (n, hi, lo, rhs)
            | _, _ => none
          | _ => none
      let bitTargets := (bitWrites.map (fun p => p.1)).eraseDups
      for sigName in blockingNames do
        if bitTargets.contains sigName then
          -- read-modify-write: start from the signal, overwrite each
          -- written range
          let tgtW := match env.getWidth sigName with
            | some (hi, lo) => hi - lo + 1
            | none => 32
          let parts := bitWrites.filter (fun p => p.1 == sigName)
          -- The BASE is whatever the signal holds before the bit writes:
          -- a preceding whole-signal blocking write if there is one
          -- (`q = init; q[5] = d;`), else the signal's own value.
          let base :=
            match stmts.findSome? (fun st => match st with
              | .blockAssign lhs rhs =>
                match lhsSelectBounds lhs, exprToName lhs with
                | none, some n => if n == sigName then some rhs else none
                | _, _ => none
              | _ => none) with
            | some rhs => lowerExpr rhs
            | none => Expr.ref sigName
          let merged := parts.foldl (fun acc (_, hi, lo, rhs) =>
            let w := hi - lo + 1
            let m : Nat := ((1 <<< w) - 1) <<< lo
            let notM : Int := Int.ofNat (((1 <<< tgtW) - 1) ^^^ m)
            let piece := Expr.slice (.concat [.const 0 tgtW,
              Expr.slice (lowerExpr rhs) (w - 1) 0]) (tgtW - 1) 0
            let shifted := if lo == 0 then piece
              else Expr.op .shl [piece, Expr.const (Int.ofNat lo) tgtW]
            Expr.op .or [Expr.op .and [acc, Expr.const notM tgtW],
                         Expr.op .and [shifted, Expr.const (Int.ofNat m) tgtW]]
          ) base
          body := body.push (.assign sigName merged)
        else
          let expr := stmtsToMuxExprBlocking sigName stmts (some preBlocking)
          body := body.push (.assign sigName expr)
        if !((wireSet.contains sigName || portNameSet.contains sigName)) then
          wires := wires.push { name := sigName, ty := .bitVector 32 }; wireSet := wireSet.insert sigName true  -- default 32-bit

      -- Collect all register names (exclude array regs handled by Stmt.memory)
      -- A sync-read target (`rd <= mem[ra]` with mem an array reg) is a
      -- Stmt.memory read port, not a scalar register: lowering it as a
      -- register made a garbage bit-select of the ARRAY the register
      -- input (`(Mem >> ra) & 1`) plus a duplicate driver on rd — found
      -- by the roundtrip-proof probe (sync-read memories broke on
      -- self-reparse).  Exclude a name only when ALL its nonblocking
      -- assigns in this block are array sync reads.
      let nbRaw := collectNBRaw stmts
      let syncReadTargets := (stmts.filterMap fun st => match st with
        | .nonblockAssign (.ident rd) (.index (.ident arrN) _) =>
          if arrayRegNames.any (· == arrN) then some rd else none
        | _ => none).eraseDups.filter fun rd =>
          nbRaw.all fun (t, rhs) =>
            t != rd ||
              (match rhs with
               | .index (.ident arrN) _ => arrayRegNames.any (· == arrN)
               | _ => false)
      let regNames := (collectAllRegNames stmts).eraseDups.filter
        fun n => !arrayRegNames.any (· == n) && !syncReadTargets.any (· == n)
      -- Collect the guarded assigns ONCE for the whole block:
      -- `stmtsToMuxExpr` re-ran `collectGuardedNB` (a full lowering of
      -- every RHS in the block) once PER REGISTER — O(regs × block), the
      -- dominant cost on XiangShan's RenameTable/Rob (323+ registers in
      -- one always block).
      let allGuarded := collectGuardedNB stmts
      for regName in regNames do
        let hwTy := env.getHWType regName
        let initVal := match initMap.find? (·.1 == regName) with
          | some (_, v) => v
          | none => 0
        let dataExpr := stripResetMux resetName initVal
          (guardedToMux (allGuarded.filter (·.target == regName)) (.ref regName))
        body := body.push (.register regName clock (resetName, resetKind) dataExpr initVal)
        if !((wireSet.contains regName || portNameSet.contains regName)) then
          wires := wires.push { name := regName, ty := hwTy }; wireSet := wireSet.insert regName true

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
          body := body.push (.assign sigName (.ref latestWire))
          if !(wireSet.contains sigName || portNameSet.contains sigName) then
            let sigTy := env.getHWType sigName
            wires := wires.push { name := sigName, ty := sigTy }; wireSet := wireSet.insert sigName true
    | .wireDecl name _ (some initExpr) =>
      -- `wire x = expr;` → assign — UNLESS x is procedurally assigned in
      -- an always block, in which case the initializer is register init
      -- (already carried by the reset arm) and a continuous assign would
      -- be a competing driver (see `alwaysTargets` above).
      if !(alwaysTargets.contains name) then
        body := body.push (.assign name (lowerExpr initExpr))
    | .regDecl name width (some arraySize) =>
      -- Array reg → Stmt.memory for JIT memory access
      -- Do NOT add to wires list — Stmt.memory creates the class member.
      let dataWidth := widthToBits width
      let addrWidth := Nat.log2 arraySize + (if Nat.isPowerOfTwo arraySize then 0 else 1)
      -- Extract array writes from always blocks
      let mut writeAddr : Expr := .const 0 addrWidth
      let mut writeData : Expr := .const 0 dataWidth
      let mut writeEnable : Expr := .const 0 1
      let mut extraWrites : List (Expr × Expr × Expr) := []
      let mut extraReads : List (Expr × String) := []
      let mut memClock : String := "clk"
      for prevItem in svMod.items do
        match prevItem with
        | .alwaysBlock (.posedge blkClk) stmts =>
          -- Try full-word writes first: arr[idx] <= data
          let arrayWrites := collectArrayWrites name stmts
          if !arrayWrites.isEmpty then
            -- The memory is clocked by the block that WRITES it (firtool
            -- SRAM macros use `W0_clk`/`RW0_clk`, never a wire named
            -- `clk` — the old hardcoded name failed elaboration).
            memClock := blkClk
            -- Compose MULTIPLE guarded writes as a priority mux (later
            -- statements win, mirroring non-blocking semantics); the old
            -- loop simply kept the LAST write and dropped the others.
            -- Each guarded write becomes its OWN write port.  Folding
            -- them into a priority mux (the previous behaviour) is only
            -- correct when at most one guard is ever true: XiangShan's
            -- dt_352x1 fires several of its eight write ports in the same
            -- cycle, and the folded form then dropped every write but the
            -- highest-priority one.  `Stmt.memory` carries the extra
            -- ports, and both backends emit one guarded write each in
            -- port order (last-port-wins on an address collision, the
            -- Verilog `always_ff` rule).
            for (idx, data, cond) in arrayWrites do
              let c : Expr := match cond with
                | some c => lowerMemPayload name c
                | none => .const 1 1
              let a := lowerMemPayload name idx
              let d := lowerMemPayload name data
              if writeEnable == Expr.const 0 1 then
                writeAddr := a; writeData := d; writeEnable := c
              else
                extraWrites := extraWrites ++ [(a, d, c)]
          else
            -- Try byte-lane writes: if (wstrb[n]) arr[addr][hi:lo] <= data[hi:lo]
            -- (also matches firtool's `[base +: w]` mask-chunk form)
            let byteLanes := collectByteLaneWrites name stmts
            match byteLanes with
            | lane0 :: _ =>
              memClock := blkClk
              let addr := lowerExpr lane0.addr
              writeAddr := addr
              let rmw := buildByteStrobeWrite name addr byteLanes dataWidth
              -- A masked read-modify-write on a WIDE memory is a wide OP
              -- (`row & ~mask | data & mask`).  Nested in the memory
              -- statement's write-data slot it has no valid C rendering
              -- (`array & array`); as its own wire it goes through the
              -- backends' wide-ASSIGN paths, which materialise operands
              -- word by word.  Narrow memories keep the inline form.
              if dataWidth > 64 then
                let wdWire := s!"{name}_wdata_rmw"
                body := body.push (.assign wdWire rmw)
                if !(wireSet.contains wdWire || portNameSet.contains wdWire) then
                  wires := wires.push { name := wdWire, ty := widthToHWType width }
                  wireSet := wireSet.insert wdWire true
                writeData := .ref wdWire
              else
                writeData := rmw
              -- Enable if any strobe bit is set
              let enableExpr := byteLanes.foldl (fun acc lane =>
                let c := lowerExpr lane.cond
                if acc == Expr.const 0 1 then c else Expr.op .or [acc, c]
              ) (Expr.const 0 1)
              writeEnable := enableExpr
            | [] => pure ()
        | _ => pure ()
      -- Extract read ports.  The first read claims `Stmt.memory`'s
      -- dedicated read fields; the rest become genuine EXTRA read ports
      -- (XiangShan's dt_352x1 has eight).  The claimed contAssign items
      -- are excluded from normal lowering below (they used to also lower
      -- as ordinary assigns → duplicate drivers).
      let mut readAddr : Expr := .const 0 addrWidth
      let mut readDataName := s!"{name}_rdata"
      let mut comboRead := true
      let mut claimed := false
      for prevItem in svMod.items do
        match prevItem with
        | .contAssign lhs (.index (.ident arrN) idx) =>
          if arrN == name then
            match exprToName lhs with
            | some rdName =>
              if !claimed then
                readDataName := rdName; readAddr := lowerExpr idx; claimed := true
              else
                extraReads := extraReads ++ [(lowerExpr idx, rdName)]
            | none => pure ()
        | .alwaysBlock (.posedge _) innerStmts =>
          for s in innerStmts do
            match s with
            | .nonblockAssign (.ident rdName) (.index (.ident arrN) idx) =>
              -- Sync reads: first claims the dedicated fields; the rest
              -- become extra read ports, symmetric with the combo scan
              -- (they used to be silently dropped).
              if arrN == name then
                if !claimed then
                  readDataName := rdName; readAddr := lowerExpr idx
                  comboRead := false; claimed := true
                else
                  extraReads := extraReads ++ [(lowerExpr idx, rdName)]
            | _ => pure ()
        | _ => pure ()
      body := body.push (.memory name addrWidth dataWidth memClock
        writeAddr writeData writeEnable
        readAddr readDataName comboRead extraWrites extraReads)
      for rd in readDataName :: extraReads.map (·.2) do
        if !(wireSet.contains rd || portNameSet.contains rd) then
          wires := wires.push { name := rd, ty := widthToHWType width }
          wireSet := wireSet.insert rd true
    | .instantiation modName instName conns _paramOvr =>
      -- Module instantiation → Stmt.inst (parameter overrides resolved at flatten time)
      let irConns := conns.map fun (portName, expr) => (portName, lowerExpr expr)
      body := body.push (.inst modName instName irConns)
    | _ => pure ()

  -- Deduplicate wires (hash-set membership + Array push: the List
  -- version was O(wires²) — 15% of Rob's lower phase)
  let mut dedupWiresA : Array Port := #[]
  let mut seenWireNames : Std.HashMap String Bool := {}
  let portNames2 : Std.HashMap String Bool :=
    (inputs.map (·.name) ++ outputs.map (·.name)).foldl
      (fun h n => h.insert n true) {}
  for w in wires do
    if !(seenWireNames.contains w.name) && !(portNames2.contains w.name) then
      dedupWiresA := dedupWiresA.push w
      seenWireNames := seenWireNames.insert w.name true
  let mut dedupWires := dedupWiresA.toList

  -- Deduplicate registers and handle output reg ports
  let mut dedupBody : List Stmt := []
  let mut seenRegNames : Std.HashMap String Bool := {}
  let outputNames : Std.HashMap String Bool :=
    (outputs.map (·.name)).foldl (fun h n => h.insert n true) {}
  -- (dead `exprDepthSimple`/`regDepthMap`/`bestDepth` removed: they were
  -- never read, yet walked every register's full mux expression — pure
  -- overhead on Rob-scale modules)

  -- For registers assigned in multiple always blocks, keep the one
  -- with deeper mux expression (more logic). This handles the PicoRV32
  -- pattern where the decode block sets a flag and the execution block clears it.
  -- Process in FORWARD order — first occurrence wins.
  -- For PicoRV32, the decode block (always[9]) comes before the execution
  -- block (always[17]). The decode block sets flags; the execution block clears them.
  -- We keep the decode block's version which has the meaningful logic.
  for stmt in body do
    match stmt with
    | .register name clk rst input init =>
      if !(seenRegNames.contains name) then
        -- For output reg: rename the register to _reg_name, add assign output = _reg_name
        if outputNames.contains name then
          let regName := s!"_reg_{name}"
          dedupBody := [.assign name (.ref regName), .register regName clk rst input init] ++ dedupBody
          seenRegNames := seenRegNames.insert name true
          -- Add the internal register wire
          if !(dedupWires.any (·.name == regName)) then
            let hwTy := env.getHWType name
            dedupWires := dedupWires ++ [{ name := regName, ty := hwTy }]
        else
          dedupBody := [stmt] ++ dedupBody
          seenRegNames := seenRegNames.insert name true
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

  -- Refinement passes (strictly additive — only rewrite shapes we
  -- explicitly recognise, leave everything else alone):
  --   1. narrowMaskStmt:        narrow `lowerExpr`'s 32-bit `~x` mask
  --                             to the operand's actual width (Test 37,
  --                             plus incidentally fixes issue #41 /
  --                             Test 30).
  --   2. promoteSignedStmt:     rewrite `lt_u`/`le_u`/`gt_u`/`ge_u` to
  --                             their `_s` counterparts when either
  --                             arg references a `signed` port
  --                             (issue #43 / Test 32).
  -- Merge the part-select continuous assigns: one driver per target,
  -- built as an OR of each written slice shifted into place.  Emitting
  -- them as separate `assign name = …` statements produced competing
  -- full-vector drivers (iverilog rejects it) and kept only the last.
  let mut mergedBody : List Stmt := dedupBody
  if !partialAssigns.isEmpty then
    let targets := partialAssigns.foldl (fun (acc : List String) (n, _, _, _) =>
      if acc.contains n then acc else acc ++ [n]) []
    for tgt in targets do
      let parts := partialAssigns.toList.filter (fun (n, _, _, _) => n == tgt)
      -- Widest bit touched decides the shift widths; a target whose other
      -- bits are driven elsewhere is not our concern (Verilog would call
      -- that multiple drivers too).
      -- Build at the TARGET's declared width.  The pieces are narrow
      -- slices, so a shift amount declared 32 made the OR-chain 32 bits
      -- wide (`widthOf` of a shift is the max of its operands): a write
      -- to bit 35 of a 40-bit reg was shifted straight out and lost.
      -- Widening each piece to the target width first pins the whole
      -- chain there, and the amount's own width is irrelevant since
      -- Verilog treats a shift count as self-determined.
      let tgtW := match env.getWidth tgt with
        | some (hi, lo) => hi - lo + 1
        | none => 32
      let terms := parts.map fun (_, hi, lo, rhs) =>
        let w := hi - lo + 1
        -- zero-extend the piece to the target width before shifting
        let bits := Expr.slice (.concat [.const 0 tgtW,
          Expr.slice rhs (w - 1) 0]) (tgtW - 1) 0
        if lo == 0 then bits
        else Expr.op .shl [bits, Expr.const (Int.ofNat lo) tgtW]
      let merged := match terms with
        | [] => Expr.const 0 tgtW
        | t :: rest => rest.foldl (fun acc t' => Expr.op .or [acc, t']) t
      mergedBody := mergedBody ++ [.assign tgt merged]
  let narrowedBody := mergedBody.map (narrowMaskStmt env)
  let promotedBody := narrowedBody.map (promoteSignedStmt env)
  pure {
    name := svMod.name
    inputs := inputs
    outputs := outputs
    wires := dedupWires
    body := topoSortBody promotedBody
    assertions := assertions
    isPrimitive := false
  }

/-- Prefix all wire/register names in an expression -/
partial def prefixExprNames (pfx : String) (nameSet : List String) : Expr → Expr
  | .ref name => if nameSet.any (· == name) then .ref s!"{pfx}_{name}" else .ref name
  | .op o args => .op o (args.map (prefixExprNames pfx nameSet))
  | .concat args => .concat (args.map (prefixExprNames pfx nameSet))
  | .slice e hi lo => .slice (prefixExprNames pfx nameSet e) hi lo
  | .sliceDim e hi lo => .sliceDim (prefixExprNames pfx nameSet e) hi lo
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
            | .memory n _ _ _ _ _ _ _ _ _ .. => some n | _ => none
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
                let (rstName, rstKind) := rst
                .register s!"{instName}_{name}" s!"{instName}_{clk}"
                  (s!"{instName}_{rstName}", rstKind)
                  (prefixExprNames instName subNames input) init
              | .inst subModName subInstName subConns =>
                -- Keep nested .inst with prefixed names — will be flattened in next iteration
                .inst subModName s!"{instName}_{subInstName}"
                  (subConns.map fun (pn, e) => (pn, prefixExprNames instName subNames e))
              | .memory name aw dw clk wa wd we ra rd combo ew er =>
                .memory s!"{instName}_{name}" aw dw s!"{instName}_{clk}"
                  (prefixExprNames instName subNames wa)
                  (prefixExprNames instName subNames wd)
                  (prefixExprNames instName subNames we)
                  (prefixExprNames instName subNames ra)
                  s!"{instName}_{rd}" combo
                  (ew.map fun (a, d, e) =>
                    (prefixExprNames instName subNames a,
                     prefixExprNames instName subNames d,
                     prefixExprNames instName subNames e))
                  (er.map fun (a, r) =>
                    (prefixExprNames instName subNames a, s!"{instName}_{r}"))
            flatBody := flatBody ++ [prefixed]
      | other => flatBody := flatBody ++ [other]

    -- Prefix internal wire names with _gen_ to prevent CppSim local shadowing.
    -- Exclude: input/output port names, register names, memory names.
    let portNames := top.inputs.map (·.name) ++ top.outputs.map (·.name)
    let regNames := flatBody.filterMap fun s => match s with
      | .register n _ _ _ _ => some n | _ => none
    let memNames := flatBody.filterMap fun s => match s with
      | .memory n _ _ _ _ _ _ _ _ _ .. => some n | _ => none
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
      | .memory n aw dw clk wa wd we ra rd combo ew er =>
        .memory n aw dw clk (genExpr wa) (genExpr wd) (genExpr we) (genExpr ra) rd combo
          (ew.map fun (a, d, e) => (genExpr a, genExpr d, genExpr e))
          (er.map fun (a, r) => (genExpr a, r))

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
      | .sliceDim e hi lo => .sliceDim (genExprRefs wireNames e) hi lo
      | .index a i => .index (genExprRefs wireNames a) (genExprRefs wireNames i)
      | e => e

/-- Lower a full SV design to Sparkle IR -/
def lowerDesign (svDesign : SVDesign) : Except String Design := do
  let mut modules : List Module := []
  for m in svDesign.modules do
    let lowered ← lowerModule m
    modules := modules ++ [lowered]
  -- Pick the top module: prefer the module that is NOT instantiated by
  -- any other (so source order doesn't matter — a designer can declare
  -- sub-modules either before or after the top).  Fall back to the
  -- first module when every module is instantiated (e.g. mutual
  -- instantiation, which Sparkle doesn't really support anyway).
  --
  -- This also avoids issue #42, where putting `module inc` before
  -- `module bug2_chained_inst` made the flattener treat `inc` as the
  -- top and silently drop the chained-instance design.
  let instantiated : List String := modules.flatMap fun m =>
    m.body.filterMap fun s => match s with
      | .inst modName _ _ => some modName
      | _ => none
  let topName :=
    (modules.find? fun m => !instantiated.contains m.name) |>.map (·.name)
      |>.getD (modules.head?.map (·.name) |>.getD "top")
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

/-- Generic reachability DCE: remove wires/registers NOT reachable from
    output ports. BFS through assign and register dependencies to find all
    reachable signals. Eliminates debug/trace signals automatically without
    hardcoding any signal names. -/
def reachabilityDCE (design : Design) : Design :=
  { design with modules := design.modules.map fun m =>
    if m.body.isEmpty then m else Id.run do
      let assignMap := m.body.foldl (fun (acc : Std.HashMap String (List Expr)) s =>
        match s with
        | .assign lhs rhs => acc.insert lhs ((acc.getD lhs []) ++ [rhs])
        | _ => acc) {}
      let regMap := m.body.foldl (fun (acc : Std.HashMap String Expr) s =>
        match s with | .register output _ _ input _ => acc.insert output input | _ => acc) {}
      let memMap := m.body.foldl (fun (acc : Std.HashMap String (List Expr)) s =>
        match s with
        | .memory _ _ _ _ wa wd we ra rd _ .. => acc.insert rd [wa, wd, we, ra]
        | _ => acc) {}
      let instExprs := m.body.foldl (fun (acc : List Expr) s =>
        match s with
        | .inst _ _ conns => acc ++ conns.map (·.2)
        | _ => acc) []
      let mut reached : Std.HashMap String Bool := {}
      let mut frontier : List String := m.outputs.map (·.name)
      -- All registers are reachable roots. Registers hold state and may
      -- indirectly affect outputs through multi-cycle FSM behavior.
      -- Only combinational wires (assigns) are candidates for DCE.
      -- The register's RESET is a use too: it lives in a String field
      -- (not an Expr), so `countExprUses` never sees it — without this
      -- root, synthesized reset wires (`_no_rst`, `_rst_<sig>_inv`)
      -- lose their driving assign and the emitted Verilog fails
      -- elaboration ("Unable to bind wire/reg/memory").
      for s in m.body do
        match s with
        | .register output clkName (rstName, _) _ _ =>
          -- The CLOCK is String-typed like the reset: a derived clock
          -- (`clock_falling = ~clock`, JTAG's negedge domain) must seed
          -- reachability or its driving assign is pruned, leaving
          -- `always_ff @(posedge clock_falling)` unbound.
          frontier := frontier ++ [output, rstName, clkName]
        | _ => pure ()
      for s in m.body do
        match s with
        | .memory _ _ _ _ wa wd we ra rd _ .. =>
          frontier := frontier ++ [rd]
          for e in [wa, wd, we, ra] do
            frontier := frontier ++ (Sparkle.IR.Optimize.countExprUses e {} |>.toList.map (·.1))
        | _ => pure ()
      for expr in instExprs do
        frontier := frontier ++ (Sparkle.IR.Optimize.countExprUses expr {} |>.toList.map (·.1))
      for r in frontier do reached := reached.insert r true
      let mut iters : Nat := 0
      while !frontier.isEmpty && iters < 1000 do
        let mut next : List String := []
        for name in frontier do
          match assignMap.get? name with
          | some exprs =>
            for expr in exprs do
              for r in (Sparkle.IR.Optimize.countExprUses expr {} |>.toList.map (·.1)) do
                if !reached.contains r then
                  reached := reached.insert r true
                  next := next ++ [r]
          | none => pure ()
          match regMap.get? name with
          | some input =>
            for r in (Sparkle.IR.Optimize.countExprUses input {} |>.toList.map (·.1)) do
              if !reached.contains r then
                reached := reached.insert r true
                next := next ++ [r]
          | none => pure ()
          match memMap.get? name with
          | some exprs =>
            for expr in exprs do
              for r in (Sparkle.IR.Optimize.countExprUses expr {} |>.toList.map (·.1)) do
                if !reached.contains r then
                  reached := reached.insert r true
                  next := next ++ [r]
          | none => pure ()
        frontier := next
        iters := iters + 1
      let reachSet := reached
      { m with
        body := m.body.filter fun s => match s with
          | .assign lhs _ => reachSet.contains lhs
          | .register output _ _ _ _ => reachSet.contains output
          | _ => true
        wires := m.wires.filter fun w => reachSet.contains w.name } }

/-- Re-declare any name the body still references but nothing declares.

    Runs LAST, after `Optimize.optimizeDesign`, because both that pass and
    `reachabilityDCE` can leave a reference dangling and either could undo a
    repair applied earlier:

    * a `.memory` write is never pruned, so its address/data operands stay
      referenced after the wires feeding them are gone (`latched_rd`,
      `next_pc`);
    * an `output reg` written only inside a disabled branch — PicoRV32 gates
      `eoi`, `mem_addr`, `trace_data`, … on `ENABLE_IRQ`, 0 by default — yields
      no `.register`, yet `lowerModule`'s output-reg rename still emits
      `assign eoi = _reg_eoi`, and the port is a DCE root so the alias lives on
      with nothing behind it.

    Either way the emitted C names an undeclared identifier and gcc rejects the
    translation unit (28 errors on the hierarchical PicoRV32 JIT — the failure
    the `Build multi-core JIT` CI job hits).  Unreachable state reads as its
    reset value, so binding these to 0 is the faithful repair, not a papering
    over. -/
def declareOrphanRefs (design : Design) : Design :=
  { design with modules := design.modules.map fun m =>
      -- Accumulator collection + HashMap dedup: the flatMap + list
      -- `eraseDups` version was O(refs²) — RenameTable-scale bodies have
      -- hundreds of thousands of ref occurrences.
      let referenced : Std.HashMap String Bool := Id.run do
        let mut acc : Std.HashMap String Bool := {}
        let rec go (h : Std.HashMap String Bool) (e : Expr) :
            Std.HashMap String Bool :=
          match e with
          | .ref n => h.insert n true
          | .op _ xs => xs.foldl go h
          | .concat xs => xs.foldl go h
          | .slice x _ _ => go h x
          | .sliceDim x _ _ => go h x
          | .index a i => go (go h a) i
          | _ => h
        for s in m.body do
          match s with
          | .assign _ rhs => acc := go acc rhs
          | .register _ _ _ input _ => acc := go acc input
          | .memory _ _ _ _ wa wd we ra _ _ .. =>
            acc := go (go (go (go acc wa) wd) we) ra
          | .inst _ _ conns =>
            for (_, e) in conns do
              acc := go acc e
        return acc
      let declared : Std.HashMap String Bool := Id.run do
        let mut d : Std.HashMap String Bool := {}
        for p in m.inputs ++ m.outputs ++ m.wires do
          d := d.insert p.name true
        for s in m.body do
          match s with
          | .memory n _ _ _ _ _ _ _ _ _ .. => d := d.insert n true
          | _ => pure ()
        return d
      let orphans := referenced.toList.filterMap fun (n, _) =>
        -- Never paper over a fail-loud sentinel: declaring it and driving
        -- it 0 turned "reduction over unknown width" from a loud
        -- elaboration error into a silent constant (ICacheMissUnit's
        -- meta-entry parity read 0 for every entry).
        if declared.contains n || n.startsWith "__reduction_xor" then none
        else some n
      if orphans.isEmpty then m
      else
        { m with
          wires := m.wires ++ orphans.map fun n =>
            ({ name := n, ty := .bitVector 32 } : Port)
          body := (orphans.map fun n => Stmt.assign n (.const 0 32)) ++ m.body } }

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
  -- Generic reachability DCE: remove unreachable wires/registers
  let stripped := reachabilityDCE result
  -- Optimize: constant folding, DCE, single-use wire inlining
  let optimized := stripResetMuxDesign (Sparkle.IR.Optimize.optimizeDesign stripped)
  pure (declareOrphanRefs optimized)

/-- Parse Verilog and lower to IR, preserving module hierarchy (no flattening).
    Each module is optimized independently. Sub-module instances remain as Stmt.inst.
    This produces C++ classes per module with function-call-based instantiation,
    giving I-cache locality identical to Verilator. -/
def parseAndLowerHierarchical (input : String) : Except String Design := do
  -- Light preprocessing: @(*) and named blocks only.
  -- NO for-loop unroll (PicoRV32 has for loops with different patterns).
  -- For-loop containing modules will be flattened by flattenDesign within
  -- the top module only — sub-modules that use for loops are handled by
  -- the existing unrollForLoops in lowerModule.
  let preprocessed := input
    |> fun s => s.replace "@(*)" "@*"
    |> fun s =>
      let lines := s.splitOn "\n"
      (lines.map fun l =>
        let trimmed := String.trimLeft l
        if trimmed.startsWith "integer " then ""
        else
          let parts := l.splitOn "begin : "
          -- Only strip a NAMED BLOCK label, i.e. when `begin` is a whole
          -- token.  `io_in_begin : 8'h0` (XiangShan ByteMaskTailGen has a
          -- port literally named `io_in_begin` inside a ternary) must not
          -- match — the old substring split silently ate the rest of the
          -- line.
          let isTokenBoundary :=
            parts.length >= 2 &&
            (let before := parts[0]!
             before.isEmpty ||
             (let c := before.back
              !(c.isAlphanum || c == '_' || c == '$')))
          if isTokenBoundary then parts[0]! ++ "begin"
          else l
      ) |> ("\n".intercalate ·)
  let svDesign ← Tools.SVParser.Parser.parse preprocessed
  let design ← lowerDesign svDesign
  -- For hierarchical: top module is the one NOT instantiated by any other module.
  let instantiatedModules := design.modules.flatMap fun m =>
    m.body.filterMap fun s => match s with | .inst modName _ _ => some modName | _ => none
  let topCandidates := design.modules.filter fun m =>
    !instantiatedModules.any (· == m.name)
  let design := match topCandidates.head? with
    | some top => { design with topModule := top.name }
    | none => design
  -- Generic reachability DCE: remove unreachable wires/registers
  let stripped := reachabilityDCE design
  -- Optimize each module independently
  let optimized := stripResetMuxDesign (Sparkle.IR.Optimize.optimizeDesign stripped)
  pure (declareOrphanRefs optimized)

def parseAndLowerWithMemInit (input : String) : Except String (Design × List ReadMemHInfo) := do
  let svDesign ← Tools.SVParser.Parser.parse input
  let design ← lowerDesign svDesign
  let memInits := extractReadMemH svDesign
  pure (design, memInits)

end Tools.SVParser.Lower
