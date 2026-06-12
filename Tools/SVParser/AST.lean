/-
  SystemVerilog AST — Synthesizable RTL Subset

  Captures Verilog syntax faithfully before semantic lowering to Sparkle IR.
  Separate from Sparkle.IR.AST to keep a clean parser/compiler boundary.

  Supports: module with parameters, input/output/output reg, wire/reg,
  assign, always @(posedge)/always @*, if/else, case/casez,
  localparam, integer, for loops, generate if/endgenerate.
-/

namespace Tools.SVParser.AST

/-- Verilog numeric literal with optional width and base -/
inductive SVLiteral where
  | decimal (width : Option Nat) (value : Nat)
  | hex     (width : Option Nat) (value : Nat)
  | binary  (width : Option Nat) (value : Nat)
  /-- `casez`-style binary literal with `?` wildcards (e.g. `4'b1???`).
      `value` keeps the non-`?` bits set, `mask` has a 1 in every `?`
      position (i.e. "bits to ignore when comparing").  Equivalent to
      a plain `binary` when `mask = 0`. -/
  | binaryWild (width : Nat) (value : Nat) (mask : Nat)
  deriving Repr, BEq

/-- Unary operators -/
inductive SVUnaryOp where
  | logNot    -- !
  | bitNot    -- ~
  | neg       -- - (unary minus)
  | reductAnd -- &x (reduction AND)
  | reductOr  -- |x (reduction OR)
  | signed    -- $signed(x)
  deriving Repr, BEq

/-- Binary operators -/
inductive SVBinOp where
  -- Arithmetic
  | add | sub | mul
  -- Bitwise
  | bitAnd | bitOr | bitXor
  -- Shift
  | shl | shr | asr
  -- Comparison
  | eq | neq | lt | le | gt | ge
  -- Logical
  | logAnd | logOr
  deriving Repr, BEq

/-- Expressions -/
inductive SVExpr where
  | lit     (l : SVLiteral)
  | ident   (name : String)
  | unary   (op : SVUnaryOp) (arg : SVExpr)
  | binary  (op : SVBinOp) (lhs rhs : SVExpr)
  | ternary (cond then_ else_ : SVExpr)
  | index   (arr : SVExpr) (idx : SVExpr)
  | slice   (expr : SVExpr) (hi lo : Nat)
  | partSelectPlus (expr : SVExpr) (base : SVExpr) (width : SVExpr)  -- [base +: width]
  | concat  (args : List SVExpr)
  | repeat_ (count : SVExpr) (value : SVExpr)  -- {n{expr}}
  deriving Repr, BEq

/-- Statements (inside always blocks) -/
inductive SVStmt where
  | blockAssign    (lhs rhs : SVExpr)                -- lhs = rhs;
  | nonblockAssign (lhs rhs : SVExpr)                -- lhs <= rhs;
  | ifElse (cond : SVExpr) (then_ else_ : List SVStmt)
  | caseStmt (expr : SVExpr) (arms : List (List SVExpr × List SVStmt))
      (default_ : Option (List SVStmt))
  | forLoop (init : SVStmt) (cond : SVExpr) (step : SVStmt) (body : List SVStmt)
  | assertStmt (cond : SVExpr)                          -- assert(cond);
  deriving Repr, BEq

/-- Sensitivity list for always blocks -/
inductive SVSensitivity where
  | posedge (signal : String)
  | negedge (signal : String)
  | star
  deriving Repr, BEq

/-- Port direction -/
inductive SVPortDir where
  | input | output | inout
  deriving Repr, BEq

/-- Port declaration.

    `width` is the *resolved* `(hi, lo)` pair (e.g. `(7, 0)` for an
    8-bit port).  `widthExpr` is the *symbolic* pair captured at parse
    time when either bound mentions a parameter — e.g. `[W-1:0]`
    becomes `widthExpr = some (W-1, 0)` while `width` falls back to
    the parser's `(31, 0)` default.  Lower-time param substitution
    resolves `widthExpr` against the param value map and overwrites
    `width`. -/
structure SVPort where
  dir    : SVPortDir
  isReg  : Bool := false            -- output reg
  width  : Option (Nat × Nat)       -- [hi:lo] or none for 1-bit
  name   : String
  widthExpr : Option (SVExpr × SVExpr) := none  -- symbolic [hi:lo] before param subst
  deriving Repr, BEq

/-- Parameter declaration -/
structure SVParam where
  name      : String
  width     : Option (Nat × Nat)     -- optional [hi:lo]
  value     : SVExpr                 -- default value expression
  isLocal   : Bool := false          -- localparam vs parameter
  widthExpr : Option (SVExpr × SVExpr) := none  -- symbolic [hi:lo] before param subst
  deriving Repr, BEq

/-- Module-level items -/
inductive SVModuleItem where
  | wireDecl      (name : String) (width : Option (Nat × Nat))
                  (initExpr : Option SVExpr)              -- wire [w] x = expr;
  | regDecl       (name : String) (width : Option (Nat × Nat))
                  (arraySize : Option Nat)                -- reg [w] x [0:N];
  | integerDecl   (name : String)                         -- integer i;
  | paramDecl     (param : SVParam)                       -- parameter/localparam
  | contAssign    (lhs rhs : SVExpr)                      -- assign lhs = rhs;
  | alwaysBlock   (sensitivity : SVSensitivity) (body : List SVStmt)
  | generateBlock (cond : SVExpr) (body : List SVModuleItem)
                  (elseBody : List SVModuleItem)          -- generate if (...) ... endgenerate
  | instantiation (moduleName instName : String)
                  (connections : List (String × SVExpr))
                  (paramOverrides : List (String × SVExpr) := [])
  | taskDecl      (name : String) (body : List SVStmt)    -- task ... endtask
  | readmemh      (filename : String) (memName : String)  -- $readmemh("file", mem)
  deriving Repr, BEq

/-- A parsed Verilog module -/
structure SVModule where
  name   : String
  params : List SVParam := []       -- #(parameter ...) list
  ports  : List SVPort
  items  : List SVModuleItem
  deriving Repr, BEq

/-- A collection of modules -/
structure SVDesign where
  modules : List SVModule
  deriving Repr, BEq

end Tools.SVParser.AST
