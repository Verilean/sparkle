/-
  SystemVerilog AST — Synthesizable RTL Subset

  Captures Verilog syntax faithfully before semantic lowering to Sparkle IR.
  Separate from Sparkle.IR.AST to keep a clean parser/compiler boundary.
-/

namespace Tools.SVParser.AST

/-- Verilog numeric literal with optional width and base -/
inductive SVLiteral where
  | decimal (width : Option Nat) (value : Nat)
  | hex     (width : Option Nat) (value : Nat)
  | binary  (width : Option Nat) (value : Nat)
  deriving Repr, BEq

/-- Unary operators -/
inductive SVUnaryOp where
  | logNot    -- !
  | bitNot    -- ~
  | neg       -- - (unary minus)
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
  | concat  (args : List SVExpr)
  deriving Repr, BEq

/-- Statements (inside always blocks) -/
inductive SVStmt where
  | blockAssign    (lhs rhs : SVExpr)                -- lhs = rhs;
  | nonblockAssign (lhs rhs : SVExpr)                -- lhs <= rhs;
  | ifElse (cond : SVExpr) (then_ else_ : List SVStmt)
  | caseStmt (expr : SVExpr) (arms : List (SVExpr × List SVStmt))
      (default_ : Option (List SVStmt))
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

/-- Port declaration -/
structure SVPort where
  dir   : SVPortDir
  width : Option (Nat × Nat)   -- [hi:lo] or none for 1-bit
  name  : String
  deriving Repr, BEq

/-- Module-level items -/
inductive SVModuleItem where
  | wireDecl   (name : String) (width : Option (Nat × Nat))
  | regDecl    (name : String) (width : Option (Nat × Nat))
  | contAssign (lhs rhs : SVExpr)                         -- assign lhs = rhs;
  | alwaysBlock (sensitivity : SVSensitivity) (body : List SVStmt)
  | instantiation (moduleName instName : String)
      (connections : List (String × SVExpr))
  deriving Repr, BEq

/-- A parsed Verilog module -/
structure SVModule where
  name  : String
  ports : List SVPort
  items : List SVModuleItem
  deriving Repr, BEq

/-- A collection of modules -/
structure SVDesign where
  modules : List SVModule
  deriving Repr, BEq

end Tools.SVParser.AST
