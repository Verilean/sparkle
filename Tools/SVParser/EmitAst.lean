/-
  M0 of the certified-roundtrip track: the emitter, factored through the
  parser's AST.

      shipping:   Expr ──emitExpr──────────────▶ String
      factored:   Expr ──emitAstExpr──▶ SVExpr ──(render)──▶ String

  `emitAstExpr` is a TOTAL function producing, for every IR expression
  the shipping emitter handles, the SVExpr that the shipping parser
  yields on the shipping emitter's output:

      Parser.parseExprString (Verilog.emitExpr widthOf e)
        = .ok (emitAstExpr widthOf e)          -- validated below

  Design decisions:

  * Validation is PARSE-equality, not byte-equality of a re-renderer.
    The shipping emitter's formatting is not compositional (e.g. a
    slice-of-compound prints `n'((E) >> lo)` — parens on the operand,
    none on the shift), so a byte-identical pretty-printer would have to
    encode formatting accidents in the AST.  Parse-equality is also the
    stronger tie: it validates `emitAstExpr` against BOTH shipping
    functions at once, and is exactly the composition the roundtrip
    theorem factors through.

  * `emitAstExpr` mirrors the shipping arms LINE FOR LINE, including the
    normalizations (width-cast NOT, bias-encoded signed compares,
    size-cast slice-of-compound, concat element casts, `$signed` asr) —
    it is a specification OF the emitter, not an idealization.  The
    `#guard`s at the bottom hold the mirror to the shipping code arm by
    arm; edit one without the other and the build fails.

  * `exprWidthT` is the total twin of the shipping `partial def
    exprWidthV` (same rules), because a `partial def` cannot appear in
    anything we later want unfolding equations for.

  `none` = outside the emitAst fragment: symbolic-width `sliceDim`
  (specialized away before emission on the shipping path) and malformed
  arities (where the shipping emitter prints `/* ERROR … */`).
-/

import Sparkle.Backend.Verilog
import Tools.SVParser.AST
import Tools.SVParser.Parser

namespace Tools.SVParser.EmitAst

open Sparkle.IR.AST
open Tools.SVParser.AST
open Sparkle.Backend.Verilog (sanitizeName)

/-- Total twin of `Sparkle.Backend.Verilog.exprWidthV` (verbatim rules). -/
def exprWidthT (widthOf : String → Option Nat) : Expr → Option Nat
  | .const _ w => some w
  | .ref n => widthOf n
  | .slice _ hi lo => some (hi - lo + 1)
  | .concat args => goSum args
  | .op op args =>
    match op with
    | .eq | .lt_u | .lt_s | .le_u | .le_s | .gt_u | .gt_s | .ge_u | .ge_s =>
      some 1
    | .and | .or | .xor | .not | .add | .sub => goMax args
    | .mux =>
      match args with
      | [_, t, e] =>
        match exprWidthT widthOf t, exprWidthT widthOf e with
        | some x, some y => some (max x y)
        | _, _ => none
      | _ => none
    | _ => none
  | _ => none
where
  goSum : List Expr → Option Nat
    | [] => some 0
    | a :: rest =>
      match exprWidthT widthOf a, goSum rest with
      | some x, some y => some (x + y)
      | _, _ => none
  goMax : List Expr → Option Nat
    | [] => some 1
    | a :: rest =>
      match exprWidthT widthOf a, goMax rest with
      | some x, some y => some (max x y)
      | _, _ => none

/-- Two's-complement encoding of a possibly-negative constant, as the
    emitter performs it. -/
def encodeConst (v : Int) (w : Nat) : Nat :=
  Int.toNat (((v % (2 ^ w : Nat)) + (2 ^ w : Nat)) % (2 ^ w : Nat))

/-- The inverse of `lowerBinOp` on the operators the emitter prints as a
    plain infix binary. -/
def binOpOf : Operator → Option SVBinOp
  | .and => some .bitAnd
  | .or => some .bitOr
  | .xor => some .bitXor
  | .add => some .add
  | .sub => some .sub
  | .mul => some .mul
  | .eq => some .eq
  | .lt_u => some .lt
  | .le_u => some .le
  | .gt_u => some .gt
  | .ge_u => some .ge
  | .shl => some .shl
  | .shr => some .shr
  | _ => none

mutual
/-- The shipping `emitExpr`, at the AST level (see the header). -/
def emitAstExpr (widthOf : String → Option Nat) : Expr → Option SVExpr
  | .const v w =>
    -- Zero-width constants are emitted 1-bit (Verilog forbids `0'd0`);
    -- negatives print as sized HEX two's complement.
    let w0 := if w == 0 then 1 else w
    if v < 0 then some (.lit (.hex (some w0) (encodeConst v w0)))
    else some (.lit (.decimal (some w0) v.toNat))
  | .ref n => some (.ident (sanitizeName n))
  | .concat args => do
    -- Op-typed elements of known nonzero width get a size cast, pinning
    -- Verilog's self-determined element width to the IR's.
    some (.concat (← emitConcatElems widthOf args))
  | .slice e hi lo =>
    match e with
    | .ref name =>
      -- Full-width slice of a known wire is elided (`s[0:0]` on a
      -- scalar is illegal Verilog).  NOTE: the shipping lookup is on
      -- the SANITIZED name.
      match widthOf (sanitizeName name) with
      | some w =>
        if lo == 0 && hi + 1 ≥ w then some (.ident (sanitizeName name))
        else some (.slice (.ident (sanitizeName name)) hi lo)
      | none => some (.slice (.ident (sanitizeName name)) hi lo)
    | _ => do
      -- Part-select on a compound is illegal; the emitter prints a size
      -- cast `n'((E) >> lo)` instead.
      let inner ← emitAstExpr widthOf e
      let n := hi + 1 - lo
      if lo == 0 then some (.sizeCast n inner)
      else some (.sizeCast n (.binary .shr inner (.lit (.decimal none lo))))
  | .sliceDim _ _ _ => none
  | .index arr idx => do
    some (.index (← emitAstExpr widthOf arr) (← emitAstExpr widthOf idx))
  | .op .mux [c, t, f] => do
    some (.ternary (← emitAstExpr widthOf c) (← emitAstExpr widthOf t)
                   (← emitAstExpr widthOf f))
  | .op .not [arg] => do
    -- Verilog's `~` is context-determined; the emitter pins the width
    -- with `(w'(inner ^ w'(2^w-1)))` when the operand width is known.
    let inner ← emitAstExpr widthOf arg
    match exprWidthT widthOf arg with
    | some w =>
      if w == 0 then some (.unary .bitNot inner)
      else some (.sizeCast w (.binary .bitXor inner
                   (.sizeCast w (.lit (.decimal none (2 ^ w - 1))))))
    | none => some (.unary .bitNot inner)
  | .op .neg [arg] => do
    some (.unary .neg (← emitAstExpr widthOf arg))
  | .op operator [a, b] => do
    let ea ← emitAstExpr widthOf a
    let eb ← emitAstExpr widthOf b
    match operator with
    | .lt_s | .le_s | .gt_s | .ge_s =>
      -- Bias-encoded signed compare when the value width is known:
      -- `((a & m) ^ sb) OP ((b & m) ^ sb)` over UNSIGNED comparison.
      let cmp : SVBinOp := match operator with
        | .lt_s => .lt | .le_s => .le | .gt_s => .gt | _ => .ge
      let w? := match exprWidthT widthOf a, exprWidthT widthOf b with
        | some x, some y => some (max x y)
        | some x, none => some x
        | none, some y => some y
        | none, none => none
      match w? with
      | some w =>
        if w == 0 then some (.lit (.binary (some 1) 0))
        else
          let m : SVExpr := .lit (.hex (some w) (2 ^ w - 1))
          let sb : SVExpr := .lit (.hex (some w) (2 ^ (w - 1)))
          some (.binary cmp (.binary .bitXor (.binary .bitAnd ea m) sb)
                            (.binary .bitXor (.binary .bitAnd eb m) sb))
      | none =>
        some (.binary cmp (.unary .signed ea) (.unary .signed eb))
    | .asr =>
      some (.binary .asr (.unary .signed ea) (.unary .signed eb))
    | _ => do
      some (.binary (← binOpOf operator) ea eb)
  | .op _ _ => none

def emitConcatElems (widthOf : String → Option Nat) :
    List Expr → Option (List SVExpr)
  | [] => some []
  | a :: rest => do
    let ea ← emitAstExpr widthOf a
    let ea := match a with
      | .op _ _ =>
        match exprWidthT widthOf a with
        | some w => if w > 0 then .sizeCast w ea else ea
        | none => ea
      | _ => ea
    let es ← emitConcatElems widthOf rest
    some (ea :: es)
end

/-- Run the shipping expression parser on a string (the validation
    harness for parse-equality). -/
def parseExprString (s : String) : Except String SVExpr :=
  Tools.SVParser.Lexer.run
    (do Tools.SVParser.Lexer.ws; Tools.SVParser.Parser.parseExpr) s

/- ------------------------------------------------------------------ -/
/- Validation: parse-equality against the SHIPPING emitter, arm by arm. -/

private def wof : String → Option Nat
  | "a" => some 8
  | "b" => some 8
  | "s" => some 1
  | "wide" => some 96
  | _ => none

private def chk (e : Expr) : Bool :=
  match parseExprString (Sparkle.Backend.Verilog.emitExpr wof e) with
  | .ok sv => emitAstExpr wof e == some sv
  | .error _ => false

-- consts: sized decimal, zero-width promotion, negative → sized hex
#guard chk (.const 42 8)
#guard chk (.const 0 0)
#guard chk (.const (-2) 8)
-- refs (incl. a name needing sanitization)
#guard chk (.ref "a")
#guard chk (.ref "io$weird")
-- concat, with an op element getting its width pin
#guard chk (.concat [.ref "a", .ref "b"])
#guard chk (.concat [.op .and [.ref "a", .ref "b"], .ref "b"])
-- slices: full-width elide, plain, and slice-of-compound (both lo forms)
#guard chk (.slice (.ref "a") 7 0)
#guard chk (.slice (.ref "a") 3 1)
#guard chk (.slice (.op .add [.ref "a", .ref "b"]) 3 0)
#guard chk (.slice (.op .add [.ref "a", .ref "b"]) 3 1)
-- index / mux / neg
#guard chk (.index (.ref "wide") (.ref "a"))
#guard chk (.op .mux [.ref "s", .ref "a", .ref "b"])
#guard chk (.op .neg [.ref "a"])
-- width-pinned NOT, and NOT of unknown width (parenthesised fallback)
#guard chk (.op .not [.ref "a"])
#guard chk (.op .not [.ref "unknown"])
#guard chk (.op .not [.op .not [.ref "unknown"]])
-- every plain binary
#guard chk (.op .and [.ref "a", .ref "b"])
#guard chk (.op .or [.ref "a", .ref "b"])
#guard chk (.op .xor [.ref "a", .ref "b"])
#guard chk (.op .add [.ref "a", .ref "b"])
#guard chk (.op .sub [.ref "a", .ref "b"])
#guard chk (.op .mul [.ref "a", .ref "b"])
#guard chk (.op .eq [.ref "a", .ref "b"])
#guard chk (.op .lt_u [.ref "a", .ref "b"])
#guard chk (.op .le_u [.ref "a", .ref "b"])
#guard chk (.op .gt_u [.ref "a", .ref "b"])
#guard chk (.op .ge_u [.ref "a", .ref "b"])
#guard chk (.op .shl [.ref "a", .ref "b"])
#guard chk (.op .shr [.ref "a", .ref "b"])
-- signed compares: bias form (known widths) and $signed fallback
#guard chk (.op .lt_s [.ref "a", .ref "b"])
#guard chk (.op .ge_s [.ref "a", .ref "b"])
#guard chk (.op .lt_s [.ref "unknown", .ref "unknown2"])
-- asr
#guard chk (.op .asr [.ref "a", .ref "b"])
-- nesting stress: everything at once
#guard chk (.op .mux [.op .eq [.ref "a", .const 3 8],
                      .concat [.op .not [.ref "a"], .slice (.ref "b") 3 1],
                      .op .add [.op .mul [.ref "a", .ref "b"], .const 1 8]])
-- total width twin agrees with the shipping partial one
private def chkW (e : Expr) : Bool :=
  exprWidthT wof e == Sparkle.Backend.Verilog.exprWidthV wof e
#guard chkW (.op .and [.ref "a", .const 3 4])
#guard chkW (.concat [.ref "a", .ref "b", .const 1 1])
#guard chkW (.op .mux [.ref "s", .ref "a", .ref "wide"])
#guard chkW (.op .not [.ref "a"])
#guard chkW (.op .eq [.ref "a", .ref "b"])

end Tools.SVParser.EmitAst
