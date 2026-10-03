/-
  M4: a mathematical semantics for the emitted SystemVerilog SUBSET.

  `evalSV` models Verilog's width algorithm as restricted to the shapes
  `emitAstExpr` produces: every expression is evaluated at a CONTEXT
  width `W = max ctx (widthSV e)`; context-determined operands
  (arith/bitwise/ternary arms) inherit `W`, while the self-determined
  boundaries reset it — size-cast arguments (cast width), comparison
  operands (their own max), shift amounts, concat elements, condition
  of a ternary.

  The target theorem (`emit_sem`, growing fragment): for fragment
  expressions,

      evalSV wof env (widthOf we e) (emitAstExpr wof e)
        = evalExpr we env e

  — the direct forward-correctness statement that removes the PARSER
  from the trusted base for the emit direction.  The context width at
  the top is the assignment LHS width, which the module fragment
  (BFrag.assign's width-agreement condition) pins to `widthOf we e`.
-/
import Tools.SVParser.AST
import Sparkle.IR.Semantics

namespace Tools.SVParser.SVSemantics

open Tools.SVParser.AST
open Sparkle.IR.Semantics (mask)

/-- Value environment (by identifier). -/
abbrev SEnv := String → Nat

/-- Self-determined width of a subset expression (`none` = outside the
    modeled subset: unknown ident widths, index/part-select/repeat). -/
def widthSV (wof : String → Option Nat) : SVExpr → Option Nat
  | .lit (.decimal (some w) _) => some w
  | .lit (.decimal none _) => some 32
  | .lit (.hex (some w) _) => some w
  | .lit (.hex none _) => some 32
  | .lit (.binary (some w) _) => some w
  | .lit (.binary none _) => some 32
  | .lit (.binaryWild w _ _) => some w
  | .ident n => wof n
  | .sizeCast w _ => some w
  | .unary .bitNot a => widthSV wof a
  | .unary .neg a => widthSV wof a
  | .unary .signed a => widthSV wof a
  | .unary _ _ => some 1        -- reductions, logical not
  | .binary op a b =>
    match op with
    | .eq | .neq | .lt | .le | .gt | .ge | .logAnd | .logOr => some 1
    | .shl | .shr | .asr => widthSV wof a
    | _ => do some (max (← widthSV wof a) (← widthSV wof b))
  | .ternary _ t f => do some (max (← widthSV wof t) (← widthSV wof f))
  | .concat args => go args
  | .slice (.ident _) hi lo => some (hi - lo + 1)
  | _ => none
where
  go : List SVExpr → Option Nat
    | [] => some 0
    | a :: rest => do some ((← widthSV wof a) + (← go rest))

/-- Literal value. -/
def litVal : SVLiteral → Nat
  | .decimal _ v => v
  | .hex _ v => v
  | .binary _ v => v
  | .binaryWild _ v _ => v

mutual
/-- Evaluate at an EXPLICIT width `W` (all context-determined operands
    inherit it). -/
def evalAt (wof : String → Option Nat) (env : SEnv) (W : Nat) :
    SVExpr → Option Nat
  | .lit l => some (mask W (litVal l))
  | .ident n => do
    let _ ← wof n          -- outside the subset if the width is unknown
    some (mask W (env n))
  | .sizeCast w a => do
    -- self-determined boundary: the argument sees a w-bit context and
    -- the cast truncates to w, then zero-extends into W
    let v ← evalSV wof env w a
    some (mask W (mask w v))
  | .unary .bitNot a => do
    let v ← evalAt wof env W a
    some (mask W (v ^^^ (2 ^ W - 1)))
  | .unary .neg a => do
    let v ← evalAt wof env W a
    some (mask W (2 ^ W - mask W v))
  | .unary _ _ => none        -- $signed / reductions: not yet modeled
  | .binary op a b =>
    match op with
    | .bitAnd => do
      some (mask W ((← evalAt wof env W a) &&& (← evalAt wof env W b)))
    | .bitOr => do
      some (mask W ((← evalAt wof env W a) ||| (← evalAt wof env W b)))
    | .bitXor => do
      some (mask W ((← evalAt wof env W a) ^^^ (← evalAt wof env W b)))
    | .add => do
      some (mask W ((← evalAt wof env W a) + (← evalAt wof env W b)))
    | .sub => do
      let va ← evalAt wof env W a
      let vb ← evalAt wof env W b
      some (mask W (va + (2 ^ W - mask W vb)))
    | .mul => do
      some (mask W ((← evalAt wof env W a) * (← evalAt wof env W b)))
    | .shl => do
      -- amount is self-determined
      some (mask W ((← evalAt wof env W a) <<< (← evalSV wof env 0 b)))
    | .shr => do
      some ((← evalAt wof env W a) >>> (← evalSV wof env 0 b))
    | .eq => do
      -- comparison operands size to their own max, independent of W
      let wc := max (← widthSV wof a) (← widthSV wof b)
      let va ← evalAt wof env wc a
      let vb ← evalAt wof env wc b
      some (if va = vb then 1 else 0)
    | .lt => do
      let wc := max (← widthSV wof a) (← widthSV wof b)
      let va ← evalAt wof env wc a
      let vb ← evalAt wof env wc b
      some (if va < vb then 1 else 0)
    | .le => do
      let wc := max (← widthSV wof a) (← widthSV wof b)
      let va ← evalAt wof env wc a
      let vb ← evalAt wof env wc b
      some (if va ≤ vb then 1 else 0)
    | .gt => do
      let wc := max (← widthSV wof a) (← widthSV wof b)
      let va ← evalAt wof env wc a
      let vb ← evalAt wof env wc b
      some (if vb < va then 1 else 0)
    | .ge => do
      let wc := max (← widthSV wof a) (← widthSV wof b)
      let va ← evalAt wof env wc a
      let vb ← evalAt wof env wc b
      some (if vb ≤ va then 1 else 0)
    | _ => none               -- neq/logical/asr: not yet modeled
  | .ternary c t f => do
    let vc ← evalSV wof env 0 c   -- condition is self-determined
    if vc ≠ 0 then evalAt wof env W t else evalAt wof env W f
  | .concat args => do
    -- elements are self-determined; MSB-first assembly, zero-extended
    let v ← goConcat wof env args
    some (mask W v)
  | .slice (.ident n) hi lo => do
    -- part-select on a declared vector: reads the RAW bits of the
    -- signal (never context-widened), then zero-extends into W.
    -- Only in-range selects are modeled — an out-of-range select is
    -- x-valued in Verilog and outside this subset.
    let w ← wof n
    if lo ≤ hi ∧ hi < w then
      some (mask W (mask (hi - lo + 1) ((env n) >>> lo)))
    else none
  | _ => none

/-- Evaluate with a CONTEXT width: the effective width is the max of
    the context and the expression's self-determined width. -/
def evalSV (wof : String → Option Nat) (env : SEnv) (ctx : Nat)
    (e : SVExpr) : Option Nat := do
  evalAt wof env (max ctx (← widthSV wof e)) e

def goConcat (wof : String → Option Nat) (env : SEnv) :
    List SVExpr → Option Nat
  | [] => some 0
  | a :: rest => do
    let wa ← widthSV wof a
    let va ← evalSV wof env 0 a
    let restW ← widthSV.go wof rest
    let vr ← goConcat wof env rest
    some ((mask wa va) <<< restW ||| vr)
end

/- Behavioral pins: the width algorithm on the shapes that motivated
   the emitter's pinning rules. -/
section Pins
private def wofP : String → Option Nat
  | "a" => some 8 | "b" => some 8 | "c" => some 1 | "s" => some 4
  | _ => none
private def envP : SEnv := fun n =>
  if n == "a" then 0xA5 else if n == "b" then 3 else
  if n == "c" then 1 else if n == "s" then 9 else 0

-- bare add in an 8-bit context wraps at 8 bits
#guard evalSV wofP envP 8 (.binary .add (.ident "a") (.ident "b"))
    = some ((0xA5 + 3) % 256)
-- the SAME add in a 12-bit context keeps the carry — the classic
-- context-width effect the fragment's width agreement rules out
#guard evalSV wofP envP 12 (.binary .add (.ident "a") (.ident "b"))
    = some (0xA5 + 3)
-- ~ in a wide context inverts the container: the NCBUpstreamRXREQ
-- accident class, and why the emitter pins NOT with a cast
#guard evalSV wofP envP 32 (.unary .bitNot (.ident "c"))
    = some (0xFFFFFFFE)
-- the emitter's pinned NOT: 1'(c ^ 1'd1) is context-immune
#guard evalSV wofP envP 32
    (.sizeCast 1 (.binary .bitXor (.ident "c")
      (.lit (.decimal (some 1) 1)))) = some 0
-- comparison operands size to their own max, independent of context
#guard evalSV wofP envP 32 (.binary .lt (.ident "s") (.ident "a"))
    = some 1
-- concat elements are self-determined
#guard evalSV wofP envP 0 (.concat [.ident "c", .ident "s"])
    = some ((1 <<< 4) ||| 9)
-- part-select reads raw bits, context-immune (a = 0xA5 → a[6:4] = 2,
-- even in a 32-bit context)
#guard evalSV wofP envP 32 (.slice (.ident "a") 6 4) = some 2
-- out-of-range select is outside the subset
#guard evalSV wofP envP 0 (.slice (.ident "a") 8 0) = none
end Pins

end Tools.SVParser.SVSemantics
