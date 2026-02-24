/-
  BitNet BitLinear BitWidth

  Bit-width tracking and sign extension for the pipelined adder tree.
  Core abstraction: `SizedExpr` pairs a Sparkle `Expr` with its known bit-width.
-/

import Sparkle.IR.Builder
import Sparkle.IR.AST
import Sparkle.IR.Type

namespace Sparkle.Examples.BitNet.BitLinear

open Sparkle.IR.Builder
open Sparkle.IR.AST
open Sparkle.IR.Type
open CircuitM

/-- An expression paired with its known bit-width -/
structure SizedExpr where
  expr  : Expr
  width : Nat
  deriving Repr

instance : Inhabited SizedExpr where
  default := { expr := .const 0 1, width := 1 }

/-- The bit-width rule for signed addition: max(n,m) + 1 -/
def addBitWidth (a b : Nat) : Nat := max a b + 1

/-- Sign-extend a SizedExpr to `targetWidth` bits. -/
def signExtendExpr (se : SizedExpr) (targetWidth : Nat) : CircuitM SizedExpr := do
  if se.width == targetWidth then
    return se
  else if se.width > targetWidth then
    let w ← makeWire "trunc" (.bitVector targetWidth)
    emitAssign w (Expr.slice se.expr (targetWidth - 1) 0)
    return { expr := .ref w, width := targetWidth }
  else
    let k := targetWidth - se.width
    if k == 1 then
      let w ← makeWire "sext" (.bitVector targetWidth)
      emitAssign w (Expr.concat [Expr.slice se.expr (se.width - 1) (se.width - 1), se.expr])
      return { expr := .ref w, width := targetWidth }
    else
      let signBit := Expr.slice se.expr (se.width - 1) (se.width - 1)
      let highBits ← makeWire "high_fill" (.bitVector k)
      emitAssign highBits (Expr.mux signBit
        (.const ((1 <<< k) - 1) k)
        (.const 0 k))
      let w ← makeWire "sext" (.bitVector targetWidth)
      emitAssign w (Expr.concat [.ref highBits, se.expr])
      return { expr := .ref w, width := targetWidth }

end Sparkle.Examples.BitNet.BitLinear
