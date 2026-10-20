import Tools.ShippingReaderApp

/-! # The reader by levels on the applicative lifts (G3)

`Tools.ShippingReaderApp.readN cfg k` reads the three applicative kinds,
with lifts nested at most `k` deep through first operands. This file runs
it (compiled code, logs prefixed `READERAPP`, no assertion) on quotations of
closed terms:

* `t1`: one lift (`appBool`): expected unread at level 0, read at level 1;
* `t2`: a lift whose FIRST operand is a lift: expected read from level 2;
* `t3`: a lift whose SECOND operand is a lift: expected read at level 1;
* `t4`: a lifted comparison of two literals at width 8, level 1.

For every level 0 … 3: whether the reader returns a term, and whether that
term quotes back to the expression. -/
namespace Tests.Compiler.ReaderAppTest
open Sparkle.Compiler.Elab
open Tools.ShippingUnifiedSource Tools.ShippingReaderTerm Tools.ShippingReaderInputs
open Tools.ShippingReaderApp

def dom : Lean.Expr := .const ``Sparkle.Core.Domain.defaultDomain []

def cfg : Cfg := kindsCfg dom (isExpr dom) []

def t1 : Term .bool := .appBool .band (.boolLit true) (.boolLit false)
def t2 : Term .bool := .appBool2 .nor t1 (.boolLit true)
def t3 : Term .bool := .appBool .bxor (.boolLit true) t1
def t4 : Term .bool := .appCompare .ule (.bitsLit 8 3) (.bitsLit 8 200)

def report (nm : String) (t : Term .bool) : IO Unit := do
  let e := quote cfg.dom cfg.bools cfg.bits t
  for k in [0, 1, 2, 3] do
    match readN cfg k e with
    | none => IO.println s!"READERAPP {nm} level {k}: not read"
    | some r =>
      IO.println s!"READERAPP {nm} level {k}: read, quotes back = {quote cfg.dom cfg.bools cfg.bits r.2 == e}"

#eval report "t1" t1
#eval report "t2" t2
#eval report "t3" t3
#eval report "t4" t4

end Tests.Compiler.ReaderAppTest
