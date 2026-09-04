/-
  Zero-width elimination — the fix for shipping bug #9.

  The elaborator deliberately materializes `Unit`/`PUnit` HList
  terminators as zero-width wires (`_tmp_b_N = const 0 0`) and packs
  them into the loop-state concat.  In the IR that is harmless: a
  width-0 element contributes zero bits to `concat` under the
  semantics' MSB-first assembly.  SystemVerilog, however, has no
  zero-width nets — the Verilog backend declared them as `logic [0:0]`
  and emitted them into the concat as a REAL bit, widening the pack by
  one and letting the implicit assignment truncation shift every
  register's value left each cycle:

      logic [7:0] _tmp_loop_body;          // 8-bit net
      assign _tmp_loop_body = {r, _tmp_b}; // 9-bit RHS → truncated!

  An emitted 8-bit counter counted 2, 6, 14, 30, 62 under iverilog.
  Every `circuit do` design's emitted Verilog was affected (the
  IR/CSim paths were always correct, which is why simulation tests
  never saw it).

  This pass removes zero-width elements at the IR level, right where
  the elaborator finishes a module: drop concat elements of width 0
  (collapsing a resulting singleton), drop assignments to width-0
  wires, and drop the width-0 wire declarations.  Every backend and
  every verifier then sees the clean module.
-/
import Sparkle.IR.AST
import Sparkle.IR.Optimize

namespace Sparkle.IR.ZeroWidth

open Sparkle.IR.AST
open Sparkle.IR.Optimize (WidthMap buildWidthMap)

/-- Total width mirror (matches `Sparkle.IR.Semantics.widthOf`'s
    rules; only used to detect width-0 concat elements). -/
def exprWidth (wm : WidthMap) : Expr → Nat
  | .const _ w => w
  | .ref n => wm.getD n 0
  | .op .mux args =>
    match args with
    | [_, t, _] => exprWidth wm t
    | _ => 0
  | .op .eq _ | .op .lt_u _ | .op .lt_s _ | .op .le_u _ | .op .le_s _
  | .op .gt_u _ | .op .gt_s _ | .op .ge_u _ | .op .ge_s _ => 1
  | .op .not args =>
    match args with
    | [a] => exprWidth wm a
    | _ => 0
  | .op .shr args =>
    match args with
    | [a, _] => exprWidth wm a
    | _ => 0
  | .op _ args =>
    match args with
    | [a, b] => max (exprWidth wm a) (exprWidth wm b)
    | [a] => exprWidth wm a
    | _ => 0
  | .concat args => go args
  | .slice _ hi lo => hi - lo + 1
  | .sliceDim _ _ _ => 0
  | .index _ _ => 0
where
  go : List Expr → Nat
    | [] => 0
    | a :: rest => exprWidth wm a + go rest

mutual
/-- Drop width-0 concat elements (they contribute no bits); collapse a
    resulting singleton concat to its element. -/
def dzExpr (wm : WidthMap) : Expr → Expr
  | .concat args =>
    match (dzList wm args).filter (fun a => exprWidth wm a != 0) with
    | [a] => a
    | as => .concat as
  | .op o args => .op o (dzList wm args)
  | .slice e hi lo => .slice (dzExpr wm e) hi lo
  | .sliceDim e d i => .sliceDim (dzExpr wm e) d i
  | .index a i => .index (dzExpr wm a) (dzExpr wm i)
  | e => e

def dzList (wm : WidthMap) : List Expr → List Expr
  | [] => []
  | a :: rest => dzExpr wm a :: dzList wm rest
end

/-- Drop assignments to width-0 wires (their value is unobservable and
    they no longer appear anywhere after `dzExpr`); clean every other
    statement's expressions. -/
def dzStmt (wm : WidthMap) : Stmt → Option Stmt
  | .assign l r =>
    match wm.get? l with
    | some 0 => none
    | _ => some (.assign l (dzExpr wm r))
  | .register o c rs i iv => some (.register o c rs (dzExpr wm i) iv)
  | .memory nm aw dw c wa wd wen ra rd cr ew er =>
    some (.memory nm aw dw c (dzExpr wm wa) (dzExpr wm wd)
      (dzExpr wm wen) (dzExpr wm ra) rd cr
      (ew.map fun p => (dzExpr wm p.1, dzExpr wm p.2.1, dzExpr wm p.2.2))
      (er.map fun p => (dzExpr wm p.1, p.2)))
  | .inst mn i conns =>
    some (.inst mn i (conns.map fun p => (p.1, dzExpr wm p.2)))

def dropZeroWidthModule (m : Module) : Module :=
  let wm := buildWidthMap m
  { m with
    body := m.body.filterMap (dzStmt wm),
    wires := m.wires.filter (fun p => p.ty.bitWidth != 0) }

def dropZeroWidthDesign (d : Design) : Design :=
  { d with modules := d.modules.map dropZeroWidthModule }

end Sparkle.IR.ZeroWidth
