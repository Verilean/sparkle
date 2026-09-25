/-
  Result check for `optimizeModule` on small combinational modules.

  `optimizeModule` is a multi-phase optimizer; rather than prove it directly,
  its result is treated as an untrusted proposal.  For a module whose body is
  made only of `assign`s over fitting constants, references and the six
  binary operators `+ - * & | ^`, the proposal is kept only if `optCheck`
  accepts it: every output of both modules normalises to the SAME expression
  over the inputs.  Normalisation inlines each assignment's (already
  normalised) definition into later uses — only when the wire's declared
  width equals the expression's width, so the enclosing operator's width is
  unchanged — and removes a mask `e & (2^w - 1)` when `e` has width `w` and
  reads only inputs (whose values fit their widths).  `optCheck` is proved
  sound in `Tools/ShippingOptSoundness.lean`.
-/
import Sparkle.IR.AST
import Sparkle.IR.Semantics
import Sparkle.IR.Optimize
import Sparkle.IR.RegDedup
import Sparkle.IR.ReorderInvariance

namespace Sparkle.IR.OptCheck

open Sparkle.IR.AST
open Sparkle.IR.Semantics (WEnv widthOf)

deriving instance DecidableEq for Port

/-- The binary operators the check understands. -/
def isBinOp : Operator → Bool
  | .add | .sub | .mul | .and | .or | .xor => true
  | _ => false

/-- Normalise one expression against the definitions seen so far. `ins`: the
input names (values fit their declared widths). -/
def normE (we : WEnv) (ins : List String) (defs : List (String × Expr)) : Expr → Option Expr
  | .const v w => if 0 ≤ v ∧ v < ((2 ^ w : Nat) : Int) then some (.const v w) else none
  | .ref x =>
    match defs.lookup x with
    | some d => if we x = widthOf we d then some d else none
    | none => some (.ref x)
  | .op o [a, b] =>
    if isBinOp o then do
      let a' ← normE we ins defs a
      let b' ← normE we ins defs b
      match o, b' with
      | .and, .const m w =>
        if m = ((2 ^ w - 1 : Nat) : Int) ∧ widthOf we a' = w ∧
            (Sparkle.IR.Reorder.refsOf a').all (fun x => ins.contains x) then some a'
        else some (.op o [a', b'])
      | _, _ => some (.op o [a', b'])
    else none
  | _ => none

/-- Normalise a combinational body into `name ↦ normal form` (newest first). -/
def normBody (we : WEnv) (ins : List String) :
    List (String × Expr) → List Stmt → Option (List (String × Expr))
  | defs, [] => some defs
  | defs, .assign l r :: rest => do
    let e ← normE we ins defs r
    normBody we ins ((l, e) :: defs) rest
  | _, _ :: _ => none

/-- Accept `o` as an optimisation of `m`: same ports, and every output
normalises to the same expression, which reads only inputs declared with the
same width in both modules (`o`'s normalisation trusts only those inputs). -/
def optCheck (m o : Module) : Bool :=
  let ins := m.inputs.map (·.name)
  let wm := Sparkle.IR.RegDedup.declWidth m
  let wo := Sparkle.IR.RegDedup.declWidth o
  let insO := ins.filter (fun x => wm x == wo x)
  match normBody wm ins [] m.body, normBody wo insO [] o.body with
  | some dm, some dO =>
    decide (o.inputs = m.inputs) && decide (o.outputs = m.outputs) &&
    m.outputs.all fun p =>
      match dm.lookup p.name, dO.lookup p.name with
      | some em, some eo =>
        decide (em = eo) && (Sparkle.IR.Reorder.refsOf em).all (fun x => insO.contains x)
      | _, _ => false
  | _, _ => false

/-- The statement shapes the synthesis entry produces: an `assign` of a
constant, a reference, or one of the six operators on two references. -/
def simpleRhs : Expr → Bool
  | .const _ _ => true
  | .ref _ => true
  | .op o [.ref _, .ref _] => isBinOp o
  | _ => false

def simpleBody (m : Module) : Bool :=
  m.body.all fun st => match st with
    | .assign _ r => simpleRhs r
    | _ => false

/-- `optimizeModule`, result-checked on modules of simple shape: there the
optimised module is kept only if `optCheck` accepts it, else the input module
is returned unoptimised. Other modules get `optimizeModule` unchanged. -/
def checkedOptimize (m : Module) : Module :=
  let o := Sparkle.IR.Optimize.optimizeModule m
  if simpleBody m then
    if optCheck m o then o else m
  else o

end Sparkle.IR.OptCheck
