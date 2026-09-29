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
import Sparkle.IR.PrintCheck

namespace Sparkle.IR.OptCheck

open Sparkle.IR.AST
open Sparkle.IR.Semantics (WEnv widthOf)

deriving instance DecidableEq for Port

/-- The binary operators the check understands. -/
def isBinOp : Operator → Bool
  | .add | .sub | .mul | .and | .or | .xor => true
  | _ => false

/-- Source/printing operators include logical shifts. The normalizer deliberately
remains smaller: a shift-bearing original cannot pass `optCheckCore`, so the
checked route retains that original rather than accepting an unchecked result. -/
def isPrintBinOp (op : Operator) : Bool := isBinOp op || op == .shr || op == .shl

/-- Comparison nodes admitted to the checked route. Their semantic
normalization is not yet supported, so the original module is retained. -/
def isControlBinOp : Operator → Bool
  | .eq | .lt_u | .le_u | .gt_u | .ge_u | .lt_s | .le_s | .gt_s | .ge_s => true
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
def optCheckCore (m o : Module) : Bool :=
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

/-- Concrete declarations supported by the proved module renderer. This
checks syntax/metadata only, not identifiers or expression width agreement. -/
def printDeclsCheck (m : Module) : Bool :=
  !m.isPrimitive && m.parameters.isEmpty &&
    (m.inputs ++ m.outputs ++ m.wires).all fun p => match p.ty with
      | .bit => true
      | .bitVector n => 0 < n
      | _ => false

/-- Preserve printable declarations and the uniform-width printing check
when the input already satisfies them. The normal-form check alone says
nothing about unused assignments' widths or unused inputs' width lookups.
The input-width check preserves initialization for every supplied input.
Failing candidates use the
existing unchanged fallback. Inputs outside the printing fragment retain
the previous acceptance policy. -/
def optCheck (m o : Module) : Bool :=
  optCheckCore m o && ((!printDeclsCheck m || printDeclsCheck o) &&
    (!PrintCheck.moduleCheck m ||
      (PrintCheck.moduleCheck o && PrintCheck.inputWidthsAgree m o)))

/-- The statement shapes the synthesis entry produces: an `assign` of a
constant, a reference, or one of the six normalizer operators or logical
left/right shift or unsigned comparison on two references, or a mux on
three references. -/
def simpleRhs : Expr → Bool
  | .const _ _ => true
  | .ref _ => true
  | .op o [.ref _, .ref _] => isPrintBinOp o || isControlBinOp o
  | .op .mux [.ref _, .ref _, .ref _] => true
  | .concat [.const _ _, .ref _] => true
  | .slice (.concat [.const 0 w, .ref _]) hi lo => lo == 0 && hi + 1 == w
  | _ => false

def simpleBody (m : Module) : Bool :=
  m.body.all fun st => match st with
    | .assign _ r => simpleRhs r
    | _ => false

/-- Topological, single-assignment order for combinational bodies. External
names are permitted; targets cannot read themselves or be assigned again.
This structural check is proved equivalent to Acyclic in the proof layer. -/
def assignmentOrderCheck : List Stmt → Bool
  | [] => true
  | .assign l r :: rest =>
    let later := Sparkle.IR.Reorder.writesOf rest
    !later.contains l &&
      (Sparkle.IR.Reorder.refsOf r).all (fun x => x != l && !later.contains x) &&
      assignmentOrderCheck rest
  | _ => false

/-- `optimizeModule`, result-checked on modules of simple shape: there the
optimised module is kept only if `optCheck` and the assignment-order check
accept it, else the input module
is returned unoptimised. Other modules get `optimizeModule` unchanged. -/
def checkedOptimize (m : Module) : Module :=
  let o := Sparkle.IR.Optimize.optimizeModule m
  if simpleBody m then
    if optCheck m o && assignmentOrderCheck o.body then o else m
  else o

/-! ## Sequential rename-equivalence check

A sequential module (assigns + registers) is accepted as equivalent to
another when the registers correspond in body order — same clock, reset,
kind, initial value and declared width, with outputs possibly renamed —
and, treating register outputs as extra inputs (their values fit their
widths: `regNexts` masks every update), the assign segments normalise so
that every module output and every register's next-value expression agree
under the register renaming. The checker takes no part in the pipeline; it
is the decidable premise of the sequential printed-SV soundness theorems
and a regression gate over the certified register shapes. -/

/-- `normE` extended with the three-argument mux node the register cones
carry. Only the sequential checker uses it: the combinational checked route
keeps the original acceptance policy. -/
def seqNormE (we : WEnv) (ins : List String) (defs : List (String × Expr)) : Expr → Option Expr
  | .const v w => if 0 ≤ v ∧ v < ((2 ^ w : Nat) : Int) then some (.const v w) else none
  | .ref x =>
    match defs.lookup x with
    | some d => if we x = widthOf we d then some d else none
    | none => some (.ref x)
  | .op .mux [c, a, b] => do
    let c' ← seqNormE we ins defs c
    let a' ← seqNormE we ins defs a
    let b' ← seqNormE we ins defs b
    some (.op .mux [c', a', b'])
  | .op o [a, b] =>
    if isBinOp o then do
      let a' ← seqNormE we ins defs a
      let b' ← seqNormE we ins defs b
      match o, b' with
      | .and, .const mv w =>
        if mv = ((2 ^ w - 1 : Nat) : Int) ∧ widthOf we a' = w ∧
            (Sparkle.IR.Reorder.refsOf a').all (fun x => ins.contains x) then some a'
        else some (.op o [a', b'])
      | _, _ => some (.op o [a', b'])
    else none
  | _ => none

/-- `normBody` over `seqNormE`. -/
def seqNormBody (we : WEnv) (ins : List String) :
    List (String × Expr) → List Stmt → Option (List (String × Expr))
  | defs, [] => some defs
  | defs, .assign l r :: rest => do
    let e ← seqNormE we ins defs r
    seqNormBody we ins ((l, e) :: defs) rest
  | _, _ :: _ => none

/-- The registers of a body, in order: (out, clock, reset, input, init). -/
def seqRegs (m : Module) : List (String × String × (String × Sparkle.IR.Type.ResetKind)
    × Expr × Int) :=
  m.body.filterMap fun st => match st with
    | .register o c rk i iv => some (o, c, rk, i, iv)
    | _ => none

/-- The assign segment of a body, in order. -/
def seqAssigns (m : Module) : List Stmt :=
  m.body.filter fun st => match st with
    | .assign .. => true
    | _ => false

def seqOptCheck (m o : Module) : Bool :=
  let rM := seqRegs m
  let rO := seqRegs o
  let pairs := List.zip rM rO
  let wm := Sparkle.IR.RegDedup.declWidth m
  let wo := Sparkle.IR.RegDedup.declWidth o
  (rM.length == rO.length && decide (o.inputs = m.inputs) &&
    decide (o.outputs = m.outputs) &&
    pairs.all (fun pr =>
      match pr with
      | ((nm, cm, km, _, vm), (no, co, ko, _, vo)) =>
        cm == co && km.1 == ko.1 && decide (km.2 = ko.2) && vm == vo &&
        wm nm == wo no && decide (0 < wm nm))) &&
  (let subst : Std.HashMap String String := pairs.foldl
    (fun h pr => match pr with
      | ((nm, _), (no, _)) => h.insert no nm) {}
   let renO := Sparkle.IR.Optimize.renameRefs subst
   let insBase := m.inputs.map (·.name)
   let insM := insBase ++ rM.map (·.1)
   let insO := insBase.filter (fun x => wm x == wo x) ++ rO.map (·.1)
   match seqNormBody wm insM [] (seqAssigns m), seqNormBody wo insO [] (seqAssigns o) with
   | some dm, some dO =>
     (m.outputs.all fun p =>
       match dm.lookup p.name, dO.lookup p.name with
       | some em, some eo =>
         decide (em = renO eo) &&
           (Sparkle.IR.Reorder.refsOf em).all (fun x => insM.contains x)
       | _, _ => false) &&
     pairs.all (fun pr =>
       match pr with
       | ((_, _, _, im, _), (_, _, _, io, _)) =>
         match seqNormE wm insM dm im, seqNormE wo insO dO io with
         | some fm, some fo =>
           decide (fm = renO fo) &&
             (Sparkle.IR.Reorder.refsOf fm).all (fun x => insM.contains x)
         | _, _ => false)
   | _, _ => false)

end Sparkle.IR.OptCheck
