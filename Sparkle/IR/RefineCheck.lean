/-
  Result check for the module-level passes on assign + register modules.

  `mergeDuplicates` and `optimizeModule` are multi-phase passes; rather than
  prove them directly, their result is treated as an untrusted proposal, as
  `Sparkle.IR.OptCheck.optCheck` does for small combinational modules and
  `seqOptCheck` for the single-cone register shapes.  `refineCheck m o`
  accepts `o` as a refinement of `m` for every module made of `assign`s and
  registers — the modules the state-machine route emits:

  * the same ports; every register of `o` is a register of `m`, by NAME, with
    the same clock, reset, reset value and width (a register of `m` that `o`
    does not have was dead: nothing `o` shows reads it);
  * every output and every next-value expression of an `o` register
    normalises, in both modules, to the SAME expression over the inputs and
    the register outputs.

  The normal forms cover what those modules contain — the two-operand
  operators, shifts and comparisons, NOT and negation, a mux, a two-part
  concatenation, a part-select — and normalisation does what the optimizer
  does to them:

  * a wire is replaced by its (normalised) definition, when its declared
    width is the definition's;
  * `e & (2^w - 1)` is `e` when `e` has width `w` and reads fitting names
    only; `e & 0` is `0`;
  * `c ? 1'd1 : 1'd0` is `c` when `c` is one bit wide;
  * a part-select of `{a, b}` inside `a` or inside `b` is that part-select of
    `a` or `b`; a part-select of the whole expression is the expression; a
    part-select of a constant is a constant.

  Normal forms are TREES over the inputs and registers: a module whose
  wires form a deep, wide DAG has large ones.  The check is a decidable
  premise (and a regression gate over the corpus), not a compile-time pass.

  `refineCheck` is proved sound in `Tools/ShippingRefineSoundness.lean`.
-/
import Sparkle.IR.OptCheck

namespace Sparkle.IR.RefineCheck

open Sparkle.IR.AST
open Sparkle.IR.Semantics (WEnv widthOf mask)
open Sparkle.IR.OptCheck (seqRegs seqAssigns seqStmtOk)
open Sparkle.IR.Reorder (refsOf)

/-- The two-operand operators of the normal forms. -/
def rBinOk : Operator → Bool
  | .add | .sub | .mul | .and | .or | .xor | .shl | .shr
  | .eq | .lt_u | .le_u | .gt_u | .ge_u | .lt_s | .le_s | .gt_s | .ge_s => true
  | _ => false

/-- The one-operand operators of the normal forms. -/
def rUnOk : Operator → Bool
  | .not | .neg => true
  | _ => false

/-- A two-operand node, with the optimizer's two simplifications of `&`. -/
def rBin (we : WEnv) (ins : List String) (o : Operator) (a b : Expr) : Expr :=
  match o, b with
  | .and, .const mv w =>
    if mv = ((2 ^ w - 1 : Nat) : Int) ∧ widthOf we a = w ∧
        (refsOf a).all (fun x => ins.contains x) then a
    else if mv = 0 then .const 0 (max (widthOf we a) w)
    else .op o [a, b]
  | _, _ => .op o [a, b]

/-- A mux node; `c ? 1'd1 : 1'd0` on a one-bit `c` reading fitting names is
`c`.  Branches of different widths have no normal form. -/
def rMux (we : WEnv) (ins : List String) (c a b : Expr) : Option Expr :=
  if a = .const 1 1 ∧ b = .const 0 1 ∧ widthOf we c = 1 ∧
      (refsOf c).all (fun x => ins.contains x) then some c
  else if widthOf we a = widthOf we b then some (.op .mux [c, a, b]) else none

/-- The part-select `e[hi:lo]` of a normal form. -/
def rSlice (we : WEnv) : Expr → Nat → Nat → Expr
  | .concat [a, b], hi, lo =>
    if lo = 0 ∧ hi + 1 = widthOf we a + widthOf we b then .concat [a, b]
    else if widthOf we b ≤ lo then rSlice we a (hi - widthOf we b) (lo - widthOf we b)
    else if hi < widthOf we b then rSlice we b hi lo
    else .slice (.concat [a, b]) hi lo
  | .const v w, hi, lo =>
    if lo = 0 ∧ hi + 1 = w then .const v w
    else .const (Int.ofNat (mask (hi - lo + 1) (v.toNat >>> lo))) (hi - lo + 1)
  | e, hi, lo => if lo = 0 ∧ hi + 1 = widthOf we e then e else .slice e hi lo

/-- Normalise one expression against the definitions seen so far. `ins`: the
names whose values fit their declared widths (inputs and register outputs). -/
def rNormE (we : WEnv) (ins : List String) (defs : List (String × Expr)) : Expr → Option Expr
  | .const v w => if 0 ≤ v ∧ v < ((2 ^ w : Nat) : Int) then some (.const v w) else none
  | .ref x =>
    match defs.lookup x with
    | some d => if we x = widthOf we d then some d else none
    | none => some (.ref x)
  | .op .mux [c, a, b] => do
    let c' ← rNormE we ins defs c
    let a' ← rNormE we ins defs a
    let b' ← rNormE we ins defs b
    rMux we ins c' a' b'
  | .op o [a, b] =>
    if rBinOk o then do
      let a' ← rNormE we ins defs a
      let b' ← rNormE we ins defs b
      some (rBin we ins o a' b')
    else none
  | .op o [a] =>
    if rUnOk o then do
      let a' ← rNormE we ins defs a
      some (.op o [a'])
    else none
  | .concat [a, b] => do
    let a' ← rNormE we ins defs a
    let b' ← rNormE we ins defs b
    some (.concat [a', b'])
  | .slice e hi lo => do
    let e' ← rNormE we ins defs e
    if (refsOf e').all (fun x => ins.contains x) then some (rSlice we e' hi lo) else none
  | _ => none

/-- Normalise the assign segment of a body into `name ↦ normal form`
(newest first). -/
def rNormBody (we : WEnv) (ins : List String) :
    List (String × Expr) → List Stmt → Option (List (String × Expr))
  | defs, [] => some defs
  | defs, .assign l r :: rest => do
    let e ← rNormE we ins defs r
    rNormBody we ins ((l, e) :: defs) rest
  | _, _ :: _ => none

/-- The register of `m` with the name of a register of `o`. -/
def regOf (rM : List (String × String × (String × Sparkle.IR.Type.ResetKind) × Expr × Int))
    (name : String) :
    Option (String × String × (String × Sparkle.IR.Type.ResetKind) × Expr × Int) :=
  rM.find? (fun r => r.1 == name)

/-- Accept `o` as a refinement of `m` (see the file comment). -/
def refineCheck (m o : Module) : Bool :=
  let rM := seqRegs m
  let rO := seqRegs o
  let wm := Sparkle.IR.RegDedup.declWidth m
  let wo := Sparkle.IR.RegDedup.declWidth o
  let insBase := m.inputs.map (·.name)
  let insM := insBase ++ rM.map (·.1)
  let insO := insBase.filter (fun x => wm x == wo x) ++ rO.map (·.1)
  (decide (o.inputs = m.inputs) && decide (o.outputs = m.outputs) &&
    m.body.all seqStmtOk && o.body.all seqStmtOk &&
    decide ((rM.map (·.1)).Nodup) && decide ((rO.map (·.1)).Nodup) &&
    rM.all (fun r => !insBase.contains r.1 && r.1 != "rst") &&
    rO.all (fun r => !insBase.contains r.1 && r.1 != "rst") &&
    (seqAssigns m).all (fun st => match st with
      | .assign l _ => l != "rst"
      | _ => true) &&
    (seqAssigns o).all (fun st => match st with
      | .assign l _ => l != "rst"
      | _ => true) &&
    rO.all (fun ro =>
      match regOf rM ro.1 with
      | some rm =>
        rm.2.1 == ro.2.1 && rm.2.2.1.1 == "rst" && ro.2.2.1.1 == "rst" &&
          decide (rm.2.2.1.2 = ro.2.2.1.2) && rm.2.2.2.2 == ro.2.2.2.2 &&
          wm rm.1 == wo ro.1 && decide (0 < wm rm.1)
      | none => false) &&
    rM.all (fun rm => rm.2.2.1.1 == "rst" && decide (0 < wm rm.1))) &&
  (match rNormBody wm insM [] (seqAssigns m), rNormBody wo insO [] (seqAssigns o) with
   | some dm, some dO =>
     (m.outputs.all fun p =>
       match dm.lookup p.name, dO.lookup p.name with
       | some em, some eo =>
         decide (em = eo) && (refsOf eo).all (fun x => insO.contains x)
       | _, _ => false) &&
     rO.all (fun ro =>
       match regOf rM ro.1 with
       | some rm =>
         (match rNormE wm insM dm rm.2.2.2.1, rNormE wo insO dO ro.2.2.2.1 with
          | some fm, some fo =>
            decide (fm = fo) && (refsOf fo).all (fun x => insO.contains x)
          | _, _ => false)
       | none => false) &&
     -- every register of `m` has a next value (the dropped ones too)
     rM.all (fun rm => (rNormE wm insM dm rm.2.2.2.1).isSome)
   | _, _ => false)

end Sparkle.IR.RefineCheck
