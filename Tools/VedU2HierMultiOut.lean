import Tools.VedU2HierReg

/-!
# `U2HRStmtK`: the hierarchical statement for children with k ≥ 1 outputs (CANDIDATE, not reviewed)

`U2HRStmt` (Tools/VedU2HierReg.lean) is unchanged and is false for a design with a child that has
two or more outputs, because `HierShapeS` -> `connsOkS` contains `c.outputs.length == 1`.  This file
adds a SEPARATE statement for the wider shape (user decision 2026-11-23, option 3).

* `connsOkK` is `connsOkS` with `c.outputs.length == 1` replaced by `1 ≤ c.outputs.length`, plus two
  clauses that are trivial for one output: the child's output port names are pairwise distinct, and
  the parent wires the child's outputs are connected to are pairwise distinct.
  NO OUTPUT IS DROPPED: the clause `(c.inputs ++ c.outputs).all (fun p => cs.any (· .1 == p.name))`
  (already in `connsOkS`) requires every input AND every output port to be connected, the clause
  `cs.all (… .ref x …)` requires each connection to be a plain wire, and its width test requires
  `declWidth m x == p.ty.bitWidth` (each output wire has the width of its port).
* `HierShapeK` is `HierShapeS` with `connsOkK` (every other clause is the same).
* `U2HRStmtK` is `U2HRStmt` with `HierShapeS d m = true` replaced by `HierShapeK d m = true`; every
  other conjunct is the SAME definition (`CorrStmt`, `ShapeCore`, `designClkRst`, `WidthStmt`,
  `OrderHS`, `OrderStmt`, `AdmArr`, `OutputsStmtHS`), none of which mentions the number of a child's
  outputs: the semantics (`instEvalS`, `outWrites`, `instOuts`/`wrH`) already writes EVERY connected
  output port (`outWrites` filters the connections on all output ports; the order check writes all
  output refs, so a parent wire written by two outputs / instances is refused by `WOH`).
-/

namespace Tools.VedU2Hier

open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics Sparkle.IR.Reorder
open Tools.VedU1Contract Tools.VedU1Hier

/-- The parent wires the child's output ports are connected to (a connection of an output port to
anything but a plain wire is refused by `connsOkK`). -/
def outRefNames (c : Module) (cs : List (String × Expr)) : List String :=
  (cs.filter (fun q => c.outputs.any (·.name == q.1))).filterMap fun q =>
    match q.2 with
    | .ref x => some x
    | _ => none

/-- One `inst` against the design, k ≥ 1 outputs: `connsOkS` with `c.outputs.length == 1` replaced
by `1 ≤ c.outputs.length`, distinct output port names and distinct output wires added. -/
def connsOkK (d : Design) (m : Module) (mn : String) (cs : List (String × Expr)) : Bool :=
  match findMod d mn with
  | none => false
  | some c =>
    !c.isPrimitive && c.parameters.isEmpty && c.assertions.isEmpty && leafBody c.body &&
    childSane c &&
    decide (1 ≤ c.outputs.length) && decide (c.outputs.map (·.name)).Nodup &&
    decide (outRefNames c cs).Nodup &&
    decide (cs.map (·.1)).Nodup &&
    (c.inputs ++ c.outputs).all (fun p => cs.any (fun q => q.1 == p.name)) &&
    cs.all (fun q => (c.inputs ++ c.outputs).any (fun p => p.name == q.1)) &&
    cs.all (fun q => match q.2 with
      | .ref x => (c.inputs ++ c.outputs).any
          (fun p => p.name == q.1 && scalar p.ty &&
            (declWidth m x == p.ty.bitWidth || isClkRstPort c p.name))
      | _ => false)

/-- `HierShapeS` with `connsOkK`. -/
def HierShapeK (d : Design) (m : Module) : Bool :=
  d.topModule == m.name && decide (d.modules.map (·.name)).Nodup &&
  !((d.modules.map (·.name)).contains m.name) &&
  m.body.all isAsgInstReg &&
  m.body.all (fun s => match s with
    | .inst mn _ cs => connsOkK d m mn cs
    | _ => true) &&
  decide (instNames m.body).Nodup &&
  d.modules.all (fun c => m.body.any (fun s => match s with
    | .inst mn _ _ => mn == c.name
    | _ => false)) &&
  clkRstOk d m

/-- CANDIDATE statement for a parent with registers whose children have one or more outputs:
`U2HRStmt` with `HierShapeS d m = true` replaced by `HierShapeK d m = true`. -/
def U2HRStmtK (c : Contract) (m : Module) (d : Design) (f : c.table.Ty) : Prop :=
  CorrStmt c ∧ ShapeCore c m ∧ c.clkRst = designClkRst d m ∧ HierShapeK d m = true ∧
  WidthStmt c m ∧ OrderHS d m ∧ (∀ x ∈ d.modules, OrderStmt x) ∧
  (∃ arr, AdmArr d m arr) ∧ OutputsStmtHS c m d f

end Tools.VedU2Hier
