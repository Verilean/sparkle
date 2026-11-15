import Tools.VedWriteForms
import Sparkle.Core.CircuitMonad
import Sparkle.Core.CircuitDo

/-!
# Checks for the `#writeDesign` argument forms of the packed / hierarchical entries

`#ved_u1_packed_write`, `#ved_u1_hier_write` and `#ved_u2_hier_write` take the argument list of
`#writeDesign decl "x.sv" "x_cppsim.h" [wires]` (paths and wires constant unused) and run the body of
`#ved_u1_packed` / `#ved_u1_hier` / `#ved_u2_hier`.  The small examples here are NOT part of the 327
inventory rows.

* POSITIVES (each after the original `#writeDesign` on the same declaration, with and without the
  wires constant): the registered theorem has EXACTLY the entry's statement over the declaration
  (`PackedStmt` / `U1HStmt` / `U2HStmt`, compared with `==`), the axioms are the standard three, and the
  artifact checked is the artifact `#writeDesign` writes: `ved_mod` is the module and `ved_design` the
  design that `synthesizeHierarchical decl` returns (the design of `synthesizeCombinational` plus the
  returned module).
* CONTROLS (the same command forms are refused exactly like the entry commands, leaving no `ved_*`
  constant): `#ved_u1_packed_write` on a one-output declaration `[packed]`; `#ved_u1_hier_write` and
  `#ved_u2_hier_write` on a packed declaration `[multi-output]`.
-/

namespace Tests.Ved.WriteFormsCheck

open Lean Elab Command Term Meta
open Sparkle.IR.AST Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.Core
open Tools.VedU1Contract Tools.VedU1Entry Tools.VedU1Hier Tools.VedU1HierEntry Tools.VedU2Hier

/-! ## Declarations -/

def wiresC : Array String := #["_gen_x"]

/-- a packed two-field result (field 0 = 8 bits high, field 1 = 4 bits low) -/
def pk2 (a : Signal defaultDomain (BitVec 8)) (b : Signal defaultDomain (BitVec 4)) :
    Signal defaultDomain (BitVec 8 × BitVec 4) := bundle2 (~~~a) b

def pk2b (a : Signal defaultDomain (BitVec 8)) (b : Signal defaultDomain (BitVec 4)) :
    Signal defaultDomain (BitVec 8 × BitVec 4) := bundle2 (a &&& (Signal.pure 15#8 : Signal defaultDomain (BitVec 8))) b

def one (a : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) := ~~~a

/-- combinational children and parent (asymmetric, so a miswiring is observable) -/
@[hardware_module] def wA (x y : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  x - y

@[hardware_module] def wB (x y : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  (x ^^^ y) - y

def hpar (a b c : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  let p := wA a b
  let q := wA b c
  wB p q

def hpar2 (a b c : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  let p := wA a b
  let q := wA b c
  wB p q

/-- a register child and a register-free parent of it -/
@[hardware_module]
def accMod (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg (0#8)
    let a := (r : Signal defaultDomain (BitVec 8))
    r <~ a + x
    return a

@[hardware_module]
def parTwo (a b : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  let p := accMod a
  let q := accMod b
  p - q + a

@[hardware_module]
def parTwo2 (a b : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  let p := accMod a
  let q := accMod b
  p - q + a

#verify_elab_deep accMod

#writeDesign pk2 ".lake/build/gen/wf/pk2.sv" ".lake/build/gen/wf/pk2_cppsim.h"
#writeDesign pk2b ".lake/build/gen/wf/pk2b.sv" ".lake/build/gen/wf/pk2b_cppsim.h" wiresC
#writeDesign hpar ".lake/build/gen/wf/hpar.sv" ".lake/build/gen/wf/hpar_cppsim.h" wiresC
#writeDesign hpar2 ".lake/build/gen/wf/hpar2.sv" ".lake/build/gen/wf/hpar2_cppsim.h"
#writeDesign parTwo ".lake/build/gen/wf/parTwo.sv" ".lake/build/gen/wf/parTwo_cppsim.h" wiresC
#writeDesign parTwo2 ".lake/build/gen/wf/parTwo2.sv" ".lake/build/gen/wf/parTwo2_cppsim.h"

#guard_msgs (drop info) in
#ved_u1_packed_write pk2 ".lake/build/gen/wf/pk2.sv" ".lake/build/gen/wf/pk2_cppsim.h"
#guard_msgs (drop info) in
#ved_u1_packed_write pk2b ".lake/build/gen/wf/pk2b.sv" ".lake/build/gen/wf/pk2b_cppsim.h" wiresC
#guard_msgs (drop info) in
#ved_u1_hier_write hpar ".lake/build/gen/wf/hpar.sv" ".lake/build/gen/wf/hpar_cppsim.h" wiresC
#guard_msgs (drop info) in
#ved_u1_hier_write hpar2 ".lake/build/gen/wf/hpar2.sv" ".lake/build/gen/wf/hpar2_cppsim.h"
#guard_msgs (drop info) in
#ved_u2_hier_write parTwo ".lake/build/gen/wf/parTwo.sv" ".lake/build/gen/wf/parTwo_cppsim.h" wiresC
#guard_msgs (drop info) in
#ved_u2_hier_write parTwo2 ".lake/build/gen/wf/parTwo2.sv" ".lake/build/gen/wf/parTwo2_cppsim.h"

/-! ## Positives: exact statement, standard axioms, the `#writeDesign` artifact -/

def std3 : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- `ved_mod` is the returned module, `ved_design` the design of `synthesizeCombinational`, and every
module of the `#writeDesign` design (`synthesizeHierarchical`) is one of them. -/
def sameArtifact (decl : Name) (hier : Bool) : TermElabM Unit := do
  let nm := Names.ofBase decl
  let some (.defnInfo di) := (← getEnv).find? nm.mod | throwError "{decl}: no ved_mod"
  let design ← Sparkle.Compiler.Elab.synthesizeHierarchical decl
  let (m, d0) ← Sparkle.Compiler.Elab.synthesizeCombinational decl
  unless di.value == toExpr m do throwError "{decl}: ved_mod is not the returned module"
  unless design.modules.any (fun x => di.value == toExpr x) do
    throwError "{decl}: ved_mod is not a module of the #writeDesign design"
  if hier then
    let some (.defnInfo dd) := (← getEnv).find? (decl ++ `ved_design) | throwError "{decl}: no ved_design"
    unless dd.value == toExpr d0 do throwError "{decl}: ved_design is not the design of the synthesis"
    for x in design.modules do
      unless di.value == toExpr x || d0.modules.any (· == x) do
        throwError "{decl}: a #writeDesign module is neither ved_mod nor in ved_design"

def checkPacked (decl : Name) (stmtStx : Term) : CommandElabM Unit := liftTermElabM do
  let nm := Names.ofBase decl
  let stmt ← instantiateMVars (← Term.elabTerm stmtStx none)
  let expected := mkAppN (Lean.mkConst ``Tools.VedU1Packed.PackedStmt)
    #[Lean.mkConst nm.contract, Lean.mkConst nm.mod, stmt]
  let some (.thmInfo ti) := (← getEnv).find? nm.thm | throwError "{nm.thm} is not a theorem"
  unless ti.type == expected do throwError "{nm.thm}: stored type differs"
  let ax ← collectAxioms nm.thm
  unless ax.all (std3.contains ·) do throwError "axioms {ax}"
  sameArtifact decl false
  logInfo m!"written OK {decl}"

def checkHier (decl : Name) (u2 : Bool) : CommandElabM Unit := liftTermElabM do
  let nm := HNames.ofBase decl
  let stmt := Lean.mkConst decl
  let expected := mkAppN (Lean.mkConst (if u2 then ``U2HStmt else ``U1HStmt))
    #[Lean.mkConst nm.contract, Lean.mkConst nm.mod, Lean.mkConst nm.design, stmt]
  let some (.thmInfo ti) := (← getEnv).find? nm.thm | throwError "{nm.thm} is not a theorem"
  unless ti.type == expected do throwError "{nm.thm}: stored type differs"
  let ax ← collectAxioms nm.thm
  unless ax.all (std3.contains ·) do throwError "axioms {ax}"
  sameArtifact decl true
  logInfo m!"written OK {decl}"

/-- info: written OK Tests.Ved.WriteFormsCheck.pk2 -/
#guard_msgs in
run_cmd checkPacked ``pk2 (← `(pk2))

/-- info: written OK Tests.Ved.WriteFormsCheck.pk2b -/
#guard_msgs in
run_cmd checkPacked ``pk2b (← `(pk2b))

/-- info: written OK Tests.Ved.WriteFormsCheck.hpar -/
#guard_msgs in
run_cmd checkHier ``hpar false

/-- info: written OK Tests.Ved.WriteFormsCheck.hpar2 -/
#guard_msgs in
run_cmd checkHier ``hpar2 false

/-- info: written OK Tests.Ved.WriteFormsCheck.parTwo -/
#guard_msgs in
run_cmd checkHier ``parTwo true

/-- info: written OK Tests.Ved.WriteFormsCheck.parTwo2 -/
#guard_msgs in
run_cmd checkHier ``parTwo2 true

/-! ## Controls: refused like the entry commands, nothing left behind -/

def expectWriteRefused (stage : String) (decl : Name) (cmd : CommandElabM Unit) :
    CommandElabM Unit := do
  let msgs0 := (← get).messages
  cmd
  let after := (← get).messages
  let errs := after.toList.filter (·.severity == .error)
  modify fun s => { s with messages := msgs0 }
  let mut refused := false
  for e in errs do
    let t ← e.data.toString
    if t.startsWith "VED U1 REFUSED" && (t.splitOn s!"[{stage}]").length > 1 then refused := true
  unless refused do throwError "control ACCEPTED (expected a refusal at [{stage}])"
  for n in [`ved_mod, `ved_contract, `ved_outs, `ved_body, `ved_u1, `ved_design] do
    if (← getEnv).contains (decl ++ n) then throwError "left behind: {n}"
  logInfo m!"refused [{stage}], clean"

def pkCtl (a : Signal defaultDomain (BitVec 8)) (b : Signal defaultDomain (BitVec 4)) :
    Signal defaultDomain (BitVec 8 × BitVec 4) := bundle2 (~~~a) b

def pkCtl2 (a : Signal defaultDomain (BitVec 8)) (b : Signal defaultDomain (BitVec 4)) :
    Signal defaultDomain (BitVec 8 × BitVec 4) := bundle2 (~~~a) b

/-- info: refused [packed], clean -/
#guard_msgs in
run_cmd do
  expectWriteRefused "packed" ``one
    (elabCommand (← `(#ved_u1_packed_write one ".lake/build/gen/wf/o.sv" ".lake/build/gen/wf/o_cppsim.h" wiresC)))

/-- info: refused [multi-output], clean -/
#guard_msgs in
run_cmd do
  expectWriteRefused "multi-output" ``pkCtl
    (elabCommand (← `(#ved_u1_hier_write pkCtl ".lake/build/gen/wf/c.sv" ".lake/build/gen/wf/c_cppsim.h" wiresC)))

/-- info: refused [multi-output], clean -/
#guard_msgs in
run_cmd do
  expectWriteRefused "multi-output" ``pkCtl2
    (elabCommand (← `(#ved_u2_hier_write pkCtl2 ".lake/build/gen/wf/c2.sv" ".lake/build/gen/wf/c2_cppsim.h")))

end Tests.Ved.WriteFormsCheck
