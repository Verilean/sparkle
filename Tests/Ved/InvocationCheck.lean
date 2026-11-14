import Tools.VedInvocation
import Sparkle.Compiler.Elab

/-!
# Checks for `#ved_u1_write` (the `#writeDesign` argument form) and the chunked input domain

* positives: the command with and without the wires constant checks the ORIGINAL declaration:
  the stored theorem is `U1Stmt decl.ved_contract decl.ved_mod @decl` (compared with `==`),
  standard axioms only, and the module in `decl.ved_mod` is the module of the design
  `synthesizeHierarchical decl` (what `#writeDesign` synthesizes);
* must-stay-refused controls: the same argument form on a packed multi-output declaration and on
  a structure-valued declaration is refused exactly like `#ved_u1`, leaving no checker constant;
* a 13-bit input domain (two chunks of 2^12, `Tools/VedInvocationDom.lean`).
-/

namespace Tests.Ved.InvocationCheck

open Lean Elab Command Term Meta
open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.VedU1Contract Tools.VedU1Entry

def inc (a : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  a + (Signal.pure 1#8 : Signal defaultDomain (BitVec 8))

def andOr (a b : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  (a &&& b) ||| (a ^^^ b)

def wiresC : Array String := #["_gen_x"]

def twoOut (a b : Signal defaultDomain (BitVec 8)) :
    Signal defaultDomain (BitVec 8 × BitVec 8) := bundle2 a b

def delay1 (a : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  Signal.register 0#8 a

def wide13 (c : Signal defaultDomain (BitVec 13)) : Signal defaultDomain Bool :=
  let one : Signal defaultDomain (BitVec 13) := Signal.pure 1#13
  ((c &&& one) ^^^ ((c >>> (Signal.pure 12#13 : Signal defaultDomain (BitVec 13))) &&& one)) ===
    (Signal.pure 0#13 : Signal defaultDomain (BitVec 13))

#writeDesign inc ".lake/build/gen/inv/inc.sv" ".lake/build/gen/inv/inc_cppsim.h"
#writeDesign andOr ".lake/build/gen/inv/andor.sv" ".lake/build/gen/inv/andor_cppsim.h" wiresC

#guard_msgs (drop info) in
#ved_u1_write inc ".lake/build/gen/inv/inc.sv" ".lake/build/gen/inv/inc_cppsim.h"
#guard_msgs (drop info) in
#ved_u1_write andOr ".lake/build/gen/inv/andor.sv" ".lake/build/gen/inv/andor_cppsim.h" wiresC
#guard_msgs (drop info) in
#ved_u1_write wide13 ".lake/build/gen/inv/w.sv" ".lake/build/gen/inv/w_cppsim.h"

/-- the stored statement, the axioms, and that `ved_mod` is the `#writeDesign` module -/
def checkWritten (decl : Name) : CommandElabM Unit := liftTermElabM do
  let nm := Names.ofBase decl
  let stmt := Lean.mkConst decl
  let expected := mkAppN (Lean.mkConst ``U1Stmt) #[Lean.mkConst nm.contract, Lean.mkConst nm.mod, stmt]
  let some (.thmInfo ti) := (← getEnv).find? nm.thm | throwError "{nm.thm} is not a theorem"
  unless ti.type == expected do throwError "{nm.thm}: stored type differs"
  let ax ← collectAxioms nm.thm
  unless ax.all ([``propext, ``Classical.choice, ``Quot.sound].contains ·) do throwError "axioms {ax}"
  let design ← Sparkle.Compiler.Elab.synthesizeHierarchical decl
  let some (.defnInfo di) := (← getEnv).find? nm.mod | throwError "no ved_mod"
  unless design.modules.any (fun m => di.value == toExpr m) do
    throwError "{decl}: ved_mod is not a module of the #writeDesign design"
  logInfo m!"written OK {decl}"

/-- info: written OK Tests.Ved.InvocationCheck.inc -/
#guard_msgs in
run_cmd checkWritten ``inc

/-- info: written OK Tests.Ved.InvocationCheck.andOr -/
#guard_msgs in
run_cmd checkWritten ``andOr

/-- info: written OK Tests.Ved.InvocationCheck.wide13 -/
#guard_msgs in
run_cmd checkWritten ``wide13

/-! ## Controls: the same command form is refused like `#ved_u1`, nothing left behind -/

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
  for n in [`ved_mod, `ved_contract, `ved_outs, `ved_body, `ved_u1] do
    if (← getEnv).contains (decl ++ n) then throwError "left behind: {n}"
  logInfo m!"refused [{stage}], clean"

structure PO where
  x : Signal defaultDomain (BitVec 8)
  y : Signal defaultDomain (BitVec 8)

def twoField (a b : Signal defaultDomain (BitVec 8)) : PO := { x := a &&& b, y := a ||| b }

/-- info: refused [multi-output], clean -/
#guard_msgs in
run_cmd do
  expectWriteRefused "multi-output" ``twoOut
    (elabCommand (← `(#ved_u1_write twoOut ".lake/build/gen/inv/t.sv" ".lake/build/gen/inv/t_cppsim.h" wiresC)))

/-- info: refused [table], clean -/
#guard_msgs in
run_cmd do
  expectWriteRefused "table" ``twoField
    (elabCommand (← `(#ved_u1_write twoField ".lake/build/gen/inv/f.sv" ".lake/build/gen/inv/f_cppsim.h")))

/-! ## Domain width controls: one input of 12 (plain decide), 16 (chunked), 32 and 64 bits (symbolic) -/

def eq12 (c : Signal defaultDomain (BitVec 12)) : Signal defaultDomain Bool :=
  c === (Signal.pure 5#12 : Signal defaultDomain (BitVec 12))

def eq16 (c : Signal defaultDomain (BitVec 16)) : Signal defaultDomain Bool :=
  c === (Signal.pure 5#16 : Signal defaultDomain (BitVec 16))

def mask32 (a : Signal defaultDomain (BitVec 32)) : Signal defaultDomain (BitVec 32) :=
  (a &&& (Signal.pure 0xFF00FF#32 : Signal defaultDomain (BitVec 32))) +
    (Signal.pure 0x1234#32 : Signal defaultDomain (BitVec 32))

def add64 (a : Signal defaultDomain (BitVec 64)) : Signal defaultDomain (BitVec 64) :=
  a + (Signal.pure 3#64 : Signal defaultDomain (BitVec 64))

#guard_msgs (drop info) in
#ved_u1 eq12
#guard_msgs (drop info) in
#ved_u1 eq16
#guard_msgs (drop info) in
#ved_u1 mask32
#guard_msgs (drop info) in
#ved_u1 add64

def checkStored (decl : Name) : CommandElabM Unit := liftTermElabM do
  let nm := Names.ofBase decl
  let expected := mkAppN (Lean.mkConst ``U1Stmt) #[Lean.mkConst nm.contract, Lean.mkConst nm.mod, Lean.mkConst decl]
  let some (.thmInfo ti) := (← getEnv).find? nm.thm | throwError "{nm.thm} is not a theorem"
  unless ti.type == expected do throwError "{nm.thm}: stored type differs"
  let ax ← collectAxioms nm.thm
  unless ax.all ([``propext, ``Classical.choice, ``Quot.sound].contains ·) do throwError "axioms {ax}"
  logInfo m!"stored OK {decl}"

/-- info: stored OK Tests.Ved.InvocationCheck.eq12 -/
#guard_msgs in
run_cmd checkStored ``eq12

/-- info: stored OK Tests.Ved.InvocationCheck.eq16 -/
#guard_msgs in
run_cmd checkStored ``eq16

/-- info: stored OK Tests.Ved.InvocationCheck.mask32 -/
#guard_msgs in
run_cmd checkStored ``mask32

/-- info: stored OK Tests.Ved.InvocationCheck.add64 -/
#guard_msgs in
run_cmd checkStored ``add64

end Tests.Ved.InvocationCheck
