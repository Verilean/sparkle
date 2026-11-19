import Sparkle
import Tools.VedU1Entry

/-!
# Check: the small regression causes of the U1 entry

Positives (one small body per cause): `Neg` of a signal; `Signal.fst` / `Signal.snd` of a bundled pair; a
three-operand chain through two half adders (24 input bits: the wide path, the high half of a concatenation);
`Signal.registerWithEnable`; an anonymous binder `(_ : Signal …)` (the port is `_gen_x`).
Controls (must stay refused at [proof]): for each positive, the module of another body with the same
interface (another operator, another output, another initial value, another constant), for the original
declaration.
-/

namespace Tests.Ved.U1SmallRegCheck

open Lean Elab Command Term Meta
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.VedU1Contract Tools.VedU1Entry

def negD (a : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) := -a
def notD (a : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) := ~~~a

def halfAdder (a b : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8 × BitVec 8) :=
  bundle2 (a ^^^ b) (a &&& b)

def haOr (a b : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  let r := halfAdder a b
  r.fst ||| r.snd
def haAnd (a b : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  let r := halfAdder a b
  r.fst &&& r.snd

def addThree (a b c : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  let ab := halfAdder a b
  let abc := halfAdder ab.fst c
  abc.fst
def addThreeCarry (a b c : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  let ab := halfAdder a b
  let abc := halfAdder ab.fst c
  abc.snd

def regEn (en : Signal defaultDomain Bool) (x : Signal defaultDomain (BitVec 16)) :
    Signal defaultDomain (BitVec 16) :=
  Signal.registerWithEnable 0#16 en x
def regEn1 (en : Signal defaultDomain Bool) (x : Signal defaultDomain (BitVec 16)) :
    Signal defaultDomain (BitVec 16) :=
  Signal.registerWithEnable 1#16 en x

def pure42 (_ : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) := Signal.pure 42
def pure43 (_ : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) := Signal.pure 43

/-! ## 1. Positives -/

#guard_msgs (drop info) in
#ved_u1 negD
#guard_msgs (drop info) in
#ved_u1 haOr
#guard_msgs (drop info) in
#ved_u1 addThree
#guard_msgs (drop info) in
#ved_u1 regEn
#guard_msgs (drop info) in
#ved_u1 pure42

def checkStmt (n : Name) : MetaM Unit := do
  let ci ← getConstInfo (n ++ `ved_u1)
  let expected := mkAppN (mkConst ``U1Stmt) #[mkConst (n ++ `ved_contract), mkConst (n ++ `ved_mod), mkConst n]
  unless ci.type == expected do throwError "{n}: the statement differs from U1Stmt of the original constant"
  let ax ← collectAxioms (n ++ `ved_u1)
  let std := [``propext, ``Classical.choice, ``Quot.sound]
  unless ax.all std.contains && ax.size == 3 do throwError "{n}: axioms {ax}"
  logInfo m!"{n}: exact statement, standard axioms"

/-- info: Tests.Ved.U1SmallRegCheck.negD: exact statement, standard axioms -/
#guard_msgs in
run_meta checkStmt ``negD
/-- info: Tests.Ved.U1SmallRegCheck.haOr: exact statement, standard axioms -/
#guard_msgs in
run_meta checkStmt ``haOr
/-- info: Tests.Ved.U1SmallRegCheck.addThree: exact statement, standard axioms -/
#guard_msgs in
run_meta checkStmt ``addThree
/-- info: Tests.Ved.U1SmallRegCheck.regEn: exact statement, standard axioms -/
#guard_msgs in
run_meta checkStmt ``regEn
/-- info: Tests.Ved.U1SmallRegCheck.pure42: exact statement, standard axioms -/
#guard_msgs in
run_meta checkStmt ``pure42

/-! ## 2. Controls: must stay refused -/

def modOf (base : Name) : TermElabM Sparkle.IR.AST.Module := do
  let some v := (← getConstInfo (base ++ `ved_mod)).value? | throwError "no value"
  evalModule v

def checkerNames (base : Name) : List Name :=
  [`ved_mod, `ved_contract, `ved_outs, `ved_body, `ved_u1].map (base ++ ·)

def expectRefused (stage : String) (absent : List Name) (act : TermElabM Unit) :
    CommandElabM Unit := liftTermElabM do
  let accepted ← try act; pure true catch e =>
    let s ← e.toMessageData.toString
    unless s.startsWith "VED U1 REFUSED" && (s.splitOn s!"[{stage}]").length > 1 do throw e
    pure false
  if accepted then throwError "control ACCEPTED (expected a refusal at [{stage}])"
  let env ← getEnv
  for n in absent do
    if env.contains n then throwError "left behind: {n}"
  logInfo m!"refused [{stage}], clean"

-- the modules of the other bodies, whose positives are accepted above
#guard_msgs (drop info) in
#ved_u1 notD
#guard_msgs (drop info) in
#ved_u1 haAnd
#guard_msgs (drop info) in
#ved_u1 addThreeCarry
#guard_msgs (drop info) in
#ved_u1 regEn1
#guard_msgs (drop info) in
#ved_u1 pure43

/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" (checkerNames `ctlNeg) do
  discard <| checkU1 ``negD `ctlNeg ``negD (← modOf ``notD) .generated

/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" (checkerNames `ctlHa) do
  discard <| checkU1 ``haOr `ctlHa ``haOr (← modOf ``haAnd) .generated

/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" (checkerNames `ctlAdd3) do
  discard <| checkU1 ``addThree `ctlAdd3 ``addThree (← modOf ``addThreeCarry) .generated

/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" (checkerNames `ctlRegEn) do
  discard <| checkU1 ``regEn `ctlRegEn ``regEn (← modOf ``regEn1) .generated

/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" (checkerNames `ctlPure) do
  discard <| checkU1 ``pure42 `ctlPure ``pure42 (← modOf ``pure43) .generated

end Tests.Ved.U1SmallRegCheck
