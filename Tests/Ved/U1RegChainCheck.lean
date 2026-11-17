import Sparkle
import Tools.VedU1Entry

/-!
# Check: register chains without `Signal.loop` (U1)

Positives: a 3-register delay line (`chain3`), and a 2-register one with a non-zero initial value
(`chain2I`): exact `U1Stmt`, standard axioms.  Controls (must stay refused at [proof]), for the
original declaration `chain3`: the module of the same interface with another initial value
(`chain3One`), and the module of a delay line one register shorter (`chain2`).
-/

namespace Tests.Ved.U1RegChainCheck

open Lean Elab Command Term Meta
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.VedU1Contract Tools.VedU1Entry

def chain3 (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  Signal.register 0#8 (Signal.register 0#8 (Signal.register 0#8 x))
def chain3One (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  Signal.register 1#8 (Signal.register 0#8 (Signal.register 0#8 x))
def chain2 (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  Signal.register 0#8 (Signal.register 0#8 x)
def chain2I (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  Signal.register 5#8 (Signal.register 0#8 x)

/-! ## 1. Positives -/

#guard_msgs (drop info) in
#ved_u1 chain3
#guard_msgs (drop info) in
#ved_u1 chain2I

def checkStmt (n : Name) : MetaM Unit := do
  let ci ← getConstInfo (n ++ `ved_u1)
  let expected := mkAppN (mkConst ``U1Stmt) #[mkConst (n ++ `ved_contract), mkConst (n ++ `ved_mod), mkConst n]
  unless ci.type == expected do throwError "{n}: the statement differs from U1Stmt of the original constant"
  let ax ← collectAxioms (n ++ `ved_u1)
  let std := [``propext, ``Classical.choice, ``Quot.sound]
  unless ax.all std.contains && ax.size == 3 do throwError "{n}: axioms {ax}"
  logInfo m!"{n}: exact statement, standard axioms"

/-- info: Tests.Ved.U1RegChainCheck.chain3: exact statement, standard axioms -/
#guard_msgs in
run_meta checkStmt ``chain3
/-- info: Tests.Ved.U1RegChainCheck.chain2I: exact statement, standard axioms -/
#guard_msgs in
run_meta checkStmt ``chain2I

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

#guard_msgs (drop info) in
#ved_u1 chain3One
#guard_msgs (drop info) in
#ved_u1 chain2

/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" (checkerNames `ctlInit) do
  discard <| checkU1 ``chain3 `ctlInit ``chain3 (← modOf ``chain3One) .generated

/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" (checkerNames `ctlDepth) do
  discard <| checkU1 ``chain3 `ctlDepth ``chain3 (← modOf ``chain2) .generated

end Tests.Ved.U1RegChainCheck
