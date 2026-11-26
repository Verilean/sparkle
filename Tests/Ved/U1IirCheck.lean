import Sparkle
import Sparkle.Compiler.Elab
import IP.Control.FixedPoint
import Tools.VedU1Entry

set_option maxRecDepth 100000

/-!
# Check: the wide signed product of a sign-extended value (`ved_iir_norm`)

`IP.Control.IIRBiquad` (R101, R112) closes with `omega` on a goal in which `4194 * sext x >> 16` (a 64-bit
signed product) occurs in several syntactic copies: the `Nat` form of the implementation, the `Int` form of the
`bmod` specification and the cast form.  `omega` gives each copy its own floor atoms and cannot identify them.
`ved_loop_close` therefore ends with the alternative `ved_iir_norm` (`Tools/VedU1Iir.lean`).

`iirH`: a register holding the previous sample, the output `min (mulQ 4194 x + s) 4194304` (signed compare) with
`mulQ a b = (sext64 a * sext64 b) >>> 16` as in `IP.Control.FixedPoint`.
* Without the `ved_iir_norm` alternative (checked in scratch at 3bb349ed, the alternative removed from
  `ved_loop_close`) `iirH` is REFUSED at `[proof]`: `omega could not prove the goal`, with one floor atom per copy of
  the product.
* With it `iirH` is accepted: stored type `==` `U1Stmt` of the original constant, axioms exactly
  `[propext, Classical.choice, Quot.sound]`.
* `iirN` (no clamp) is accepted at both commits; it is the module of the control.
Control (must stay refused at `[proof]`): the specification of `iirH` against the module of `iirN` (altered
output: no saturation).
-/

namespace Tests.Ved.U1IirCheck

open Lean Elab Command Term Meta
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.IP.Control.FixedPoint
open Tools.VedU1Contract Tools.VedU1Entry

def clampHi (lim : BitVec 32) (x : Signal defaultDomain (BitVec 32)) : Signal defaultDomain (BitVec 32) :=
  let hi : Signal defaultDomain (BitVec 32) := Signal.pure lim
  Signal.mux (Signal.slt hi x) hi x

def iirN (x : Signal defaultDomain (BitVec 32)) : Signal defaultDomain (BitVec 32) :=
  circuit do
    let sReg ← Signal.reg (0#32)
    let s := (sReg : Signal defaultDomain (BitVec 32))
    let y := mulQSig (Signal.pure 4194#32) x + s
    sReg <~ x
    return y

def iirH (x : Signal defaultDomain (BitVec 32)) : Signal defaultDomain (BitVec 32) :=
  circuit do
    let sReg ← Signal.reg (0#32)
    let s := (sReg : Signal defaultDomain (BitVec 32))
    let y := clampHi (BitVec.ofInt 32 4194304) (mulQSig (Signal.pure 4194#32) x + s)
    sReg <~ x
    return y

/-! ## 1. Positives -/

#guard_msgs (drop info) in
#ved_u1 iirN
#guard_msgs (drop info) in
#ved_u1 iirH

def checkStmt (n : Name) : MetaM Unit := do
  let ci ← getConstInfo (n ++ `ved_u1)
  let expected := mkAppN (mkConst ``U1Stmt) #[mkConst (n ++ `ved_contract), mkConst (n ++ `ved_mod), mkConst n]
  unless ci.type == expected do throwError "{n}: the statement differs from U1Stmt of the original constant"
  let ax ← collectAxioms (n ++ `ved_u1)
  let std := [``propext, ``Classical.choice, ``Quot.sound]
  unless ax.all std.contains && ax.size == 3 do throwError "{n}: axioms {ax}"
  logInfo m!"{n}: exact statement, standard axioms"

/-- info: Tests.Ved.U1IirCheck.iirH: exact statement, standard axioms -/
#guard_msgs in
run_meta checkStmt ``iirH
/-- info: Tests.Ved.U1IirCheck.iirN: exact statement, standard axioms -/
#guard_msgs in
run_meta checkStmt ``iirN

/-! ## 2. Control: must stay refused -/

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

/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" (checkerNames `ctlIir) do
  discard <| checkU1 ``iirH `ctlIir ``iirH (← modOf ``iirN) .generated

end Tests.Ved.U1IirCheck
