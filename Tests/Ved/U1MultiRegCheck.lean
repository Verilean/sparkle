import Tools.VedU1Deep
import Sparkle.Core.CircuitMonad
import Sparkle.Core.CircuitDo

/-!
# `#ved_u1_deep` with several registers and Bool data inputs

Issue sparkle-ved-multireg.  The deep route's script used to cover ONE register
and bit-vector inputs.  It now proves, for k ≥ 1 registers, the invariant
"register `_nm i` of the module equals `Cdo.irState … i` at the same cycle", and
accepts `Bool` data inputs (the declaration's own semantics: `PTy.sig .bit`,
`ins t n != 0`; the deep circuit's 1-bit encoding comes from `_inp`).

What is fixed here (`#guard_msgs`):
1. Positives (local copies shaped like the `Tests/CircuitDoTest.lean` and
   `Tests/SignalLoopTest.lean` representatives, local names): two registers with
   a Bool reset, four independent counters, a held register with a Bool
   enable and a bit-vector input, a 3-state FSM with a hold, and user parameters
   named like the generator's own binders.  Each is accepted with the standard
   three axioms, and the registered theorem's type is rebuilt by hand and compared
   with `==` against `U1Stmt f.ved_contract f.ved_mod f`.
2. Refusals (`expectRefused`: the stage is checked and nothing the checker or
   the builder registered is left under the base): one register's next value
   changed, two same-width registers swapped in the module, another
   declaration's DeepElab constants, a wrong initial value.
-/

namespace Tests.Ved.U1MultiRegCheck

open Lean Elab Command Term Meta
open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics
open Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.Core
open Tools.VedU1Contract Tools.VedU1Entry Tools.VedU1Deep

def twoRegReset (reset : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let a ← Signal.reg 0#8
    let b ← Signal.reg 0#8
    if reset then
      a <~ 0#8
      b <~ 0#8
    else
      a <~ a + 1#8
      b <~ b + 2#8
    return a + b

/-- Same shape, other constants (a different meaning). -/
def twoRegReset3 (reset : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let a ← Signal.reg 0#8
    let b ← Signal.reg 0#8
    if reset then
      a <~ 0#8
      b <~ 0#8
    else
      a <~ a + 1#8
      b <~ b + 3#8
    return a + b

def fourCtr : Signal defaultDomain (BitVec 8) :=
  circuit do
    let a ← Signal.reg 0#8
    let b ← Signal.reg 0#8
    let c ← Signal.reg 0#8
    let d ← Signal.reg 0#8
    a <~ a + 1#8
    b <~ b + 2#8
    c <~ c + 3#8
    d <~ d + 4#8
    let aSig := (a : Signal defaultDomain (BitVec 8))
    let bSig := (b : Signal defaultDomain (BitVec 8))
    let cSig := (c : Signal defaultDomain (BitVec 8))
    let dSig := (d : Signal defaultDomain (BitVec 8))
    return aSig + bSig + cSig + dSig

/-- Register `acc` is held while `en` is low; `n` always counts. -/
def heldEn (en : Signal defaultDomain Bool) (d : Signal defaultDomain (BitVec 8)) :
    Signal defaultDomain (BitVec 8) :=
  circuit do
    let acc ← Signal.reg 0#8
    let n ← Signal.reg 0#8
    if en then
      acc <~ acc + d
      n <~ n + 1#8
    else
      n <~ n + 1#8
    return acc

def fsmHold : Signal defaultDomain (BitVec 8) :=
  circuit do
    let state ← Signal.reg 0#2
    let extra ← Signal.reg 0#8
    match state with
    | 0#2 => state <~ 1#2
    | 1#2 =>
      state <~ 2#2
      extra <~ extra + 1#8
    | _ => state <~ 0#2
    return extra

/-- User parameters (`u`, `m`) and register names (`t`, `ins`) spelled like the
names a generated script could bind. -/
def hygBool (u : Signal defaultDomain Bool) (m : Signal defaultDomain (BitVec 8)) :
    Signal defaultDomain (BitVec 8) :=
  circuit do
    let t ← Signal.reg 0#8
    let ins ← Signal.reg 0#8
    if u then
      t <~ t + m
      ins <~ ins + 1#8
    else
      ins <~ ins + 1#8
    return t

#guard_msgs (drop info) in
#verify_elab_deep twoRegReset
#guard_msgs (drop info) in
#verify_elab_deep twoRegReset3
#guard_msgs (drop info) in
#verify_elab_deep fourCtr
#guard_msgs (drop info) in
#verify_elab_deep heldEn
#guard_msgs (drop info) in
#verify_elab_deep fsmHold
#guard_msgs (drop info) in
#verify_elab_deep hygBool

/-! ## 1. Accepted: strict, complete type -/

def runEntry (n : Name) : CommandElabM Unit := liftTermElabM do
  let (_, _, thm) ← vedU1DeepEntry n
  let r ← Tools.VedStrictAudit.strictAudit thm
  logInfo m!"VED U1 OK {thm}: {Tools.VedStrictAudit.showNames r.axioms}"

/-- info: VED U1 OK Tests.Ved.U1MultiRegCheck.twoRegReset.ved_u1: [Classical.choice, Quot.sound, propext] -/
#guard_msgs in
set_option Elab.async false in
run_cmd runEntry ``twoRegReset

/-- info: VED U1 OK Tests.Ved.U1MultiRegCheck.fourCtr.ved_u1: [Classical.choice, Quot.sound, propext] -/
#guard_msgs in
set_option Elab.async false in
run_cmd runEntry ``fourCtr

/-- info: VED U1 OK Tests.Ved.U1MultiRegCheck.heldEn.ved_u1: [Classical.choice, Quot.sound, propext] -/
#guard_msgs in
set_option Elab.async false in
run_cmd runEntry ``heldEn

/-- info: VED U1 OK Tests.Ved.U1MultiRegCheck.fsmHold.ved_u1: [Classical.choice, Quot.sound, propext] -/
#guard_msgs in
set_option Elab.async false in
run_cmd runEntry ``fsmHold

/-- info: VED U1 OK Tests.Ved.U1MultiRegCheck.hygBool.ved_u1: [Classical.choice, Quot.sound, propext] -/
#guard_msgs in
set_option Elab.async false in
run_cmd runEntry ``hygBool

example : U1Stmt twoRegReset.ved_contract twoRegReset.ved_mod twoRegReset := twoRegReset.ved_u1
example : U1Stmt fourCtr.ved_contract fourCtr.ved_mod fourCtr := fourCtr.ved_u1
example : U1Stmt heldEn.ved_contract heldEn.ved_mod heldEn := heldEn.ved_u1
example : U1Stmt fsmHold.ved_contract fsmHold.ved_mod fsmHold := fsmHold.ved_u1
example : U1Stmt hygBool.ved_contract hygBool.ved_mod hygBool := hygBool.ved_u1

/-- Bool ports are `PTy.bit`, bit-vector ports `PTy.bv w`; registers are what the
module has (the invariant ranges over all of them). -/
example : (ved_table% twoRegReset).ins = [PTy.bit] := by decide
example : (regsOf twoRegReset.ved_mod.body).length = 2 := by decide
example : (regsOf fourCtr.ved_mod.body).length = 4 := by decide
example : (ved_table% heldEn).ins = [PTy.bit, PTy.bv 8] := by decide
example : (regsOf hygBool.ved_mod.body).length = 2 := by decide

/-- info: complete type and std3 axioms: twoRegReset, fourCtr, heldEn, fsmHold, hygBool -/
#guard_msgs in
run_cmd liftTermElabM do
  for n in [``twoRegReset, ``fourCtr, ``heldEn, ``fsmHold, ``hygBool] do
    let ti ← getConstInfo (n ++ `ved_u1)
    let expected := mkAppN (mkConst ``U1Stmt)
      #[mkConst (n ++ `ved_contract), mkConst (n ++ `ved_mod), mkConst n]
    unless ti.type == expected do throwError "type of {n}.ved_u1 is not the expected statement"
    let axs ← collectAxioms (n ++ `ved_u1)
    let std3 : List Name := [``propext, ``Classical.choice, ``Quot.sound]
    unless axs.all (std3.contains ·) do throwError "{n}.ved_u1 axioms {axs}"
  logInfo "complete type and std3 axioms: twoRegReset, fourCtr, heldEn, fsmHold, hygBool"

/-! ## 2. Refusals -/

def modOf (base : Name) : TermElabM Sparkle.IR.AST.Module := do
  let some v := (← getConstInfo (base ++ `ved_mod)).value? | throwError "no value"
  evalModule v

def checkerNames (base : Name) : List Name :=
  [`ved_mod, `ved_contract, `ved_outs, `ved_body, `ved_u1].map (base ++ ·) ++ auxNames base

def assertClean (absent : List Name) : TermElabM Unit := do
  let env ← getEnv
  for n in absent do
    if env.contains n then throwError "left behind: {n}"

def expectRefused (stage : String) (absent : List Name) (act : TermElabM Unit) :
    CommandElabM Unit := liftTermElabM do
  let accepted ← try act; pure true catch e =>
    let s ← e.toMessageData.toString
    unless s.startsWith "VED U1 REFUSED" && (s.splitOn s!"[{stage}]").length > 1 do throw e
    pure false
  if accepted then throwError "control ACCEPTED (expected a refusal at [{stage}])"
  assertClean absent
  logInfo m!"refused [{stage}], clean"

def deepSrc (stmt deep : Name) : TermElabM ProofSrc := do
  let tbl ← readTable stmt
  pure (.built (buildDeepWith stmt deep tbl))

/-- One register's next value changed: the constant 2 (`b <~ b + 2`) becomes 4. -/
def mutNext (m : Sparkle.IR.AST.Module) : Sparkle.IR.AST.Module :=
  { m with body := m.body.map fun s => match s with
      | .assign n (.const 2 w) => .assign n (.const 4 w)
      | s => s }

/-- Two same-width registers swapped in the module: the register statements
exchange their output names (their cones, inits and the wires stay). -/
def mutSwap (m : Sparkle.IR.AST.Module) : Sparkle.IR.AST.Module :=
  match regsOf m.body with
  | (r1, _, _, _) :: (r2, _, _, _) :: _ =>
    { m with body := m.body.map fun s => match s with
        | .register o c r e i =>
          .register (if o == r1 then r2 else if o == r2 then r1 else o) c r e i
        | s => s }
  | _ => m

/-- A wrong initial value on every register. -/
def mutInit (m : Sparkle.IR.AST.Module) : Sparkle.IR.AST.Module :=
  { m with body := m.body.map fun s => match s with
      | .register o c r e _ => .register o c r e 5
      | s => s }

/-- info: mutations differ from the original -/
#guard_msgs in
run_cmd liftTermElabM do
  let m ← modOf ``twoRegReset
  if decide (mutNext m = m) || decide (mutSwap m = m) || decide (mutInit m = m) then
    throwError "a mutation is the identity"
  logInfo "mutations differ from the original"

/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" (checkerNames `ctlNext) do
  discard <| checkU1 ``twoRegReset `ctlNext ``twoRegReset (mutNext (← modOf ``twoRegReset))
    (← deepSrc ``twoRegReset ``twoRegReset)

/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" (checkerNames `ctlNext4) do
  discard <| checkU1 ``fourCtr `ctlNext4 ``fourCtr (mutNext (← modOf ``fourCtr))
    (← deepSrc ``fourCtr ``fourCtr)

/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" (checkerNames `ctlSwap) do
  discard <| checkU1 ``twoRegReset `ctlSwap ``twoRegReset (mutSwap (← modOf ``twoRegReset))
    (← deepSrc ``twoRegReset ``twoRegReset)

/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" (checkerNames `ctlSwap4) do
  discard <| checkU1 ``fourCtr `ctlSwap4 ``fourCtr (mutSwap (← modOf ``fourCtr))
    (← deepSrc ``fourCtr ``fourCtr)

/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" (checkerNames `ctlFacts) do
  discard <| checkU1 ``twoRegReset `ctlFacts ``twoRegReset (← modOf ``twoRegReset)
    (← deepSrc ``twoRegReset ``twoRegReset3)

/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" (checkerNames `ctlInit) do
  discard <| checkU1 ``twoRegReset `ctlInit ``twoRegReset (mutInit (← modOf ``twoRegReset))
    (← deepSrc ``twoRegReset ``twoRegReset)

/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" (checkerNames `ctlInit4) do
  discard <| checkU1 ``fourCtr `ctlInit4 ``fourCtr (mutInit (← modOf ``fourCtr))
    (← deepSrc ``fourCtr ``fourCtr)

end Tests.Ved.U1MultiRegCheck
