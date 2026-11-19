import Sparkle
import Sparkle.Core.CircuitMonad
import Tools.VedU1Entry

/-!
# Check: a `runCircuitH` (Circuit-monad) register loop through the wire-share loop path

The loop body of `runCircuitH` holds `Circuit.next r s >>= k` / `pure`; `loopScriptFor` adds `Bind.bind` /
`Pure.pure` to its simp set for such a declaration, and the closing step has range facts for an `xor` chain
(`Tools/VedU1LoopXor.lean`).  Positives: a counter, two counters, a three-register xor.  Controls (must stay
refused at [proof]): the module of another increment, or of another initial value, for the original declaration.
-/

namespace Tests.Ved.U1CircuitLoopCheck

open Lean Elab Command Term Meta
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.VedU1Contract Tools.VedU1Entry

def cnt : Signal defaultDomain (BitVec 8) :=
  runCircuitH (αs := [BitVec 8]) (0#8, ())
    (fun regs => do
      let (r0, _) := regs
      Circuit.next r0 (Circuit.read r0 + 1#8)
      return Circuit.read r0)

def cntInc2 : Signal defaultDomain (BitVec 8) :=
  runCircuitH (αs := [BitVec 8]) (0#8, ())
    (fun regs => do
      let (r0, _) := regs
      Circuit.next r0 (Circuit.read r0 + 2#8)
      return Circuit.read r0)

def cntInit : Signal defaultDomain (BitVec 8) :=
  runCircuitH (αs := [BitVec 8]) (5#8, ())
    (fun regs => do
      let (r0, _) := regs
      Circuit.next r0 (Circuit.read r0 + 1#8)
      return Circuit.read r0)

def xor3 : Signal defaultDomain (BitVec 8) :=
  runCircuitH (αs := [BitVec 8, BitVec 8, BitVec 8]) (0#8, 0#8, 0#8, ())
    (fun regs => do
      let (a, b, c, _) := regs
      Circuit.next a (Circuit.read a + 1#8)
      Circuit.next b (Circuit.read b + 2#8)
      Circuit.next c (Circuit.read c + 3#8)
      return Circuit.read a ^^^ Circuit.read b ^^^ Circuit.read c)

/-! ## 1. Positives -/

#guard_msgs (drop info) in
#ved_u1 cnt
#guard_msgs (drop info) in
#ved_u1 cntInc2
#guard_msgs (drop info) in
#ved_u1 cntInit
#guard_msgs (drop info) in
#ved_u1 xor3

def checkStmt (n : Name) : MetaM Unit := do
  let ci ← getConstInfo (n ++ `ved_u1)
  let expected := mkAppN (mkConst ``U1Stmt) #[mkConst (n ++ `ved_contract), mkConst (n ++ `ved_mod), mkConst n]
  unless ci.type == expected do throwError "{n}: the statement differs from U1Stmt of the original constant"
  let ax ← collectAxioms (n ++ `ved_u1)
  let std := [``propext, ``Classical.choice, ``Quot.sound]
  unless ax.all std.contains && ax.size == 3 do throwError "{n}: axioms {ax}"
  logInfo m!"{n}: exact statement, standard axioms"

/-- info: Tests.Ved.U1CircuitLoopCheck.cnt: exact statement, standard axioms -/
#guard_msgs in
run_meta checkStmt ``cnt
/-- info: Tests.Ved.U1CircuitLoopCheck.xor3: exact statement, standard axioms -/
#guard_msgs in
run_meta checkStmt ``xor3

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

-- the module of the +2 counter, for the +1 counter
/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" (checkerNames `ctlCntInc) do
  discard <| checkU1 ``cnt `ctlCntInc ``cnt (← modOf ``cntInc2) .generated

-- the module of the counter started at 5, for the counter started at 0
/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" (checkerNames `ctlCntInit) do
  discard <| checkU1 ``cnt `ctlCntInit ``cnt (← modOf ``cntInit) .generated

end Tests.Ved.U1CircuitLoopCheck
