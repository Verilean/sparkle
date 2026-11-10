import Tools.VedU1Deep
import Sparkle.Core.CircuitMonad
import Sparkle.Core.CircuitDo

/-!
# `#verify_elab_deep`: closed initial values that are not `BitVec.ofNat _ lit`

Issue sparkle-ved-frontend.  The locator accepts an initial value that
evaluates to a literal (`BitVec.zero 8`, a named constant): the generator
evaluates it and the KERNEL checks `init = BitVec.ofNat w v` by `Eq.refl`
(the evaluator is not trusted).  Controls: an initial value depending on a
parameter is refused with a clear message and leaves no theorem.
-/

namespace Tests.Ved.DeepInitCheck

open Lean Elab Command Term Meta
open Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.Core
open Tools.VedU1Contract Tools.VedU1Entry Tools.VedU1Deep

def zeroInit (d : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg (BitVec.zero 8)
    let a := (r : Signal defaultDomain (BitVec 8))
    r <~ a + d
    return a

def initC : BitVec 8 := BitVec.ofInt 8 (-3)

def namedInit (d : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg initC
    let a := (r : Signal defaultDomain (BitVec 8))
    r <~ a + d
    return a

def paramInit (n : BitVec 8) (d : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg n
    let a := (r : Signal defaultDomain (BitVec 8))
    r <~ a + d
    return a

#guard_msgs (drop info) in
#verify_elab_deep zeroInit
#guard_msgs (drop info) in
#verify_elab_deep namedInit

def runEntry (n : Name) : CommandElabM Unit := liftTermElabM do
  let (_, _, thm) ← vedU1DeepEntry n
  let r ← Tools.VedStrictAudit.strictAudit thm
  logInfo m!"VED U1 OK {thm}: {Tools.VedStrictAudit.showNames r.axioms}"

/-- info: VED U1 OK Tests.Ved.DeepInitCheck.zeroInit.ved_u1: [Classical.choice, Quot.sound, propext] -/
#guard_msgs in
run_cmd runEntry ``zeroInit

/-- info: VED U1 OK Tests.Ved.DeepInitCheck.namedInit.ved_u1: [Classical.choice, Quot.sound, propext] -/
#guard_msgs in
run_cmd runEntry ``namedInit

example : U1Stmt zeroInit.ved_contract zeroInit.ved_mod zeroInit := zeroInit.ved_u1
example : U1Stmt namedInit.ved_contract namedInit.ved_mod namedInit := namedInit.ved_u1

/-! ## Refusal: an initial value depending on a parameter -/

/-- info: refused: initial values must be closed; no theorem left -/
#guard_msgs in
run_cmd do
  let ok ← try elabCommand (← `(#verify_elab_deep paramInit)); pure true
    catch _ => pure false
  -- elabCommand logs errors instead of throwing: inspect the log
  let msgs := (← get).messages.toList
  let hasErr := msgs.any fun m => m.severity == .error
  let txt ← msgs.foldlM (fun s m => do pure (s ++ (← m.data.toString))) ""
  modify fun s => { s with messages := {} }
  unless (ok && hasErr) || !ok do throwError "paramInit was accepted"
  unless (txt.splitOn "initial values depend on a parameter").length > 1 ||
      (txt.splitOn "must be closed").length > 1 do
    throwError "unclear message: {txt}"
  let env ← getEnv
  if env.contains ``paramInit_deep_trace || env.contains ``paramInit_deep then
    throwError "a theorem was left behind"
  logInfo "refused: initial values must be closed; no theorem left"

end Tests.Ved.DeepInitCheck
