import Tests.Ved.MultiOutCheck
import Tools.VedU2HierRecEntry
import Tools.VedU2HierRecOr

/-!
# Nested toy through the entry (CANDIDATE; Tools/VedU2HierRec*.lean)
-/

namespace Tests.Ved.RecEntry

open Lean Elab Command Term Meta
open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.VedU1Contract Tools.VedU1Hier Tools.VedU2Hier Tools.VedU2HierRegEntry Tests.Ved.ComposeCheckUtil

/-- a sequential leaf (one register) -/
@[hardware_module] def leafs (x : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) :=
  circuit do
    let r ← Signal.reg 0#4
    r <~ r + x
    return r

#verify_elab_deep leafs

/-- the middle module: one register of its own, one instance of `leafs` on its data input -/
@[hardware_module] def mids (x y : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) :=
  circuit do
    let r ← Signal.reg 0#4
    let c := leafs x
    r <~ r + c + y
    return r

/-- the top: register-free, one instance of the middle module on its data inputs -/
def tops (a b : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) :=
  mids a b


set_option ved.compose.nested true in
#ved_u2_hier tops

-- baseline (before the nested hunk): the option-off refusal of the real design
#eval show CommandElabM Unit from do
  let (m, d) ← synthOf ``tops
  let (stmt, nDom) ← liftTermElabM (specialiseDomain ``tops)
  let r ← try
      discard <| checkU2HR ``tops stmt nDom m d none
      pure "ACCEPTED"
    catch e => liftTermElabM (e.toMessageData.toString)
  logInfo m!"OFFMSG: {r}"

end Tests.Ved.RecEntry
