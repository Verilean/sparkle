import Tools.VedU1Deep
import Sparkle.Core.CircuitMonad
import Sparkle.Core.CircuitDo

/-!
# `#verify_elab_deep`: generated binder names never capture user parameters

Issue sparkle-ved-deep-hygiene.  The generator's proof text used fixed
binder names (`u`, `m`, `L`, `hL`, `t`, `s`, `n`, ...); a declaration with a
parameter of that name was captured (`Application type mismatch: argument u
has type Nat but expected Signal`).  Each declaration below is one register
with a Signal parameter named after a generated
binder.  Each must go through `#verify_elab_deep` and the U1 deep entry with
the same theorem shape and the standard three axioms as the control `accOrd`
with ordinary parameter names.
-/

namespace Tests.Ved.DeepHygieneCheck

open Lean Elab Command Term Meta
open Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.Core
open Tools.VedU1Contract Tools.VedU1Entry Tools.VedU1Deep

/-- `defSig f x`: a one-register accumulator whose Signal parameter is `x`.
-/
local macro "defSig " f:ident x:ident : command =>
  `(def $f ($x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
      circuit do
        let r ← Signal.reg (0#8)
        let a := (r : Signal defaultDomain (BitVec 8))
        r <~ a + $x
        return a)


defSig accOrd d
defSig sigU u
defSig sigT t
defSig sigM m
defSig sigL L
defSig sigHL hL
defSig sigS s
defSig sigN n
defSig sigPre pre
defSig sigQ q
defSig sigI i
defSig sigIh ih
defSig sigAddr addr
defSig sigHpre hpre
defSig sigHLt hLt
defSig sigK k
defSig sigEnv env
defSig sigPfx ved_u
/- Reserved-prefix lengthening: `ved_u` already lengthens the prefix to
`ved_v_`; `ved_v_u` lengthens it again. -/
defSig sigPfx2 ved_v_u
/- Declaration base `hne` is a prefix of the internal binder `hne_0`; the old
`mkI` took `hne_0` for a declaration name and left it unprefixed. -/
defSig hne hne_0
defSig hne2 hne2_0


#guard_msgs (drop info) in
#verify_elab_deep accOrd
#guard_msgs (drop info) in
#verify_elab_deep sigU
#guard_msgs (drop info) in
#verify_elab_deep sigT
#guard_msgs (drop info) in
#verify_elab_deep sigM
#guard_msgs (drop info) in
#verify_elab_deep sigL
#guard_msgs (drop info) in
#verify_elab_deep sigHL
#guard_msgs (drop info) in
#verify_elab_deep sigS
#guard_msgs (drop info) in
#verify_elab_deep sigN
#guard_msgs (drop info) in
#verify_elab_deep sigPre
#guard_msgs (drop info) in
#verify_elab_deep sigQ
#guard_msgs (drop info) in
#verify_elab_deep sigI
#guard_msgs (drop info) in
#verify_elab_deep sigIh
#guard_msgs (drop info) in
#verify_elab_deep sigAddr
#guard_msgs (drop info) in
#verify_elab_deep sigHpre
#guard_msgs (drop info) in
#verify_elab_deep sigHLt
#guard_msgs (drop info) in
#verify_elab_deep sigK
#guard_msgs (drop info) in
#verify_elab_deep sigEnv
#guard_msgs (drop info) in
#verify_elab_deep sigPfx
#guard_msgs (drop info) in
#verify_elab_deep sigPfx2
#guard_msgs (drop info) in
#verify_elab_deep hne
#guard_msgs (drop info) in
#verify_elab_deep hne2

/-- The U1 deep entry's theorem, as `U1Stmt` of the declaration itself, with
the strict audit axiom list. -/
def runEntry (n : Name) : CommandElabM Unit := liftTermElabM do
  let (_, _, thm) ← vedU1DeepEntry n
  let r ← Tools.VedStrictAudit.strictAudit thm
  logInfo m!"VED U1 OK: {Tools.VedStrictAudit.showNames r.axioms}"

local macro "checkCase " f:ident : command =>
  `(/-- info: VED U1 OK: [Classical.choice, Quot.sound, propext] -/
    #guard_msgs in
    run_cmd runEntry ``$f
    example : U1Stmt $(mkIdent (f.getId ++ `ved_contract)) $(mkIdent (f.getId ++ `ved_mod)) $f :=
      $(mkIdent (f.getId ++ `ved_u1)))

checkCase accOrd
checkCase sigU
checkCase sigT
checkCase sigM
checkCase sigL
checkCase sigHL
checkCase sigS
checkCase sigN
checkCase sigPre
checkCase sigQ
checkCase sigI
checkCase sigIh
checkCase sigAddr
checkCase sigHpre
checkCase sigHLt
checkCase sigK
checkCase sigEnv
checkCase sigPfx
checkCase sigPfx2
checkCase hne
checkCase hne2

-- Generated constant names are unchanged by the binder hygiene fix.
run_cmd liftTermElabM do
  let env ← getEnv
  let ns ← getCurrNamespace
  for b in [`accOrd, `hne] do
    for suf in ["_deep_trace", "_deep_rd0", "_deep_next", "_deep_inits", "_deep_out"] do
      let n := ns ++ Name.mkSimple (b.toString ++ suf)
      unless env.contains n do throwError "missing generated constant {n}"

end Tests.Ved.DeepHygieneCheck
