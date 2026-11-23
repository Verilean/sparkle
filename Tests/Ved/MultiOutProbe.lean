import Tools.VedU2HierRegEntry
import Tools.VedStrictAudit
import Sparkle.Core.CircuitMonad
import Sparkle.Core.CircuitDo

/-!
# Independent probe for the 2-output struct child (option `ved.compose.multiOut`)

NOT the Check's generator and none of its helpers: the toy is declared here, the standard command `#ved_u2_hier` runs with the
option on, and the stored theorem is then read from the environment and inspected with plain `Lean` code:

* its type is `==` `U2HRStmtK c m d top`, `c`, `m`, `d` the stored constants, `top` the ORIGINAL declaration;
* it is a kernel-added theorem (`thmInfo`) whose proof mentions the child's own theorem (struct route) and no `sorryAx`;
* `#print axioms` prints the axioms, and the closure is within `propext`, `Classical.choice`, `Quot.sound`.

`U2HRStmtK` is a NEW candidate statement (unreviewed); this probe checks the entry's result against it, not that it is the right one.
-/

namespace Tests.Ved.MultiOutProbe

open Lean Elab Command Term Meta
open Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.Core

structure Q2 (dom : DomainConfig) where
  p : Signal dom (BitVec 4)
  q : Signal dom (BitVec 4)

instance {dom : DomainConfig} : HasDomain (Q2 dom) dom := ⟨⟩

@[hardware_module] def kid2 {dom : DomainConfig} (x y : Signal dom (BitVec 4)) : Q2 dom :=
  ({ p := x + y, q := x - y } : Q2 dom)

def probeTop (inp : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) :=
  circuit do
    let acc ← Signal.reg 0#4
    let accS := (acc : Signal defaultDomain (BitVec 4))
    let c := kid2 accS inp
    acc <~ (c.p + c.q : Signal defaultDomain (BitVec 4))
    return accS

set_option ved.compose.multiOut true in
#ved_u2_hier probeTop

#eval show CommandElabM Unit from do
  let env ← getEnv
  let thm := `Tests.Ved.MultiOutProbe.probeTop.ved_u1
  let some (.thmInfo ti) := env.find? thm | throwError "{thm}: not a theorem in the environment"
  let top := `Tests.Ved.MultiOutProbe.probeTop
  let expected := mkAppN (mkConst ``Tools.VedU2Hier.U2HRStmtK)
    #[mkConst (top ++ `ved_contract), mkConst (top ++ `ved_mod), mkConst (top ++ `ved_design), mkConst top]
  unless ti.type == expected do throwError "the stored type is not U2HRStmtK c m d probeTop:\n{ti.type}"
  let kidThm := `Tests.Ved.MultiOutProbe.probeTop.ved_child.Tests.Ved.MultiOutProbe.kid2.ved_u1
  unless ti.value.getUsedConstants.contains kidThm do throwError "the child's theorem {kidThm} does not occur in the proof"
  let axs ← liftCoreM (collectAxioms thm)
  if axs.contains ``sorryAx then throwError "sorryAx"
  unless axs.all (fun a => [``propext, ``Classical.choice, ``Quot.sound].contains a) do throwError "axioms outside std3: {axs}"
  logInfo m!"PROBE OK: type == U2HRStmtK for probeTop; child theorem used; axioms {axs}; no sorryAx"

#print axioms Tests.Ved.MultiOutProbe.probeTop.ved_u1

end Tests.Ved.MultiOutProbe
