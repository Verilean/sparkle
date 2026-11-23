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

/-! ### Unit 3: the child theorem of a SEQUENTIAL struct child (one register), by the standard `#ved_u1` command

The struct child of the parent route is proved by the same entry (`stmtOfStruct` + `checkU1E`); here the standard command is run on a
2-output child with a register, and its result is read back: a `U1Stmt` theorem over a module that has a register, standard axioms.
No acceptance of a PARENT over such a child is claimed (see docs/VED-COMPOSE-CONNECT.md, unit 17). -/

@[hardware_module] def kidSeq {dom : DomainConfig} (x y : Signal dom (BitVec 4)) : Q2 dom :=
  circuit do
    let r ← Signal.reg 0#4
    let rS := (r : Signal dom (BitVec 4))
    r <~ x + y
    return ({ p := rS, q := rS - y } : Q2 dom)

#ved_u1 kidSeq

#eval show CommandElabM Unit from do
  let env ← getEnv
  let thm := `Tests.Ved.MultiOutProbe.kidSeq.ved_u1
  let some (.thmInfo ti) := env.find? thm | throwError "{thm}: not a theorem in the environment"
  unless ti.type.getAppFn.isConstOf ``Tools.VedU1Contract.U1Stmt do throwError "{thm}: not a U1Stmt"
  let some (.defnInfo mi) := env.find? (`Tests.Ved.MultiOutProbe.kidSeq.ved_mod) | throwError "no module constant"
  let hasReg : Bool := decide (((toString mi.value).splitOn "register").length > 1)
  let axs ← liftCoreM (collectAxioms thm)
  if axs.contains ``sorryAx then throwError "sorryAx"
  unless axs.all (fun a => [``propext, ``Classical.choice, ``Quot.sound].contains a) do throwError "axioms outside std3: {axs}"
  logInfo m!"PROBE SEQ OK: kidSeq.ved_u1 is a U1Stmt; module mentions a register: {toString hasReg}; axioms {axs}; no sorryAx"

/-! ### Unit 4: a parent with a register over the SEQUENTIAL struct child, the child's input read from the PARENT REGISTER

Same independent reading as the first probe: the standard `#ved_u2_hier` with the option on, then the stored theorem inspected with
plain `Lean` code (type `==` `U2HRStmtK c m d top`, the child's own theorem used, no `sorryAx`, std3), and in addition that the child
module HAS a register (so the child's call is not a one-cycle step). -/

def probeTopSeq (inp : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) :=
  circuit do
    let acc ← Signal.reg 0#4
    let accS := (acc : Signal defaultDomain (BitVec 4))
    let c := kidSeq accS inp
    acc <~ (c.p + c.q : Signal defaultDomain (BitVec 4))
    return accS

set_option ved.compose.multiOut true in
#ved_u2_hier probeTopSeq

#eval show CommandElabM Unit from do
  let env ← getEnv
  let thm := `Tests.Ved.MultiOutProbe.probeTopSeq.ved_u1
  let some (.thmInfo ti) := env.find? thm | throwError "{thm}: not a theorem in the environment"
  let top := `Tests.Ved.MultiOutProbe.probeTopSeq
  let expected := mkAppN (mkConst ``Tools.VedU2Hier.U2HRStmtK)
    #[mkConst (top ++ `ved_contract), mkConst (top ++ `ved_mod), mkConst (top ++ `ved_design), mkConst top]
  unless ti.type == expected do throwError "the stored type is not U2HRStmtK c m d probeTopSeq:\n{ti.type}"
  let kidThm := `Tests.Ved.MultiOutProbe.probeTopSeq.ved_child.Tests.Ved.MultiOutProbe.kidSeq.ved_u1
  unless ti.value.getUsedConstants.contains kidThm do throwError "the child's theorem {kidThm} does not occur in the proof"
  let some (.defnInfo cm) := env.find? (`Tests.Ved.MultiOutProbe.probeTopSeq.ved_child.Tests.Ved.MultiOutProbe.kidSeq.ved_mod)
    | throwError "no child module constant"
  let hasReg : Bool := decide (((toString cm.value).splitOn "register").length > 1)
  unless hasReg do throwError "the child module has no register"
  let axs ← liftCoreM (collectAxioms thm)
  if axs.contains ``sorryAx then throwError "sorryAx"
  unless axs.all (fun a => [``propext, ``Classical.choice, ``Quot.sound].contains a) do throwError "axioms outside std3: {axs}"
  logInfo m!"PROBE SEQ PARENT OK: type == U2HRStmtK for probeTopSeq; sequential child (has a register) fed from the parent register; child theorem used; axioms {axs}; no sorryAx"

#print axioms Tests.Ved.MultiOutProbe.probeTopSeq.ved_u1

end Tests.Ved.MultiOutProbe

/-! ## Unit 4: a REGISTER-FREE parent over the 2-output child, statement `U2HStmtK` (NOT yet accepted)

The standard entry `vedU2HierEntryR` with the option on routes a register-free parent with a k-output child through
`phase1`/`phase2` (statement `U2HStmtK`).  The shape (`HierShapeK`) and the child theorem pass; the open parent is the first
unsupplied piece: `genOpenMulti` (Tools/VedU2HierMultiGen.lean:271) needs the parent's value to reduce to a `circuit do`
(`runCircuitH`), a register-free parent such as `probeA` has none.  Pinned as the refusal `[open] ... runCircuitH` (and nothing
left behind), so this Check goes red the day that proposition is supplied and the acceptance assertion must be added. -/

namespace Tests.Ved.MultiOutProbe

open Lean Elab Command Term Meta
open Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.Core

def probeA (a b : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) :=
  let c := kid2 a b
  c.p - c.q

#eval show CommandElabM Unit from do
  let before := (← getEnv).constants.map₂.toList.map (·.1)
  let r ← withScope (fun sc => { sc with opts := sc.opts.setBool `ved.compose.multiOut true }) do
    try
      discard <| Tools.VedU2HierRegEntry.vedU2HierEntryR `Tests.Ved.MultiOutProbe.probeA
      pure none
    catch e => pure (some (← liftTermElabM (e.toMessageData.toString)))
  let some msg := r | throwError "probeA: expected the pinned [open] refusal, the entry ACCEPTED (add the U2HStmtK assertion)"
  unless msg.startsWith "VED U1 REFUSED Tests.Ved.MultiOutProbe.probeA [open]" && (msg.splitOn "runCircuitH").length > 1 do
    throwError "probeA: unexpected refusal: {msg.take 400}"
  let added := (← getEnv).constants.map₂.toList.map (·.1) |>.filter (!before.contains ·)
  unless added.isEmpty do throwError "probeA: constants left after the refusal: {added}"
  logInfo m!"PROBE A PINNED: register-free parent refused at [open] (runCircuitH): {msg.take 200}"

end Tests.Ved.MultiOutProbe
