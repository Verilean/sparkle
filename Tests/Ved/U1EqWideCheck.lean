import Tools.VedU1Entry
import IP.RV32.Core
import Tests.IP.Control.LQRTest
import Tests.IP.Bus.CANopenHWTest
import Tests.IP.Bus.DroneCANHWTest

/-!
# `#ved_u1` on real IP rows with `==` / wide inputs (sparkle-ved-eq-wide)

The rows are the ORIGINAL declarations (no stand-in copies):

* `Sparkle.IP.RV32.aluSignal` (4/32/32-bit inputs, shifts, signed compare, `sra`),
* `Sparkle.IP.RV32.hazardSignal` (Bool `&&&` / `|||` / `~~~` and `===`),
* `Sparkle.Tests.IP.Control.LQRTest.lqrCtrlTop` (two 32-bit inputs, Q-format multiply,
  clamp, helper definitions two levels deep),
* the `private` `synth_canopenIsNmt` and `synth_droneCanNodeFilter` of the CANopen / DroneCAN
  HW tests (`#ved_u1_private` resolves the private name from its user-facing name and runs
  the SAME entry `vedU1EntryS`).

After `#ved_u1` the checks are independent of the entry: the stored type of `<decl>.ved_u1` is,
as an `Expr` compared with `==`, `U1Stmt <decl>.ved_contract <decl>.ved_mod (@decl defaultDomain)`
(or the bare constant when the declaration has no domain argument), and its axioms are within
`propext`, `Classical.choice`, `Quot.sound`.
-/

namespace Tests.Ved.U1EqWideCheck

open Lean Elab Command Term Meta
open Tools.VedU1Contract Tools.VedU1Entry

/-- the full (private-mangled) name of the declaration whose user-facing name is `user` -/
def findPrivate (user : Name) : CoreM Name := do
  let env ← getEnv
  let r := env.constants.fold (init := (none : Option Name)) fun acc k _ =>
    match acc with
    | some _ => acc
    | none => if privateToUserName? k == some user then some k else none
  match r with
  | some n => pure n
  | none => throwError "no private declaration {user}"

/-- `#ved_u1` for a `private` declaration, named by its user-facing name -/
elab "#ved_u1_private " id:ident : command => do
  let decl ← Command.liftCoreM (findPrivate id.getId)
  Command.liftTermElabM do
    let (_, _, thm, _) ← vedU1EntryS decl
    let r ← Tools.VedStrictAudit.strictAudit thm
    logInfo m!"VED U1 OK {id.getId}: {Tools.VedStrictAudit.showNames r.axioms}"

#guard_msgs (drop info) in
#ved_u1 Sparkle.IP.RV32.aluSignal

#guard_msgs (drop info) in
#ved_u1 Sparkle.IP.RV32.hazardSignal

#guard_msgs (drop info) in
#ved_u1 Sparkle.Tests.IP.Control.LQRTest.lqrCtrlTop

#guard_msgs (drop info) in
#ved_u1_private synth_canopenIsNmt

#guard_msgs (drop info) in
#ved_u1_private synth_droneCanNodeFilter

/-- the stored type is `U1Stmt c m (@decl defaultDomain …)` (`==`), axioms within std3 -/
def checkRow (decl : Name) (nDom : Nat) : CoreM Unit := do
  let nm := Names.ofBase decl
  let thm := decl ++ `ved_u1
  let mut stmt : Lean.Expr := Lean.mkConst decl
  for _ in [0:nDom] do stmt := mkApp stmt (Lean.mkConst ``Sparkle.Core.Domain.defaultDomain)
  let expected := mkAppN (Lean.mkConst ``U1Stmt) #[Lean.mkConst nm.contract, Lean.mkConst nm.mod, stmt]
  let some (.thmInfo ti) := (← getEnv).find? thm | throwError "{thm} is not a theorem"
  unless ti.type == expected do throwError "{thm}: type is not U1Stmt c m ({decl} …)"
  let ax ← collectAxioms thm
  let ok := [``propext, ``Classical.choice, ``Quot.sound]
  unless ax.all (ok.contains ·) do throwError "{thm}: axioms {ax}"

def checkAll : CommandElabM Unit := liftCoreM do
  checkRow ``Sparkle.IP.RV32.aluSignal 1
  checkRow ``Sparkle.IP.RV32.hazardSignal 1
  checkRow ``Sparkle.Tests.IP.Control.LQRTest.lqrCtrlTop 0
  checkRow (← findPrivate `synth_canopenIsNmt) 0
  checkRow (← findPrivate `synth_droneCanNodeFilter) 0
  logInfo m!"OK 5 rows: stored type = U1Stmt c m F, axioms within std3"

/-- info: OK 5 rows: stored type = U1Stmt c m F, axioms within std3 -/
#guard_msgs in
run_cmd checkAll

end Tests.Ved.U1EqWideCheck
