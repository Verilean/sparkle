import Tools.VedU1Entry

/-!
# Checks for the domain specialisation of the U1 entry

A leading implicit binder of type exactly `DomainConfig` (written
`{dom : DomainConfig}` or auto-bound) is instantiated with `defaultDomain`;
the theorem is then about `@decl defaultDomain`, NOT the polymorphic
declaration.  Controls: every other implicit/instance binder and every fixed
domain other than `defaultDomain` stays refused at `[table]`.
-/

namespace Tests.Ved.U1DomainCheck

open Lean Elab Command Term Meta
open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.VedU1Contract Tools.VedU1Entry

/-! ## Declarations (shaped like R303 `test_not` and R73 `testComplement8`) -/

def dnotAuto (a : Signal Domain (BitVec 16)) : Signal Domain (BitVec 16) := (~~~ ·) <$> a

def dnotImpl {dom : DomainConfig} (a : Signal dom (BitVec 8)) : Signal dom (BitVec 8) := ~~~a

/-- control: a non-`DomainConfig` implicit binder -/
def dNat {n : Nat} (a : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) := ~~~a

/-- control: an instance binder -/
def dInst {dom : DomainConfig} [Inhabited Nat] (a : Signal dom (BitVec 8)) : Signal dom (BitVec 8) := ~~~a

/-- a fixed domain other than `defaultDomain` -/
def otherDom : DomainConfig := { defaultDomain with period := 20001 }

def dFixed (a : Signal otherDom (BitVec 8)) : Signal otherDom (BitVec 8) := ~~~a

/-! ## Positive: the exact theorem type and the axioms -/

def checkSpec (decl : Name) : CommandElabM Unit := liftTermElabM do
  let (_, _, thm, nDom) ← vedU1EntryS decl
  unless nDom == 1 do throwError "{decl}: expected one instantiated binder, got {nDom}"
  let nm := Names.ofBase decl
  let expected := mkAppN (Lean.mkConst ``U1Stmt)
    #[Lean.mkConst nm.contract, Lean.mkConst nm.mod,
      mkApp (Lean.mkConst decl) (Lean.mkConst ``defaultDomain)]
  let some (.thmInfo ti) := (← getEnv).find? thm | throwError "{thm} is not a theorem"
  unless ti.type == expected do throwError "{thm}: type is not U1Stmt c m (@{decl} defaultDomain)"
  let r ← Tools.VedStrictAudit.strictAudit thm
  let ax ← collectAxioms thm
  let ok := [``propext, ``Classical.choice, ``Quot.sound]
  unless ax.all (ok.contains ·) && r.axioms.all (ok.contains ·) do
    throwError "{thm}: axioms {ax}"
  logInfo m!"specialised OK {thm}"

/-- info: specialised OK Tests.Ved.U1DomainCheck.dnotAuto.ved_u1 -/
#guard_msgs in
run_cmd checkSpec ``dnotAuto

/-- info: specialised OK Tests.Ved.U1DomainCheck.dnotImpl.ved_u1 -/
#guard_msgs in
run_cmd checkSpec ``dnotImpl

/-! ## Controls: refused at `[table]`, no theorem -/

def expectTableRefusal (decl : Name) : CommandElabM Unit := liftTermElabM do
  let accepted ← try discard <| vedU1Entry decl; pure true catch e =>
    let s ← e.toMessageData.toString
    unless s.startsWith s!"VED U1 REFUSED {decl} [table]" do throw e
    pure false
  if accepted then throwError "{decl}: ACCEPTED (expected a refusal at [table])"
  for n in [`ved_mod, `ved_contract, `ved_outs, `ved_body, `ved_u1] do
    if (← getEnv).contains (decl ++ n) then throwError "left behind: {decl ++ n}"
  logInfo m!"refused [table], clean"

/-- info: refused [table], clean -/
#guard_msgs in
run_cmd expectTableRefusal ``dNat

/-- info: refused [table], clean -/
#guard_msgs in
run_cmd expectTableRefusal ``dInst

/-- info: refused [table], clean -/
#guard_msgs in
run_cmd expectTableRefusal ``dFixed

end Tests.Ved.U1DomainCheck
