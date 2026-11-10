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

/-! ## Declarations -/

-- The binder shapes of R303 `test_not` (auto-bound `Domain`) and R73
-- `testComplement8` (`{dom : DomainConfig}`), with the identity as the body.
def didAuto (a : Signal Domain (BitVec 16)) : Signal Domain (BitVec 16) := a

def didImpl {dom : DomainConfig} (a : Signal dom (BitVec 8)) : Signal dom (BitVec 8) := a

-- The bodies of the representatives themselves (copies, local names).
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

/-- info: specialised OK Tests.Ved.U1DomainCheck.didAuto.ved_u1 -/
#guard_msgs in
run_cmd checkSpec ``didAuto

/-- info: specialised OK Tests.Ved.U1DomainCheck.didImpl.ved_u1 -/
#guard_msgs in
run_cmd checkSpec ``didImpl

/-! ## The representatives' bodies: strict (`Operator.not`, any width)

The bodies of R303 `test_not` (BitVec 16, auto-bound `Domain`) and R73
`testComplement8` (BitVec 8, `{dom : DomainConfig}`): exact type
`U1Stmt c m (@decl defaultDomain)` rebuilt and compared, std3 axioms. -/

/-- info: specialised OK Tests.Ved.U1DomainCheck.dnotAuto.ved_u1 -/
#guard_msgs in
run_cmd checkSpec ``dnotAuto

/-- info: specialised OK Tests.Ved.U1DomainCheck.dnotImpl.ved_u1 -/
#guard_msgs in
run_cmd checkSpec ``dnotImpl

-- the same rule at a width that is neither 8 nor 16
def dnot5 {dom : DomainConfig} (a : Signal dom (BitVec 5)) : Signal dom (BitVec 5) := ~~~a

/-- info: specialised OK Tests.Ved.U1DomainCheck.dnot5.ved_u1 -/
#guard_msgs in
run_cmd checkSpec ``dnot5

-- Two-input bitwise operators (next operators of the combinational group)
def dand8 (a b : Signal Domain (BitVec 8)) : Signal Domain (BitVec 8) := a &&& b
def dor8 (a b : Signal Domain (BitVec 8)) : Signal Domain (BitVec 8) := a ||| b
def dxor8 {dom : DomainConfig} (a b : Signal dom (BitVec 12)) : Signal dom (BitVec 12) := a ^^^ b

/-- info: specialised OK Tests.Ved.U1DomainCheck.dand8.ved_u1 -/
#guard_msgs in
run_cmd checkSpec ``dand8

/-- info: specialised OK Tests.Ved.U1DomainCheck.dor8.ved_u1 -/
#guard_msgs in
run_cmd checkSpec ``dor8

/-- info: specialised OK Tests.Ved.U1DomainCheck.dxor8.ved_u1 -/
#guard_msgs in
run_cmd checkSpec ``dxor8

/-! ## Controls: refused at `[table]`, no theorem -/

def expectStageRefusal (stage : String) (decl : Name) : CommandElabM Unit := liftTermElabM do
  let accepted ← try discard <| vedU1Entry decl; pure true catch e =>
    let s ← e.toMessageData.toString
    unless s.startsWith s!"VED U1 REFUSED {decl} [{stage}]" do throw e
    pure false
  if accepted then throwError "{decl}: ACCEPTED (expected a refusal at [{stage}])"
  for n in [`ved_mod, `ved_contract, `ved_outs, `ved_body, `ved_u1] do
    if (← getEnv).contains (decl ++ n) then throwError "left behind: {decl ++ n}"
  logInfo m!"refused [{stage}], clean"



/-- info: refused [table], clean -/
#guard_msgs in
run_cmd expectStageRefusal "table" ``dNat

/-- info: refused [table], clean -/
#guard_msgs in
run_cmd expectStageRefusal "table" ``dInst

/-- info: refused [table], clean -/
#guard_msgs in
run_cmd expectStageRefusal "table" ``dFixed

/-! ## Controls on `not`: a wrong module / wrong statement is refused, no theorem

`checkU1E` is the checker below the entry (it takes the module and the
statement separately so a control can substitute them); the module comes from
the real entry run of the declaration above. -/

def modOf (base : Name) : TermElabM Sparkle.IR.AST.Module := do
  let some v := (← getConstInfo (base ++ `ved_mod)).value? | throwError "no value"
  evalModule v

def checkerNames (base : Name) : List Name :=
  [`ved_mod, `ved_contract, `ved_outs, `ved_body, `ved_u1].map (base ++ ·)

def expectRefused (stage : String) (base : Name) (act : TermElabM Unit) :
    CommandElabM Unit := liftTermElabM do
  let accepted ← try act; pure true catch e =>
    let s ← e.toMessageData.toString
    unless s.startsWith "VED U1 REFUSED" && (s.splitOn s!"[{stage}]").length > 1 do throw e
    pure false
  if accepted then throwError "control ACCEPTED (expected a refusal at [{stage}])"
  for n in checkerNames base do
    if (← getEnv).contains n then throwError "left behind: {n}"
  logInfo m!"refused [{stage}], clean"

/-- `@decl defaultDomain` -/
def specOf (decl : Name) : Lean.Expr := mkApp (Lean.mkConst decl) (Lean.mkConst ``defaultDomain)

/-- `not` replaced by the identity (module output = input) -/
def mutNotIdent (m : Sparkle.IR.AST.Module) : Sparkle.IR.AST.Module :=
  { m with body := m.body.map fun s => match s with
      | .assign o (.op .not [a]) => .assign o a
      | s => s }

/-- `not` replaced by arithmetic negation -/
def mutNotNeg (m : Sparkle.IR.AST.Module) : Sparkle.IR.AST.Module :=
  { m with body := m.body.map fun s => match s with
      | .assign o (.op .not a) => .assign o (.op .neg a)
      | s => s }

/-- output port widened to 17 bits -/
def mutNotWidth (m : Sparkle.IR.AST.Module) : Sparkle.IR.AST.Module :=
  { m with outputs := m.outputs.map fun p => { p with ty := .bitVector 17 } }

/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" `ctlNotIdent do
  discard <| checkU1E ``dnotAuto `ctlNotIdent (specOf ``dnotAuto) (mutNotIdent (← modOf ``dnotAuto)) .generated

/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" `ctlNotNeg do
  discard <| checkU1E ``dnotAuto `ctlNotNeg (specOf ``dnotAuto) (mutNotNeg (← modOf ``dnotAuto)) .generated

/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" `ctlNotWidth do
  discard <| checkU1E ``dnotAuto `ctlNotWidth (specOf ``dnotAuto) (mutNotWidth (← modOf ``dnotAuto)) .generated

-- the identity's module against the complement's statement, and back
/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" `ctlIdentIntoNot do
  discard <| checkU1E ``dnotAuto `ctlIdentIntoNot (specOf ``dnotAuto) (← modOf ``didAuto) .generated

/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" `ctlNotIntoIdent do
  discard <| checkU1E ``didAuto `ctlNotIntoIdent (specOf ``didAuto) (← modOf ``dnotAuto) .generated

-- and's module against or's statement, and xor's against and's
/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" `ctlAndIntoOr do
  discard <| checkU1E ``dor8 `ctlAndIntoOr (specOf ``dor8) (← modOf ``dand8) .generated

/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" `ctlOrIntoAnd do
  discard <| checkU1E ``dand8 `ctlOrIntoAnd (specOf ``dand8) (← modOf ``dor8) .generated

-- a proof term of the wrong statement (the identity's theorem for the complement)
/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" `ctlNotTerm do
  discard <| checkU1E ``dnotAuto `ctlNotTerm (specOf ``dnotAuto) (← modOf ``dnotAuto)
    (.term (mkIdent ``didAuto.ved_u1))

end Tests.Ved.U1DomainCheck
