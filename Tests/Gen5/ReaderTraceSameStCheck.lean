import Tools.ShippingGen5ReaderTraceSameSt
import Tests.Gen3.ExpectedType
set_option autoImplicit false
set_option linter.unusedVariables false
-- NOT BUILT (pending build). Check for Tools/ShippingGen5ReaderTraceSameSt.lean (RT C.CV-2). Clean build is the coder's.

/-! # RT SameSt checks

TYPE: the 2 theorems are compared by `checkExpected` against `Exp…` statements written here (own spelling).
AXIOMS: standard only. CLOSURE: no sorryAx / ofReduceBool / trustCompiler in the closure (with one negative control built in memory). -/

namespace Tests.Gen5.ReaderTraceSameStCheck
open Lean Meta Elab Sparkle.Compiler.Elab Tools.ShippingGen5ReaderTrace Tests.Gen3.ExpectedType
  Tools.ShippingGen5Cover2 Tools.ShippingGen5Cover3 Tools.ShippingGen5Cover5 Tools.ShippingGen5Cover6 Tools.ShippingGen5GDCover1
  Tools.ShippingReaderFuel Tools.ShippingReaderFuelShapeR5 Tools.ShippingLetsReaderInv Tools.ShippingLetsAliasInv Tools.ShippingReaderLenOk
  Tools.Assume.ExprEqv

def ExpFunctional : Prop := ∀ {E : ConstantInfo} {senv : StructEnv} {sp : MachineShape} {n : Nat}
    {p p' : ShapePre} {en en' : Lean.Expr} {st0 st0' : MachRead} {env env' : List MachVal}
    {st1 st1' st st' : MachRead} {v v' : Lean.Expr},
    ∀ (w : StateSideWitness E senv sp n p en st0 env st1 st v)
      (w' : StateSideWitness E senv sp n p' en' st0' env' st1' st' v'),
    p = p' ∧ en = en' ∧ st0 = st0' ∧ env = env' ∧ st1 = st1' ∧ st = st' ∧ v = v'

def ExpReach : Prop := ∀ {n : Nat} {E : ConstantInfo} {senv : StructEnv} {sp : MachineShape} {nDecl : Nat},
    ∀ (hE : EqvAtom) (hT : TraceGood senv nDecl (readF senv n))
      (hn : machineShapeF n false [] E senv true = some (some sp))
      (hIn : ShapeInputs' nDecl senv false [] E n),
    ∀ {p : ShapePre} {en : Lean.Expr} {st0 : MachRead} {env : List MachVal} {st1 st : MachRead} {v : Lean.Expr},
    ∀ (w : StateSideWitness E senv sp n p en st0 env st1 st v),
    FReachC nDecl ({} : MachRead) st0 ∧ FReachC nDecl st0 st1 ∧ FReachC nDecl st1 st ∧
    TrInv senv nDecl st ∧
    ((shapeMid senv p en).wrap? = none → InRange nDecl st st.lets.size v ∧ NoLoose 0 v)

-- mutant: the witness `w'` is for a different fuel (signature rejection, not a semantic counterexample)
def MutFunctional : Prop := ∀ {E : ConstantInfo} {senv : StructEnv} {sp : MachineShape} {n m : Nat}
    {p p' : ShapePre} {en en' : Lean.Expr} {st0 st0' : MachRead} {env env' : List MachVal}
    {st1 st1' st st' : MachRead} {v v' : Lean.Expr},
    ∀ (w : StateSideWitness E senv sp n p en st0 env st1 st v)
      (w' : StateSideWitness E senv sp m p' en' st0' env' st1' st' v'),
    p = p' ∧ en = en' ∧ st0 = st0' ∧ env = env' ∧ st1 = st1' ∧ st = st' ∧ v = v'

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``stateSide_functional ``ExpFunctional
  checkExpected ``reach'_of_witness ``ExpReach
  logInfo m!"RT SAMESTCHECK TYPE 2 theorems compared"
  checkMutant ``stateSide_functional ``MutFunctional
  logInfo m!"RT SAMESTCHECK MUTANT 1 statement mutant rejected (signature/defeq rejection, not a semantic counterexample)"

def thms : List Name := [``stateSide_functional, ``reach'_of_witness]

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in thms do checkAxioms n
  logInfo m!"RT SAMESTCHECK AXIOMS {thms.length} declarations checked (standard axioms only)"

def valueOfCI : ConstantInfo → Option Expr
  | .thmInfo v => some v.value
  | .defnInfo v => some v.value
  | .opaqueInfo v => some v.value
  | _ => none

partial def closureOf (env : Environment) (root : Name) : StateT NameSet MetaM Unit := do
  if (← get).contains root then return
  modify fun s => s.insert root
  match env.find? root with
  | none => pure ()
  | some ci =>
    for c in ci.type.getUsedConstants do closureOf env c
    match valueOfCI ci with
    | some v => for c in v.getUsedConstants do closureOf env c
    | none => pure ()
    match ci with
    | .inductInfo v => for c in v.ctors do closureOf env c
    | _ => pure ()

def forbiddenConsts : List Name := [``sorryAx, ``Lean.ofReduceBool, ``Lean.trustCompiler]

def closureHits (env : Environment) (roots : List Name) : MetaM (List Name) := do
  let (_, seen) ← (roots.forM (closureOf env)).run {}
  pure (forbiddenConsts.filter seen.contains)

run_cmd Lean.Elab.Command.liftTermElabM do
  withoutModifyingEnv do
    let tru := mkConst ``True
    let bad := mkApp2 (mkConst ``sorryAx [Level.zero]) tru (mkConst ``Bool.false)
    addDecl (.defnDecl { name := `Other.Ns.helperD, levelParams := [], type := tru, value := bad, hints := .abbrev, safety := .safe })
    addDecl (.thmDecl { name := `ReaderTraceSameStCheck.viaHelper, levelParams := [], type := tru, value := mkConst `Other.Ns.helperD })
    let env ← getEnv
    if (← closureHits env [`ReaderTraceSameStCheck.viaHelper]).isEmpty then
      throwError "RT SAMESTCHECK CLOSURE CONTROL FAILED: negative control not detected"
  let hits ← closureHits (← getEnv) thms
  unless hits.isEmpty do throwError "RT SAMESTCHECK CLOSURE: forbidden {hits}"
  logInfo m!"RT SAMESTCHECK CLOSURE OK: no sorryAx / ofReduceBool / trustCompiler in the closure of {thms.length} theorems (1 negative control detected)"

run_cmd Lean.Elab.Command.liftTermElabM do
  logInfo m!"RT SAMESTCHECK COUNTS: TYPE 2 / MUTANT 1 / AXIOMS 2 / CLOSURE 2 roots + 1 negative control"

end Tests.Gen5.ReaderTraceSameStCheck
