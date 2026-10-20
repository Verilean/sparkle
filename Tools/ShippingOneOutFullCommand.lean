import Tools.ShippingOneOutCommand

/-! # `#machine_design_svH_full f [facts, typed, design, outs]` (G1, round par/a-8)

The sibling of `#machine_design_svH_free` for the case where NO residual
check condition is left: it adds `f.machine_design_svH_full` (and, when
`f.machine_closes_at` exists, `f.machine_design_svH_full_closed`) — the
combinational endpoint of `f` with no check antecedent at all.

It reuses `Tools.ShippingOneOutCommand.build` (the head applied to
`f.machine_ships_hierHR`'s sixteen arguments and to the four named theorems)
with the residual `fun _ _ => True`. The head's shape then gives

    ∀ …, ∃ raw D, hpost ∧ (True → Bnd → …)

and the antecedent `True` is DISCHARGED here (`strip_true`: `trivial` in the
proof), so the stated type is

    ∀ …, ∃ raw D, hpost ∧ (Bnd → …)

with no residual antecedent. The command throws if the antecedent after
`hpost ∧` is still `True` (`noTrueAntecedent`).

A DIFFERENT NAME, on purpose: `#machine_design_svH_free`'s contract refuses
a re-run with another residual on `f.machine_design_svH_free`; that
endpoint (two residual conditions at `caller`) stays as the record of the
intermediate state.

The contract is that command's:

* every run rebuilds statement and proof from the four theorems given now;
* an existing `f.machine_design_svH_full` must be a theorem without universe
  parameters, on standard axioms, of a type `isDefEq` the rebuilt one,
  recorded (doc string, `fullMarker`) as built from the same four theorems —
  else the command throws, naming both; logs `SVHFULL GENERATED` (fresh) /
  `SVHFULL PRESENT … statement verified` (existing);
* the refuse scans of `Tools.ShippingOneOutCommand.refuse` run on the
  statement and on the closed form's, with a residual that mentions no
  checker: so ALL EIGHT checker constants (`shipsHierHCheck`, `hierCheck`,
  `kidsLocal`, `kidsComb`, `designCheck`, `outsCheck`, `hierTyped`,
  `portsMatchB`) are refused, written or found by the head delta expansion
  of the premises (`hidden`, 3 steps). The limits of both scans are in that
  file's header and hold here unchanged.

Nothing is assumed: the result is kernel-checked on standard axioms. The
command says nothing about WHICH declarations have the four theorems; they
are written by hand per declaration.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingOneOutFullCommand
open Lean Meta Elab Command

/-- A trivially true antecedent under two existentials and a conjunction is
discharged. -/
theorem strip_true {α β : Type} {A R : α → β → Prop}
    (h : ∃ a b, A a b ∧ (True → R a b)) : ∃ a b, A a b ∧ R a b := by
  obtain ⟨a, b, h1, h2⟩ := h
  exact ⟨a, b, h1, h2 trivial⟩

/-- The record of the four theorems a generated full endpoint was built
from. -/
def fullMarker (facts typed design outs : Name) : String :=
  s!"[svH_full lemmas: facts := {facts}, typed := {typed}, design := {design}, outs := {outs}]"

/-- Under the binders, the existentials and the left conjunct of an endpoint
statement: is the first antecedent `True`? -/
partial def trueAntecedent (e : Lean.Expr) : Bool :=
  match e with
  | .forallE _ _ b _ => trueAntecedent b
  | .mdata _ b => trueAntecedent b
  | _ =>
    if e.isAppOfArity ``Exists 2 then
      match e.getArg! 1 with
      | .lam _ _ b _ => trueAntecedent b
      | _ => false
    else if e.isAppOfArity ``And 2 then
      let r := e.getArg! 1
      r.isForall && !r.bindingBody!.hasLooseBVars && r.bindingDomain!.isConstOf ``True
    else false

/-- `f.machine_design_svH_full`: statement and proof with the `True`
antecedent discharged. Adds nothing to the environment. -/
def buildFull (f : Name) (facts typed design outs : Name) : MetaM (Lean.Expr × Lean.Expr) := do
  let tyE := mkForall `b .default (mkConst ``Sparkle.IR.AST.Module)
    (mkForall `D .default (mkConst ``Sparkle.IR.AST.Design) (mkSort .zero))
  let extra := mkLambda `b .default (mkConst ``Sparkle.IR.AST.Module)
    (mkLambda `D .default (mkConst ``Sparkle.IR.AST.Design) (mkConst ``True))
  unless ← isDefEq (← inferType extra) tyE do
    throwError "{f}: the trivial residual is not of type Module → Design → Prop"
  let (type0, value0) ← Tools.ShippingOneOutCommand.build f extra facts typed design outs
  -- type0 = ∀ xs, ∃ raw D, hpost ∧ (True → …), beta-reduced
  let value ← forallTelescope type0 fun xs body => do
    let p ← mkExpectedTypeHint (mkAppN value0 xs) body
    let q ← mkAppM ``strip_true #[p]
    mkLambdaFVars xs q
  let value ← instantiateMVars value
  let type ← Core.betaReduce (← instantiateMVars (← inferType value))
  if trueAntecedent type then
    throwError "{f}: the trivially true residual is still an antecedent of the statement"
  return (type, value)

/-- ADD (`true`) or VERIFY (`false`) `f.machine_design_svH_full`; an error on
any difference with an existing constant of that name. -/
def generate (f : Name) (facts typed design outs : Name) : MetaM (Name × Bool) := do
  let name := f ++ `machine_design_svH_full
  let (type, value) ← buildFull f facts typed design outs
  -- no checker constant may be written or hidden: the residual given to the
  -- scan mentions none
  Tools.ShippingOneOutCommand.refuse name type (mkConst ``True)
  let marker := fullMarker facts typed design outs
  if (← getEnv).contains name then
    let some (.thmInfo ni) := (← getEnv).find? name
      | throwError "{name} exists and is not a theorem: REFUSED"
    unless ni.levelParams.isEmpty do
      throwError "{name} exists with universe parameters: REFUSED"
    unless ← isDefEq ni.type type do
      throwError "{name}: REFUSED, it exists with ANOTHER statement than the one the given theorems produce.\nexisting:{indentExpr ni.type}\nrebuilt now:{indentExpr type}"
    let doc? ← Lean.findDocString? (← getEnv) name
    let recorded : Bool := match doc? with
      | some doc => (doc.splitOn marker).length > 1
      | none => false
    unless recorded do
      throwError "{name}: REFUSED, it exists with the same statement but is not recorded as built from the theorems given now.\nrecorded: {doc?}\ngiven now: {marker}"
    for ax in ← Lean.collectAxioms name do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{name} (existing) uses a non-standard axiom: {ax}"
    return (name, false)
  Tools.ShippingMachineLinkedCommand.addTheorem name type value
  addDocStringCore name marker
  return (name, true)

/-- The endpoint, its closed form, and the log line. -/
def svHFull (f : Name) (facts typed design outs : Name) : CommandElabM Unit := do
  let (name, fresh, closed?) ← liftTermElabM <|
    withOptions (fun o => maxRecDepth.set (Lean.Elab.async.set o false) 1000000) <|
      withTheReader Core.Context (fun c => { c with maxRecDepth := 1000000 }) do
        let (name, fresh) ← generate f facts typed design outs
        let cl := f ++ `machine_closes_at
        let mut closed? : Option Name := none
        if (← getEnv).contains cl then
          let nn := Tools.ShippingMachineClosesGen.closedName name
          if ← Tools.ShippingMachineClosesAtGen.closeEndpointAt f cl name nn then
            Tools.ShippingOneOutCommand.refuse nn (← getConstInfo nn).type (mkConst ``True)
            closed? := some nn
        return (name, fresh, closed?)
  let made : List Name := match closed? with
    | some nn => [name, nn]
    | none => [name]
  let used := fullMarker facts typed design outs
  if fresh then
    logInfo m!"SVHFULL GENERATED {made}: the combinational endpoint with NO check antecedent and no residual (the trivially true residual discharged; none of the eight checker constants written in the statement or found by the premise expansion); {used}"
  else
    logInfo m!"SVHFULL PRESENT {made}: already present, statement verified against the theorems given now (rebuilt, compared by isDefEq; recorded lemmas equal); nothing added; {used}"

/-- `#machine_design_svH_full f [facts, typed, design, outs]`. -/
elab "#machine_design_svH_full " d:ident ppSpace
    "[" facts:ident "," typed:ident "," design:ident "," outs:ident "]" : command => do
  let f ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  let facts ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo facts
  let typed ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo typed
  let design ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo design
  let outs ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo outs
  svHFull f facts typed design outs

end Tools.ShippingOneOutFullCommand
