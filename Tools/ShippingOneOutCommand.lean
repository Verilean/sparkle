import Tools.ShippingOneOutHead
import Tools.ShippingShipsFreeCommand
import Tools.ShippingMachineComposeRCommand
import Tools.ShippingMachineClosesAtGen

/-! # `#machine_design_svH_free f (Extra) [facts, typed, design, outs]` (G1, rounds par/a-6, par/a-7)

`f.machine_ships_hierHR` is `machine_ships_hierHC` applied to the
generator's arguments (`Tools/ShippingMachineComposeRCommand.lean`). This
command applies `Tools.ShippingOneOutHead.machine_design_svH_free` to THE
SAME sixteen arguments (read off that theorem's proof term, as
`#machine_no_ships` does for the sequential head), to the residual premise
`Extra : Module → Design → Prop` given as a term, and discharges the head's
four hypotheses with four NAMED theorems of the caller's:

* `facts  : … → RunFactsH D.modules b`
* `typed  : … → hierTyped (childMap D.modules) b = true`
* `design : … → designCheck (childMap D.modules) 0 (checkedOptimize b) = true`
* `outs   : … → hierGate b = true → … → outsCheck (childMap D.modules) 0 (checkedOptimize b) = true`

each of the form `∀ {contexts, worlds, raw, b, D} (hcore) (hpost) (entry)
(closes) …`: the first four explicit arguments are supplied (for `outs`
also the gate), every further hypothesis must be a conjunct of the
endpoint's boundary or of the residual premise `Extra b D`
(`Tools.ShippingShipsFreeCommand.discharge`); anything else is an error
naming it.

It adds `f.machine_design_svH_free : ∀ {contexts, run} hr entry closes,
∃ raw D, … ∧ (Extra b D → Bnd → …)` (beta-reduced, so the residual premise
is displayed as given) and, when `f.machine_closes_at` exists, its `_closed`
form. `Extra` is ONE antecedent; it may hold SEVERAL INDEPENDENT conditions
(at `caller`: two — `hierTyped … = true` and `portsMatchB … = true`). The
command's log counts the residual-only checker constants the statement
mentions; it does not call the endpoint check-free.

## The generation contract (review of 7fa6a19f, point 2)

* **Every run rebuilds the statement and the proof** from the arguments
  given NOW (`build`: the `Extra` term and the four theorems are applied to
  the head again), whether or not `f.machine_design_svH_free` exists.
* **Name already present.** The existing constant must be a theorem without
  universe parameters, on standard axioms, whose type `isDefEq` the type
  rebuilt now, AND whose recorded lemma list (the doc string this command
  attaches, `usedMarker`) is the list given now. Otherwise the command
  THROWS, naming the existing statement and the rebuilt one (or the two
  lemma lists). On agreement it logs `SVHFREE PRESENT …: already present,
  statement verified against the given Extra` — a line distinct from the
  `SVHFREE GENERATED` line of a fresh generation. There is no silent
  return.
* **Lemma record.** A fresh theorem gets the doc string
  `usedMarker facts typed design outs`; both log lines repeat the four
  names.
* **Refuse scan, first line (direct).** The produced statement (and the
  closed form's) is refused if it mentions `shipsHierHCheck`, `hierCheck`,
  `kidsLocal`, `kidsComb`, `designCheck` or `outsCheck`; `hierTyped` and
  `portsMatchB` are refused unless the given `Extra` itself mentions them
  (then they are the DECLARED residual). LIMIT: this walks the constants
  WRITTEN in the statement. It guarantees nothing about what a definition
  mentioned by the statement contains: with `def myCheck C m := designCheck
  C 0 m`, a residual `fun b D => myCheck … = true` passes the direct scan.
* **Refuse scan, second line (`hidden`, delta expansion of the premises).**
  For every PREMISE of the statement (the type of a proposition binder, at
  the top or under the conclusion's `∃` / `∧` / `→`), the command descends
  through `∀`, `→`, `∃ x, _` (a lambda body), `∧`, `∨`, `↔`, `¬` and both
  sides of `=`, and at each remaining leaf delta-expands the HEAD constant
  (`Lean.Meta.delta?`: the definition's value instantiated, whatever its
  reducibility attribute; then head beta) up to `hiddenFuel` = 3 times along
  a path, descending again after each step. A forbidden or residual-only
  constant found in a term PRODUCED BY AN EXPANSION is refused — the
  residual must be displayed, not named. The six forbidden and the two
  residual-only constants themselves are never expanded.
  What this second line still CANNOT see: an alias that is not at the head
  of a premise leaf (an argument, e.g. `g (myCheck …) = true` where `g` is
  not itself expanded to expose it at a head); more than three definitions
  deep; a checker reached through a structure field, an instance, a
  recursor or matcher application, an `opaque` constant or a theorem-valued
  term (`Classical.choose`, a `Decidable` instance); anything in the final
  CONCLUSION (only premises are expanded); and a checker that is logically
  equivalent but not one of the eight listed constants. The scan is an
  audit of the generation contract, not a soundness device: the theorem is
  kernel-checked whatever it mentions.

This is not a generator of the four theorems: they are written by hand per
declaration (`Tests/Compiler/OneOutCallerTest.lean`). Nothing is assumed:
the result is kernel-checked on standard axioms.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingOneOutCommand
open Lean Meta Elab Command

/-- The checker constants the produced statement must not mention. -/
def forbidden : List Name :=
  [``Tools.ShippingHierPremises.shipsHierHCheck,
   ``Tools.ShippingHierPremisesBase.hierCheck,
   ``Tools.ShippingHierOptRunH.kidsLocal,
   ``Tools.ShippingMachineDepthH.kidsComb,
   ``Tools.ShippingDesignSV.designCheck,
   ``Tools.ShippingDesignSVBack.outsCheck]

/-- The checker constants allowed only as the declared residual. -/
def residualOnly : List Name :=
  [``Tools.ShippingHierTyped.hierTyped, ``Tools.ShippingDesignSV.portsMatchB]

/-- The constants of `cs` WRITTEN in `e` (no definition is opened). -/
def mentioned (cs : List Name) (e : Lean.Expr) : List Name :=
  cs.filter fun c => (e.find? (·.isConstOf c)).isSome

/-- How many head delta steps `hidden` takes along one path. -/
def hiddenFuel : Nat := 3

/-- The constants of `cs` found in terms PRODUCED by delta-expanding the
head of a premise of `e0` (`prem`: we are inside a premise; `unfolded`: the
term at hand came out of an expansion). The file header says what is walked
and what is not. -/
partial def hidden (cs : List Name) (fuel : Nat) (prem unfolded : Bool) (e0 : Lean.Expr) :
    MetaM (List Name) := do
  let e := (← instantiateMVars e0).headBeta
  match e with
  | .mdata _ b => hidden cs fuel prem unfolded b
  | .forallE .. =>
    forallTelescope e fun xs body => do
      let mut acc : List Name ← hidden cs fuel prem unfolded body
      for x in xs do
        let t ← instantiateMVars (← inferType x)
        if ← isProp t then
          acc := acc ++ (← hidden cs fuel true unfolded t)
      return acc
  | _ =>
    let fn := e.getAppFn
    let args := e.getAppArgs
    if (fn.isConstOf ``And || fn.isConstOf ``Or || fn.isConstOf ``Iff) && args.size == 2 then
      return (← hidden cs fuel prem unfolded args[0]!) ++ (← hidden cs fuel prem unfolded args[1]!)
    else if fn.isConstOf ``Not && args.size == 1 then
      hidden cs fuel prem unfolded args[0]!
    else if fn.isConstOf ``Eq && args.size == 3 then
      return (← hidden cs fuel prem unfolded args[1]!) ++ (← hidden cs fuel prem unfolded args[2]!)
    else if fn.isConstOf ``Exists && args.size == 2 && args[1]!.isLambda then
      lambdaTelescope args[1]! fun _ body => hidden cs fuel prem unfolded body
    else if !prem then
      return []
    else
      let here : List Name := if unfolded then mentioned cs e else []
      match fuel with
      | 0 => return here
      | fuel' + 1 =>
        match ← Lean.Meta.delta? e (fun n => !cs.contains n) with
        | some e' => return here ++ (← hidden cs fuel' prem true e')
        | none => return here

/-- REFUSE a statement mentioning a forbidden constant, or a residual-only
one the declared residual does not mention (the DIRECT scan); then REFUSE a
statement one of whose premises, delta-expanded at its head up to
`hiddenFuel` steps, yields one of those constants (the `hidden` scan). The
limits of both are in the file header. -/
def refuse (name : Name) (type extra : Lean.Expr) : MetaM Unit := do
  for c in forbidden do
    if (type.find? (·.isConstOf c)).isSome then
      throwError "{name}: REFUSED, the statement still mentions {c}"
  for c in residualOnly do
    if (type.find? (·.isConstOf c)).isSome && !(extra.find? (·.isConstOf c)).isSome then
      throwError "{name}: REFUSED, the statement mentions {c}, which is not in the declared residual"
  let hid ← hidden (forbidden ++ residualOnly) hiddenFuel false false type
  unless hid.isEmpty do
    throwError "{name}: REFUSED, a premise of the statement hides {hid.eraseDups} inside a definition (found by delta-expanding premise heads, {hiddenFuel} steps); a check premise must be written in the statement, not named by an alias"

/-- The record of the four theorems a generated endpoint was built from: its
doc string, and what a re-run compares. -/
def usedMarker (facts typed design outs : Name) : String :=
  s!"[svH_free lemmas: facts := {facts}, typed := {typed}, design := {design}, outs := {outs}]"

/-- The statement (beta-reduced) and the proof of `f.machine_design_svH_free`
from `f.machine_ships_hierHR`'s arguments, the residual `extra` and the four
theorems GIVEN NOW. Adds nothing to the environment. -/
def build (f : Name) (extra : Lean.Expr) (facts typed design outs : Name) :
    MetaM (Lean.Expr × Lean.Expr) := do
  let ships := f ++ `machine_ships_hierHR
  let some (.thmInfo ti) := (← getEnv).find? ships
    | throwError "{ships}: not a theorem (run #machine_design_svHR first)"
  let v := ti.value
  unless v.isAppOf ``Tools.ShippingMachineShipsHierH.machine_ships_hierHC do
    throwError "{ships}: not built from machine_ships_hierHC"
  let a := v.getAppArgs
  unless a.size == 16 do
    throwError "{ships}: {a.size} arguments of machine_ships_hierHC, expected 16"
  let value ← forallTelescope (← inferType (mkConst ships)) fun xs _ => do
    unless xs.size == 11 do throwError "{ships}: {xs.size} binders, expected 11"
    -- R Bnd C {declName} d {kD ι dom src ext extL srcL lsrc} soundL composed houtTy,
    -- Extra, then the run's binders (mctx mref cctx cref w w' b design hr entry closes)
    let args : Array (Option Lean.Expr) := a.map some ++ #[some extra] ++ xs.map some
    let pre ← instantiateMVars
      (← mkAppOptM ``Tools.ShippingOneOutHead.machine_design_svH_free args)
    if pre.hasMVar then throwError "{f}: the head's arguments were not all inferred"
    -- the run's facts: raw D w1 hcore hpost hBnd
    let .forallE _ TF _ _ ← whnfR (← inferType pre)
      | throwError "{f}: the head's run-facts hypothesis is not where it is expected"
    let hFacts ← forallTelescope TF fun zs goal => do
      unless zs.size == 6 do throwError "{f}: the run-facts hypothesis has {zs.size} binders"
      let p ← mkAppM facts #[zs[3]!, zs[4]!, xs[9]!, xs[10]!]
      mkLambdaFVars zs (← Tools.ShippingShipsFreeCommand.discharge facts p zs[5]! goal)
    let pre := mkApp pre hFacts
    -- the width typing: raw D w1 hcore hpost hBnd hExtra
    let .forallE _ TT _ _ ← whnfR (← inferType pre)
      | throwError "{f}: the head's typing hypothesis is not where it is expected"
    let hTyped ← forallTelescope TT fun zs goal => do
      unless zs.size == 7 do throwError "{f}: the typing hypothesis has {zs.size} binders"
      let p ← mkAppM typed #[zs[3]!, zs[4]!, xs[9]!, xs[10]!]
      let both ← mkAppM ``And.intro #[zs[5]!, zs[6]!]
      mkLambdaFVars zs (← Tools.ShippingShipsFreeCommand.discharge typed p both goal)
    let pre := mkApp pre hTyped
    -- `designCheck`: raw D w1 hcore hpost hBnd hExtra
    let .forallE _ TD _ _ ← whnfR (← inferType pre)
      | throwError "{f}: the head's designCheck hypothesis is not where it is expected"
    let hDesign ← forallTelescope TD fun zs goal => do
      unless zs.size == 7 do throwError "{f}: the designCheck hypothesis has {zs.size} binders"
      let p ← mkAppM design #[zs[3]!, zs[4]!, xs[9]!, xs[10]!]
      let both ← mkAppM ``And.intro #[zs[5]!, zs[6]!]
      mkLambdaFVars zs (← Tools.ShippingShipsFreeCommand.discharge design p both goal)
    let pre := mkApp pre hDesign
    -- the output check under the gate: raw D w1 hcore hpost hg hBnd
    let .forallE _ TO _ _ ← whnfR (← inferType pre)
      | throwError "{f}: the head's output-check hypothesis is not where it is expected"
    let hOuts ← forallTelescope TO fun zs goal => do
      unless zs.size == 7 do throwError "{f}: the output-check hypothesis has {zs.size} binders"
      let p ← mkAppM outs #[zs[3]!, zs[4]!, xs[9]!, xs[10]!, zs[5]!]
      mkLambdaFVars zs (← Tools.ShippingShipsFreeCommand.discharge outs p zs[6]! goal)
    mkLambdaFVars xs (mkApp pre hOuts)
  let value ← instantiateMVars value
  let type ← Core.betaReduce (← instantiateMVars (← inferType value))
  return (type, value)

/-- `f.machine_design_svH_free`: built from the arguments given now; ADDED
when the name is free (`true`), VERIFIED against the existing theorem
otherwise (`false`) — same statement up to `isDefEq`, same recorded lemmas,
standard axioms — and an error on any difference. Never a silent return. -/
def generate (f : Name) (extra : Lean.Expr) (facts typed design outs : Name) :
    MetaM (Name × Bool) := do
  let name := f ++ `machine_design_svH_free
  let (type, value) ← build f extra facts typed design outs
  refuse name type extra
  let marker := usedMarker facts typed design outs
  if (← getEnv).contains name then
    let some (.thmInfo ni) := (← getEnv).find? name
      | throwError "{name} exists and is not a theorem: REFUSED"
    unless ni.levelParams.isEmpty do
      throwError "{name} exists with universe parameters: REFUSED"
    unless ← isDefEq ni.type type do
      throwError "{name}: REFUSED, it exists with ANOTHER statement than the one the given Extra and theorems produce.\nexisting:{indentExpr ni.type}\nrebuilt now:{indentExpr type}"
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
def svHFree (f : Name) (extraStx : Term) (facts typed design outs : Name) : CommandElabM Unit := do
  let (name, fresh, nres, closed?) ← liftTermElabM <|
    withOptions (fun o => maxRecDepth.set (Lean.Elab.async.set o false) 1000000) <|
      withTheReader Core.Context (fun c => { c with maxRecDepth := 1000000 }) do
        let ty ← Term.elabType
          (← `(Sparkle.IR.AST.Module → Sparkle.IR.AST.Design → Prop))
        let ex ← Term.elabTermEnsuringType extraStx ty
        Term.synthesizeSyntheticMVarsNoPostponing
        let ex ← instantiateMVars ex
        if ex.hasMVar then throwError "{f}: the residual premise has unassigned parts"
        let (name, fresh) ← generate f ex facts typed design outs
        let nres : Nat := (mentioned residualOnly (← getConstInfo name).type).length
        -- the closed form: `closeEndpointAt` itself verifies an existing
        -- constant of that name against the statement it builds; its
        -- statement goes through the same two scans
        let cl := f ++ `machine_closes_at
        let mut closed? : Option Name := none
        if (← getEnv).contains cl then
          let nn := Tools.ShippingMachineClosesGen.closedName name
          if ← Tools.ShippingMachineClosesAtGen.closeEndpointAt f cl name nn then
            refuse nn (← getConstInfo nn).type ex
            closed? := some nn
        return (name, fresh, nres, closed?)
  let made : List Name := match closed? with
    | some nn => [name, nn]
    | none => [name]
  let used := usedMarker facts typed design outs
  let left : String :=
    if nres == 0 then "no residual-only checker constant is written in the statement"
    else s!"{nres} INDEPENDENT residual check condition(s) remain in the statement, inside the one antecedent Extra (the endpoint is NOT check-free)"
  if fresh then
    logInfo m!"SVHFREE GENERATED {made}: the combinational endpoint without the shipsHierHCheck, kidsComb, designCheck and outsCheck antecedents; {left}; {used}"
  else
    logInfo m!"SVHFREE PRESENT {made}: already present, statement verified against the given Extra (rebuilt from the arguments given now, compared by isDefEq; recorded lemmas equal); nothing added; {left}; {used}"

/-- `#machine_design_svH_free f (Extra) [facts, typed, design, outs]`. -/
elab "#machine_design_svH_free " d:ident ppSpace "(" e:term ")" ppSpace
    "[" facts:ident "," typed:ident "," design:ident "," outs:ident "]" : command => do
  let f ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  let facts ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo facts
  let typed ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo typed
  let design ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo design
  let outs ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo outs
  svHFree f e facts typed design outs

end Tools.ShippingOneOutCommand
