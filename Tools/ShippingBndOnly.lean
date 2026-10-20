import Lean.Elab.Command
import Tools.ShippingNoPortsDeepCommand
import Tools.ShippingDesignCoverage

/-! # Small tools for a hand-made check-free endpoint (round par/d-1)

WRITTEN, NOT BUILT. Nothing here is a theorem about the compiler. The three
tools exist so that a hand-written test (`Tests/Compiler/MemParentFreeTest.lean`)
can state and assert a check-free design-level endpoint for a shape the
generators refuse, WITHOUT retyping the 40-line conclusion of the head
`Tools.ShippingNoPorts.machine_design_noPorts` and WITHOUT a generator name.

## Why the head cannot be applied by a plain term

The depth endpoint `f.machine_design_svNR{n}` is `∃ raw D, hpost ∧ (checks →
Bnd raw D → …)`: its witnesses are not known to be a core run's result, so
its check antecedents cannot be discharged from outside (the note at the end
of the header of `Tools/ShippingChecksCore.lean`). Every built check-free
generator therefore applies the head `machine_design_noPorts` to the
ARGUMENTS of `f.machine_ships_hierNR{n}`'s proof term (its `Reset`, `Bnd`,
`C`, `Bd`, `Inv`, the wired endpoint, the composed theorem): these are read
off the constant's value, not written. `#noports_open_as` does exactly that
with the BUILT function `Tools.ShippingNoPortsDeepCommand.endpointTermX`
(unchanged), for four run theorems the caller names.

## The tools

* `#noports_open_as nm := f n facts outs masked design [x₁, …]` — adds
  `nm` (in the current namespace): `endpointTermX f [x₁, …] [] n facts outs
  masked design`, kernel-checked by `addTheorem` (standard axioms only).
  Its binders: those of `f.machine_ships_hierNR{n}` (…, the run, `f`'s
  reflection, `f`'s closing), then `MachineDefines` of each `xᵢ` at the run's
  contexts. The four theorems must take `hcore hpost entry closes` (the
  output check: then `hg`) first; every further premise must be a conjunct
  of the endpoint's boundary or one of the `xᵢ` reflections
  (`Tools.ShippingNoPortsKidsCommand.dischargeWith`).
* `bnd_only% c [k₁, …]` — a TYPE: the statement of the constant `c` (an
  endpoint of the form above: at least 11 binders, the 11th `f`'s closing;
  conclusion `∃ raw D, P ∧ (Bnd → R)`) with
  - the binders after the 10th DROPPED (the closing and the extra
    reflections),
  - new binders `MachineDefines mctx mref cctx cref kᵢ kᵢ.machineData.shape`,
  - the antecedent `Bnd` REPLACED by `ChildBnd mref cref w`.
  It is refused when `R` or `P` mentions a dropped binder, and when
  `ChildBnd mref cref w` does not occur in `Bnd`. The theorem of that type
  is proved by the caller (from `c`, by giving `Bnd` its components): the
  elaborator proves nothing. `bnd_only_closing% c [k₁, …]` is the same with
  the closing binder KEPT (for an endpoint whose closing is not derived; not
  a check-free statement).
* `#assert_check_free c` — the census's own re-check
  (`Tools.ShippingDesignCoverage.recheck`: every proposition binder and
  every antecedent under the existentials ALLOWED by
  `Tools.ShippingFinalGoalCommand.allowed`, no checker / closing constant,
  `DesignSV` mentioned) on the stored statement of `c`; logs the counts and
  is an ERROR unless it passes. `#log_check_free c` logs the same and is
  never an error. -/
namespace Tools.ShippingBndOnly
open Lean Meta Elab

/-- The statement of `c` with the boundary replaced by `ChildBnd` alone and
the closing binder replaced by the reflections of `ks` (see the header). -/
def bndOnlyType (c : Name) (ks : List Name) (keepClosing : Bool := false) :
    MetaM Lean.Expr := do
  let ci ← getConstInfo c
  forallTelescope ci.type fun xs body => do
    unless xs.size ≥ 11 do
      throwError "{c}: {xs.size} binders, expected at least 11 (the binders of a depth endpoint)"
    let ct ← instantiateMVars (← inferType xs[10]!)
    unless ct.isAppOf ``Tools.ShippingChildInv.MachineClosesAt do
      throwError "{c}: the 11th binder is not the closing:{indentExpr ct}"
    unless body.isAppOfArity ``Exists 2 do
      throwError "{c}: the conclusion is not an existential:{indentExpr body}"
    let lam1 := body.getArg! 1
    unless lam1.isLambda do throwError "{c}: the first existential's body is not a lambda"
    let cb := mkAppN (mkConst ``Tools.ShippingChildInv.ChildBnd) #[xs[1]!, xs[3]!, xs[4]!]
    let ex1 ← withLocalDeclD lam1.bindingName! lam1.bindingDomain! fun raw => do
      let e1 := lam1.bindingBody!.instantiate1 raw
      unless e1.isAppOfArity ``Exists 2 do
        throwError "{c}: no second existential:{indentExpr e1}"
      let lam2 := e1.getArg! 1
      unless lam2.isLambda do throwError "{c}: the second existential's body is not a lambda"
      let ex2 ← withLocalDeclD lam2.bindingName! lam2.bindingDomain! fun dD => do
        let e2 := lam2.bindingBody!.instantiate1 dD
        unless e2.isAppOfArity ``And 2 do
          throwError "{c}: under the existentials there is no conjunction:{indentExpr e2}"
        let pP := e2.getArg! 0
        let imp := e2.getArg! 1
        unless imp.isForall do
          throwError "{c}: the second conjunct is not an implication:{indentExpr imp}"
        let bndT := (← instantiateMVars imp.bindingDomain!).headBeta
        let rR := imp.bindingBody!
        if rR.hasLooseBVars then
          throwError "{c}: the conclusion depends on the proof of the boundary"
        unless (bndT.find? (· == cb)).isSome do
          throwError "{c}: the boundary{indentExpr bndT}\ndoes not mention{indentExpr cb}"
        let inner := mkApp2 (mkConst ``And) pP (← mkArrow cb rR)
        mkAppM ``Exists #[← mkLambdaFVars #[dD] inner]
      mkAppM ``Exists #[← mkLambdaFVars #[raw] ex2]
    let ctx : Array Lean.Expr := #[xs[0]!, xs[1]!, xs[2]!, xs[3]!]
    let decls : Array (Name × (Array Lean.Expr → MetaM Lean.Expr)) :=
      ks.toArray.mapIdx fun i k =>
        (Name.mkSimple s!"hK{i}", fun (_ : Array Lean.Expr) => do
          let shape ← mkAppM ``Tools.ShippingMachineAuto.MachineData.shape
            #[mkConst (k ++ `machineData)]
          mkAppM ``Tools.ShippingMachineEntry.MachineDefines (ctx ++ #[toExpr k, shape]))
    -- the binders kept: through `f`'s reflection, and the closing when asked
    let nKeep : Nat := if keepClosing then 11 else 10
    let ty ← withLocalDeclsD decls fun hs => do
      let ty ← mkForallFVars (xs.extract 0 nKeep ++ hs) ex1
      instantiateMVars ty
    -- a dropped binder (the closing, an extra reflection) must not be mentioned
    for x in xs.extract nKeep xs.size do
      if ty.containsFVar x.fvarId! then
        throwError "{c}: the statement depends on the dropped binder {x}"
    return ty

/-- `bnd_only% c [k₁, …]`: see the header. -/
elab "bnd_only% " c:ident " [" ks:ident,* "]" : term => do
  let cN ← realizeGlobalConstNoOverloadWithInfo c
  let mut kNs : List Name := []
  for k in ks.getElems do
    let kN ← realizeGlobalConstNoOverloadWithInfo k
    kNs := kNs ++ [kN]
  bndOnlyType cN kNs

/-- `bnd_only_closing% c [k₁, …]`: as `bnd_only%`, the closing binder (the
11th) KEPT — for an endpoint whose closing is not derived. Such a statement
is NOT check-free (it asks `MachineClosesAt`). -/
elab "bnd_only_closing% " c:ident " [" ks:ident,* "]" : term => do
  let cN ← realizeGlobalConstNoOverloadWithInfo c
  let mut kNs : List Name := []
  for k in ks.getElems do
    let kN ← realizeGlobalConstNoOverloadWithInfo k
    kNs := kNs ++ [kN]
  bndOnlyType cN kNs (keepClosing := true)

open Command in
/-- `#noports_open_as nm := f n facts outs masked design [x₁, …]`: see the
header. An error where the built function refuses. (No new keyword: the
separators are existing tokens.) -/
elab "#noports_open_as " nm:ident " := " f:ident n:num facts:ident outs:ident masked:ident
    design:ident " [" xs:ident,* "]" : command => do
  let fN ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo f
  let factsN ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo facts
  let outsN ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo outs
  let maskedN ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo masked
  let designN ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo design
  let mut extra : List Name := []
  for x in xs.getElems do
    let xN ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo x
    extra := extra ++ [xN]
  let name := (← getCurrNamespace) ++ nm.getId
  if (← getEnv).contains name then throwError "{name}: exists already"
  let depth := n.getNat
  liftTermElabM <|
    withOptions (fun o => Lean.Elab.async.set o false) do
      let (type, value) ←
        Tools.ShippingNoPortsDeepCommand.endpointTermX fN extra [] depth factsN outsN maskedN
          designN
      Tools.ShippingMachineLinkedCommand.addTheorem name type value
  logInfo m!"NOPORTS OPEN {name}: the head machine_design_noPorts at the arguments of {fN}.machine_ships_hierNR{depth}, its four run hypotheses by {factsN}, {outsN}, {maskedN}, {designN}; extra reflections {extra}; checked by the kernel, standard axioms"

open Command in
/-- `#assert_check_free c`: see the header. -/
elab "#assert_check_free " c:ident : command => do
  let cN ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo c
  let ch ← liftTermElabM <| Tools.ShippingDesignCoverage.recheck cN
  let errLine : String := match ch.err with
    | some e => s!"; the re-check threw: {e}"
    | none => ""
  let line : String :=
    s!"{cN}: proposition binders {ch.props}, antecedents under the existentials {ch.antes}, NOT ALLOWED {ch.bad}, checker / closing constants {ch.checkers}, DesignSV mentioned: {ch.hasDesign}, reported constants of the memory route's list {ch.extra}{errLine}"
  if ch.ok then
    logInfo m!"CHECK-FREE OK {line}"
  else
    throwError "CHECK-FREE FAILED {line}"

open Command in
/-- `#log_check_free c`: the same re-check, LOGGED only (never an error): for
a statement that is known not to pass (a closing premise left). -/
elab "#log_check_free " c:ident : command => do
  let cN ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo c
  let ch ← liftTermElabM <| Tools.ShippingDesignCoverage.recheck cN
  let errLine : String := match ch.err with
    | some e => s!"; the re-check threw: {e}"
    | none => ""
  let verdict : String := if ch.ok then "PASSES" else "DOES NOT PASS"
  logInfo m!"CHECK-FREE LOG {cN}: {verdict} — proposition binders {ch.props}, antecedents under the existentials {ch.antes}, NOT ALLOWED {ch.bad}, checker / closing constants {ch.checkers}, DesignSV mentioned: {ch.hasDesign}{errLine}"

end Tools.ShippingBndOnly
