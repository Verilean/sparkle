import Tools.ShippingFinalGoal
import Tools.ShippingMachineClosesGen
import Tools.ShippingMachineLinkedCommand

/-! # `#machine_goal_gap f n`: the gap of a generated endpoint, as a statement

The generated SV endpoint of `f` at depth `n`
(`f.machine_design_svNR{n}_closed` if it exists, else
`f.machine_design_svNR{n}`) has the shape

    ∀ (binders), ∃ w₁ … wₖ, P ∧ (A₁ → … → Aₘ → C)

(for the depth endpoints: `∃ raw D, (b = … ∨ b = …) ∧ (checks → … → ∃ ids, …)`).
The command reads that shape from the endpoint's ACTUAL type — it does not
compare it with a fixed head conclusion (round 11 did, and the real endpoint
has one more check, `kidsMaskedN`, and a conjunction for the children's
premise, so that did not unify) — and adds

    f.machine_goal_gap{n} : ∀ (binders),
      (kid_i : Aᵢ)                         -- each ALLOWED antecedent free of the witnesses
      (gap_… : ∀ w₁ … wₖ, P → Aⱼ)          -- every other antecedent, one named hypothesis each
      → ∃ w₁ … wₖ, P ∧ C

proved by instantiating the endpoint (`Exists.elim` / `Exists.intro` /
`And.intro` and applications): kernel-checked, nothing new about the
compiler.

An antecedent is ALLOWED when it is a reflection (`MachineDefines`,
`EntryDefines`), the runtime laws at a start world (`ChildBnd`), the run
(`RunsTo`), or a conjunction of those. Everything else is a gap hypothesis,
named `gap_<head constant>` (for an equation, the head of its left side),
and logged `NOT ALLOWED`. An allowed antecedent that mentions a witness
cannot be moved in front of the existential; it becomes a `gap_…` hypothesis
too and the log says so (`ALLOWED BUT WITNESS-DEPENDENT`).

The endpoint's own binders are classified in the log the same way; they stay
binders of the gap theorem.

What this does NOT give: the conclusion `∃ w…, P ∧ C` is the endpoint's own,
not `Tools.ShippingFinalGoal.RunGoal` (that definition copies the depth-free
head `ships_design_svN_all`; the depth endpoints' `C` differs from it and no
comparison is attempted here). The gap to `MachineGoal` is: the `gap_…`
hypotheses, every binder logged `NOT ALLOWED`, and that difference of `C`. -/
namespace Tools.ShippingFinalGoalCommand
open Lean Meta Elab Command

/-- A hypothesis the final goal allows: the run, a reflection, the runtime
laws at a start world — or a conjunction of such. -/
partial def allowed (t : Lean.Expr) : Bool :=
  t.isAppOf ``Tools.ShippingEntrySoundness.RunsTo ||
  t.isAppOf ``Tools.ShippingMachineEntry.MachineDefines ||
  t.isAppOf ``Tools.ShippingInlineSoundness.EntryDefines ||
  t.isAppOf ``Tools.ShippingChildInv.ChildBnd ||
  (t.isAppOfArity ``And 2 && allowed (t.getArg! 0) && allowed (t.getArg! 1))

/-- The constant a hypothesis is named after: the head, or for an equation
the head of its left side. -/
def headName (t : Lean.Expr) : String :=
  let t := if t.isAppOfArity ``Eq 3 then t.getArg! 1 else t
  match t.getAppFn with
  | .const (.str _ s) _ => s
  | _ => "premise"

/-- One antecedent of the endpoint's inner implication. -/
structure Ante where
  /-- the hypothesis name in the gap theorem -/
  name : Name
  /-- `true`: taken as it is, in front of the existential -/
  hoisted : Bool
  /-- the hypothesis type (no witness free in it) -/
  type : Lean.Expr
  /-- the log line -/
  line : String

/-- An implication between propositions (not a dependent `∀`)? -/
def isPropArrow (t : Lean.Expr) : MetaM Bool := do
  if t.isForall && !t.bindingBody!.hasLooseBVars then isProp t.bindingDomain!
  else return false

/-- Pass 1: the antecedents under the endpoint's existentials. `ws` are the
witnesses opened so far. -/
partial def analyse (ty : Lean.Expr) (ws : Array Lean.Expr) : MetaM (Array Ante) := do
  if ty.isAppOfArity ``Exists 2 then
    let α := ty.getArg! 0
    let p := ty.getArg! 1
    let nm := if p.isLambda then p.bindingName! else `w
    withLocalDeclD nm α fun w => analyse (mkApp p w).headBeta (ws.push w)
  else if ty.isAppOfArity ``And 2 then
    let P := ty.getArg! 0
    let mut R := ty.getArg! 1
    let mut out : Array Ante := #[]
    let mut i := 0
    while (← isPropArrow R) do
      let A := R.bindingDomain!
      let dep := ws.any fun w => A.containsFVar w.fvarId!
      let ok := allowed A
      let pp ← ppExpr A
      if ok && !dep then
        out := out.push
          { name := Name.mkSimple s!"kid_{i}", hoisted := true, type := A,
            line := s!"ALLOWED     kid_{i}: {pp}" }
      else
        let base := s!"gap_{headName A}"
        let nm := if out.any (fun a => a.name == Name.mkSimple base) then s!"{base}_{i}" else base
        let tag := if ok then "ALLOWED BUT WITNESS-DEPENDENT" else "NOT ALLOWED"
        out := out.push
          { name := Name.mkSimple nm, hoisted := false,
            type := ← mkForallFVars ws (← mkArrow P A),
            line := s!"{tag} {nm}: {pp}" }
      R := R.bindingBody!
      i := i + 1
    return out
  else
    throwError "#machine_goal_gap: expected ∃ … , P ∧ (…), found{indentExpr ty}"

/-- Pass 2: from `h : ty` and the hypotheses `hs` (in the antecedents'
order), a proof of the statement without the antecedents, and that
statement. -/
partial def build (antes : Array Ante) (hs : Array Lean.Expr) (h ty : Lean.Expr)
    (ws : Array Lean.Expr) : MetaM (Lean.Expr × Lean.Expr) := do
  if ty.isAppOfArity ``Exists 2 then
    let α := ty.getArg! 0
    let p := ty.getArg! 1
    let nm := if p.isLambda then p.bindingName! else `w
    withLocalDeclD nm α fun w => do
      let body := (mkApp p w).headBeta
      withLocalDeclD `hw body fun hw => do
        let (pr, prTy) ← build antes hs hw body (ws.push w)
        let q ← mkLambdaFVars #[w] prTy
        let goal ← mkAppM ``Exists #[q]
        let inner ← mkAppOptM ``Exists.intro #[none, some q, some w, some pr]
        let f ← mkLambdaFVars #[w, hw] inner
        let v ← mkAppOptM ``Exists.elim #[none, none, some goal, some h, some f]
        return (v, goal)
  else if ty.isAppOfArity ``And 2 then
    let P := ty.getArg! 0
    let hP ← mkAppM ``And.left #[h]
    let mut hR ← mkAppM ``And.right #[h]
    let mut R := ty.getArg! 1
    for a in antes, x in hs do
      let arg := if a.hoisted then x else mkApp (mkAppN x ws) hP
      hR := mkApp hR arg
      R := R.bindingBody!
    return (← mkAppM ``And.intro #[hP, hR], mkAnd P R)
  else
    throwError "#machine_goal_gap: expected ∃ … , P ∧ (…), found{indentExpr ty}"

/-- The gap theorem of endpoint `e`, and the log lines. -/
def gapOf (e newName : Name) : MetaM (Array String) := do
  let info ← getConstInfo e
  let (type, value, report) ← forallTelescope info.type fun xs body => do
    let h := mkAppN (mkConst e (info.levelParams.map mkLevelParam)) xs
    let mut report : Array String := #[]
    for x in xs do
      let t ← instantiateMVars (← inferType x)
      if ← isProp t then
        let tag := if allowed t then "ALLOWED     binder" else "NOT ALLOWED binder"
        report := report.push s!"{tag}: {← ppExpr t}"
    let antes ← analyse body #[]
    report := report ++ antes.map (·.line)
    let decls : Array (Name × (Array Lean.Expr → MetaM Lean.Expr)) :=
      antes.map fun a => (a.name, fun _ => pure a.type)
    withLocalDeclsD decls fun hs => do
      let (pr, prTy) ← build antes hs h body #[]
      let ys := xs ++ hs
      return (← mkForallFVars ys prTy, ← mkLambdaFVars ys pr, report)
  let type ← instantiateMVars type
  let value ← instantiateMVars value
  Tools.ShippingMachineLinkedCommand.addTheorem newName type value
  return report

elab "#machine_goal_gap " d:ident n:num : command => do
  let f ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  let open0 := f ++ Name.mkSimple s!"machine_design_svNR{n.getNat}"
  let closed := Tools.ShippingMachineClosesGen.closedName open0
  let e := if (← getEnv).contains closed then closed else open0
  let newName := f ++ Name.mkSimple s!"machine_goal_gap{n.getNat}"
  let report ← liftTermElabM (gapOf e newName)
  logInfo m!"GOALGAP {newName} from {e}\n{String.intercalate "\n" report.toList}"

end Tools.ShippingFinalGoalCommand
