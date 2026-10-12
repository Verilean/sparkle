import Tools.ShippingFinalGoalCommand
import Tools.ShippingReflectCtx
import Tools.ShippingMachineLinkedCommand

/-! # `#machine_boundary_close thm`: the boundary of a closed endpoint, reduced to what its binders do not give (G1, round par/a-14)

A generated depth endpoint has the shape (`Tools/ShippingFinalGoalCommand.lean`)

    ∀ (binders), ∃ w₁ … wₖ, P ∧ (A₁ → … → Aₘ → C)

and one of the `Aᵢ` is the run boundary: a conjunction
(`Tools/ShippingMachineDepthCommandR.lean` 302–336, 553–559)

    ChildBnd mref cref w ∧ (per child with calls:)
      MachineDefines mctx mref cctx cref c c.shape ∧ names ∧
        ∀ mctx' cctx', ChildRanIn mref cref c mctx' cctx' →
          ∀ wc raw D, ChildBnd mref cref wc → Bnd_c mctx' cctx' wc raw D

where `Bnd_c` is the child's own boundary in the contexts the child is
synthesised in (for a child whose calls are gate children:
`ChildBnd mref cref wc ∧ EntryDefines mctx' mref cctx' cref g g.gateValue`).
The last conjunct is a `∀` over contexts, so the goal-gap classifier
(`allowed`) does not accept the antecedent.

The CLOSED forms (`…_closed`) have the descendants' reflections as BINDERS,
at the run's contexts (the premises of `f.closes_deep`). A reflection does
not depend on the contexts (`Tools.ShippingReflectCtx.MachineDefines.ctx`,
`EntryDefines.ctx`, BUILT). So every conjunct of the boundary that is

* a binder,
* `True`,
* a reflection whose statement at OTHER contexts is a binder,
* a conjunction, or a `∀ … →` whose conclusion is one of these or one of
  its own hypotheses (the `ChildBnd mref cref wc` it assumes),

follows from the binders. `#machine_boundary_close thm` adds `thmB`: the
same statement with each NOT-ALLOWED antecedent `Aᵢ` replaced by the
conjunction of the conjuncts of `Aᵢ` that do NOT follow that way (dropped
if none is left), proved from `thm` by supplying the old antecedent.

Nothing is assumed: `thmB`'s antecedents are conjuncts of `thm`'s, its
binders are `thm`'s, and its proof is `thm` applied. A conjunct that is not
derived is KEPT and logged. If no antecedent changes the command THROWS.

No statement about the compiler is proved here; the only lemmas used are
the two context transfers.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingBoundaryClose
open Lean Meta Elab Command

/-- The conjuncts of a proposition, flattened. -/
partial def conjuncts (t : Lean.Expr) : List Lean.Expr :=
  if t.isAppOfArity ``And 2 then conjuncts (t.getArg! 0) ++ conjuncts (t.getArg! 1) else [t]

/-- The proofs of the flattened conjuncts of `h : t`. -/
partial def parts (h t : Lean.Expr) : Array Lean.Expr :=
  if t.isAppOfArity ``And 2 then
    let a := t.getArg! 0
    let b := t.getArg! 1
    parts (mkApp3 (mkConst ``And.left) a b h) a ++ parts (mkApp3 (mkConst ``And.right) a b h) b
  else #[h]

/-- The right-nested conjunction of a non-empty list. -/
def mkConj : List Lean.Expr → Lean.Expr
  | [] => mkConst ``True
  | [a] => a
  | a :: as => mkAnd a (mkConj as)

/-- `lem h : goal` for a context-transfer lemma `lem : ∀ {…}, X ctx … → X ctx' …`,
its implicit arguments found by unification; `none` if it does not apply. -/
def transfer? (lem : Name) (h goal : Lean.Expr) : MetaM (Option Lean.Expr) :=
  -- the result is a closed term (no metavariable), so the assignments made
  -- to find it need not survive
  withoutModifyingState do
    let c ← mkConstWithFreshMVarLevels lem
    let (ms, _, ty) ← forallMetaTelescope (← inferType c)
    if ms.isEmpty then return none
    let last := ms[ms.size - 1]!
    unless ← isDefEq ty goal do return none
    unless ← isDefEq (← inferType last) (← inferType h) do return none
    unless ← isDefEq last h do return none
    let p ← instantiateMVars (mkAppN c ms)
    if p.hasMVar then return none
    return some p

/-- A proof of `goal` from the hypotheses `hyps`, by: a hypothesis; `True`;
a conjunction; a reflection at other contexts; a `∀ … →` (its proposition
binders become hypotheses); a generated boundary definition
(`….machineBoundN…`), unfolded. `none` otherwise. -/
partial def solve (hyps : Array Lean.Expr) (goal : Lean.Expr) : MetaM (Option Lean.Expr) := do
  let goal ← instantiateMVars goal
  for h in hyps do
    let t ← instantiateMVars (← inferType h)
    if t == goal then return some h
  for h in hyps do
    if ← withReducible (isDefEq (← inferType h) goal) then return some h
  if goal.isConstOf ``True then return some (mkConst ``True.intro)
  if goal.isAppOfArity ``And 2 then
    let a := goal.getArg! 0
    let b := goal.getArg! 1
    let some pa ← solve hyps a | return none
    let some pb ← solve hyps b | return none
    return some (mkApp4 (mkConst ``And.intro) a b pa pb)
  for (head, lem) in [(``Tools.ShippingMachineEntry.MachineDefines,
        ``Tools.ShippingReflectCtx.MachineDefines.ctx),
      (``Tools.ShippingInlineSoundness.EntryDefines,
        ``Tools.ShippingReflectCtx.EntryDefines.ctx)] do
    if goal.isAppOf head then
      for h in hyps do
        let t ← instantiateMVars (← inferType h)
        if t.isAppOf head then
          if let some p ← transfer? lem h goal then return some p
      return none
  if goal.isForall then
    return ← forallTelescope goal fun zs body => do
      let mut hs := hyps
      for z in zs do
        if ← isProp (← inferType z) then hs := hs.push z
      let some p ← solve hs body | return none
      return some (← mkLambdaFVars zs p)
  if let .const n _ := goal.getAppFn then
    if (n.toString.splitOn "machineBoundN").length > 1 then
      if let some g ← unfoldDefinition? goal then
        return ← solve hyps g.headBeta
  return none

/-- The antecedents `A₁ → … → C` under the conjunction: each NOT-ALLOWED one
reduced. `hR : R`. Returns the proof and its statement; `changed` counts the
antecedents that changed; `log` gets one line per conjunct. -/
partial def antes (binders : Array Lean.Expr) (hR R : Lean.Expr)
    (log : IO.Ref (Array String)) (changed : IO.Ref Nat) : MetaM (Lean.Expr × Lean.Expr) := do
  if !(← Tools.ShippingFinalGoalCommand.isPropArrow R) then return (hR, R)
  let A := R.bindingDomain!
  let C := R.bindingBody!
  let keepAsIs : MetaM (Lean.Expr × Lean.Expr) :=
    withLocalDeclD `hA A fun a => do
      let (pr, ty) ← antes binders (mkApp hR a) C log changed
      return (← mkLambdaFVars #[a] pr, ← mkForallFVars #[a] ty)
  if Tools.ShippingFinalGoalCommand.allowed A then
    let ppA := toString (← ppExpr A)
    log.modify (·.push s!"UNCHANGED (allowed) antecedent: {ppA}")
    return ← keepAsIs
  let cs := conjuncts A
  let mut kept : List Lean.Expr := []
  let mut derived : Nat := 0
  for c in cs do
    let ppC := toString (← ppExpr c)
    match ← solve binders c with
    | some _ =>
      derived := derived + 1
      log.modify (·.push s!"DERIVED from the binders: {ppC}")
    | none =>
      kept := kept ++ [c]
      let tag := if Tools.ShippingFinalGoalCommand.allowed c then "KEPT (allowed)" else
        "KEPT (NOT ALLOWED, not derived)"
      log.modify (·.push s!"{tag}: {ppC}")
  if derived == 0 then return ← keepAsIs
  changed.modify (· + 1)
  if kept.isEmpty then
    let some pA ← solve binders A
      | throwError "#machine_boundary_close: every conjunct was derived but not their conjunction{indentExpr A}"
    return ← antes binders (mkApp hR pA) C log changed
  let A' := mkConj kept
  withLocalDeclD `hB A' fun hb => do
    let some pA ← solve (binders ++ parts hb A') A
      | throwError "#machine_boundary_close: the antecedent{indentExpr A}\nis not derived from{indentExpr A'}\nand the binders"
    let (pr, ty) ← antes binders (mkApp hR pA) C log changed
    return (← mkLambdaFVars #[hb] pr, ← mkForallFVars #[hb] ty)

/-- Through the existentials and the conjunction (`gapOf`'s recursion). -/
partial def rebuild (binders : Array Lean.Expr) (h ty : Lean.Expr)
    (log : IO.Ref (Array String)) (changed : IO.Ref Nat) : MetaM (Lean.Expr × Lean.Expr) := do
  if ty.isAppOfArity ``Exists 2 then
    let α := ty.getArg! 0
    let p := ty.getArg! 1
    let nm := if p.isLambda then p.bindingName! else `w
    withLocalDeclD nm α fun w => do
      let body := (mkApp p w).headBeta
      withLocalDeclD `hw body fun hw => do
        let (pr, prTy) ← rebuild binders hw body log changed
        let q ← mkLambdaFVars #[w] prTy
        let goal ← mkAppM ``Exists #[q]
        let inner ← mkAppOptM ``Exists.intro #[none, some q, some w, some pr]
        let f ← mkLambdaFVars #[w, hw] inner
        let v ← mkAppOptM ``Exists.elim #[none, none, some goal, some h, some f]
        return (v, goal)
  else if ty.isAppOfArity ``And 2 then
    let P := ty.getArg! 0
    let R := ty.getArg! 1
    let hP := mkApp3 (mkConst ``And.left) P R h
    let hR := mkApp3 (mkConst ``And.right) P R h
    let (pr, prTy) ← antes binders hR R log changed
    return (mkApp4 (mkConst ``And.intro) P prTy hP pr, mkAnd P prTy)
  else
    throwError "#machine_boundary_close: expected ∃ … , P ∧ (…), found{indentExpr ty}"

/-- `newName`: the endpoint `e` with its not-allowed antecedents reduced to
what the binders of `e` do not give. Throws if nothing changes or `newName`
exists. Returns the log lines. -/
def closeBoundary (e newName : Name) : MetaM (Array String) := do
  if (← getEnv).contains newName then throwError "{newName}: exists already"
  let info ← getConstInfo e
  let log ← IO.mkRef (#[] : Array String)
  let changed ← IO.mkRef (0 : Nat)
  let (type, value) ← forallTelescope info.type fun xs body => do
    let h := mkAppN (mkConst e (info.levelParams.map mkLevelParam)) xs
    let mut binders : Array Lean.Expr := #[]
    for x in xs do
      if ← isProp (← inferType x) then binders := binders.push x
    let (pr, prTy) ← rebuild binders h body log changed
    return (← mkForallFVars xs prTy, ← mkLambdaFVars xs pr)
  if (← changed.get) == 0 then
    throwError "{e}: no conjunct of a not-allowed antecedent follows from the binders (nothing to close):\n{String.intercalate "\n" (← log.get).toList}"
  let type ← instantiateMVars type
  let value ← instantiateMVars value
  Tools.ShippingMachineLinkedCommand.addTheorem newName type value
  return ← log.get

/-- The name of the reduced form: `thm` ↦ `thmB`. -/
def closedBName (e : Name) : Name :=
  match e with
  | .str p s => Name.str p (s ++ "B")
  | n => n ++ `B

/-- `#machine_boundary_close thm`: adds `thmB`; an error if nothing is derived. -/
elab "#machine_boundary_close " d:ident : command => do
  let e ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  let newName := closedBName e
  let report ← liftTermElabM <|
    withOptions (fun o => Lean.Elab.async.set o false) (closeBoundary e newName)
  logInfo m!"BOUNDARY CLOSE {newName} from {e}\n{String.intercalate "\n" report.toList}"

/-- The same, a refusal LOGGED (`BOUNDARY CLOSE REFUSED`) instead of thrown;
an absent theorem is logged `BOUNDARY CLOSE ABSENT`. -/
elab "#machine_boundary_close_try " d:ident : command => do
  let e := d.getId
  unless (← getEnv).contains e do
    logInfo m!"BOUNDARY CLOSE ABSENT {e}"
    return
  let newName := closedBName e
  let savedEnv ← getEnv
  try
    let report ← liftTermElabM <|
      withOptions (fun o => Lean.Elab.async.set o false) (closeBoundary e newName)
    logInfo m!"BOUNDARY CLOSE {newName} from {e}\n{String.intercalate "\n" report.toList}"
  catch ex =>
    setEnv savedEnv
    logInfo m!"BOUNDARY CLOSE REFUSED {e}: {ex.toMessageData}"

end Tools.ShippingBoundaryClose
