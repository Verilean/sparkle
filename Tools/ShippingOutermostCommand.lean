import Tools.ShippingOutermost
import Tools.ShippingKidFactsRan
import Tools.ShippingMachineSeqLinkedRan
import Tools.ShippingNoPortsDeepCommand
import Tools.ShippingBoundaryClose
import Tools.ShippingMachineSeqCommand

/-! # The check-free depth endpoint at OUTERMOST starts: three term builders (round par/g-1)

WRITTEN, NOT BUILT. NEW file; no built file, generator or endpoint is
changed by it, and nothing here is run on import. Nothing here is a theorem
about the compiler: every function builds a term from BUILT theorems and
hands it to the kernel (`addTheorem`: standard axioms only).

The built check-free endpoint `f.machine_design_noPortsNR{n}` is the head
`Tools.ShippingNoPorts.machine_design_noPorts` at the arguments of
`f.machine_ships_hierNR{n}`'s proof term, with `C := MachineClosesAt …`.
The head is parametric in `C` and in the boundary `Bnd`. The outermost form
is the SAME head at

    C   := fun _ _ _ _ => True
    Bnd := fun mctx mref cctx cref w m D =>
             Bnd₀ mctx mref cctx cref w m D ∧ RanAt mctx mref cctx cref f f.shape w m D

(`Bnd₀`: the built boundary; `Tools.ShippingOutermost.RanAt`: every core run
from `w` returning `(m, D)` performed a machine synthesis that returned it).
The head's six hypotheses are then filled from the `_ran` forms:

| hypothesis of the head | built form (asks `MachineClosesAt`) | here |
|---|---|---|
| `soundL` (the wired endpoint) | `<head>RA args … hr entry closes hsyn` | `<head>RA_ran args … ran` (`Tools/ShippingMachineSeqLinkedRan.lean`) |
| `composed` | `f.machine_composedNR{n} … closes hBnd` | `composedOfTrace` below |
| `hFacts`, `hOuts`, `hBdRun`, `hDesign` | four per-declaration theorems taking `hcore hpost entry closes` | four taking `hpost ran` |

## `composedOfTrace`: the composed theorem with the wired endpoint as a hypothesis

`f.machine_composedNR{n}` is GENERATED (`Tools/ShippingMachineDepthCommandR.lean`,
`generateCoreNR`): there is no source text to split. By READING of that
generator, its proof term uses the closing binder in exactly one way — as an
argument of the wired head `<head>RA args mctx … hr entry closes hsyn`
(`h := mkAppN pL xs`, the first explicit argument of
`machine_linkedT_callsRN`). `composedOfTrace` takes the stored proof term,
replaces that application by a hypothesis `hT` of its type, CHECKS that the
closing binder no longer occurs, and adds

    ∀ (the first ten binders) (hBnd : Bnd₀ …) (hT : MachineTraceLBX (ServedReal …) …), <the same conclusion>

It throws if the application is not found or the closing occurs elsewhere:
the reading is then wrong and nothing is added.

## `openTerm`, `closeOutermost`

* `openTerm`: the head at the arguments above; binders: the first TEN of
  `f.machine_ships_hierNR{n}` (through `f`'s reflection — NOT its closing),
  then the extra reflections. Conclusion: `∃ raw D, P ∧ (Bnd₀ ∧ RanAt → R)`.
* `closeOutermost`: from that, with the reflections of the descendants and
  `Start0 mref cref w` as binders: `∃ raw D, P ∧ R`. The boundary `Bnd₀` is
  derived by `Tools.ShippingBoundaryClose.solve` (BUILT: a hypothesis, `True`,
  a conjunction, a reflection at other contexts, a `∀ … →`) from the
  binders and `Start0.childBnd`; `RanAt` by the theorem the caller names.
  It THROWS, with one line per conjunct, if a conjunct is not derived.

SCOPE of anything built with these: outermost starts only (`Start0`: for the
law witness, the synthesis depth reads 0). `Start0` is NOT ALLOWED by
`Tools.ShippingFinalGoalCommand.allowed` and is not added to it. -/
namespace Tools.ShippingOutermostCommand
open Lean Meta Elab
open Tools.ShippingMachineLinkedCommand (addTheorem)

/-- The wired head of `f`'s endpoint over `MachineRan`
(`Tools/ShippingMachineSeqLinkedRan.lean`), with the leading arguments of
`f.machine_sound`'s proof term. -/
def ranHead (f : Name) : MetaM (Name × Name × Array Lean.Expr) := do
  let (headL, args, back?) ← Tools.ShippingMachineSeqCommand.endpointParts f
  if back?.isSome then throwError "{f}: a transported endpoint (not handled at outermost starts)"
  let headA := headL.appendAfter "RA"
  let headRan := headA.appendAfter "_ran"
  unless (← getEnv).contains headRan do
    throwError "{f}: no {headRan} (the wired head over MachineRan)"
  return (headA, headRan, args)

/-- **`f.machine_composedNR{n}` with the wired endpoint as a hypothesis**:
see the file header. Adds `newName`. -/
def composedOfTrace (f : Name) (n : Nat) (newName : Name) : MetaM Unit := do
  let cN := f ++ Name.mkSimple s!"machine_composedNR{n}"
  let some (.thmInfo ti) := (← getEnv).find? cN
    | throwError "{cN}: not a theorem (run #machine_design_svNR {f} {n} first)"
  if (← getEnv).contains newName then throwError "{newName}: exists already"
  let (headA, _, args) ← ranHead f
  let full : Nat := args.size + 12
  let (type, value) ← lambdaBoundedTelescope ti.value 12 fun ys body => do
    unless ys.size == 12 do
      throwError "{cN}: its proof term has {ys.size} leading lambdas, expected 12"
    let closes := ys[10]!
    let hBnd := ys[11]!
    let ct ← instantiateMVars (← inferType closes)
    unless ct.isAppOf ``Tools.ShippingChildInv.MachineClosesAt do
      throwError "{cN}: its 11th binder is not the closing:{indentExpr ct}"
    let concl ← instantiateForall ti.type ys
    if concl.containsFVar closes.fvarId! then
      throwError "{cN}: its conclusion mentions the closing binder"
    let some t0 := body.find? (fun e => e.isAppOf headA && e.getAppNumArgs == full)
      | throwError "{cN}: no application of {headA} to {full} arguments in its proof term (the reading of generateCoreNR is wrong)"
    unless t0.containsFVar closes.fvarId! do
      throwError "{cN}: the application of {headA} found does not carry the closing binder"
    let tT ← instantiateMVars (← inferType t0)
    if tT.containsFVar closes.fvarId! || tT.containsFVar hBnd.fvarId! then
      throwError "{cN}: the type of the wired endpoint depends on the closing or the boundary:{indentExpr tT}"
    withLocalDeclD `hT tT fun hT => do
      let body' := body.replace fun e => if e == t0 then some hT else none
      if body'.containsFVar closes.fvarId! then
        throwError "{cN}: its proof term uses the closing binder outside the wired head {headA} (the reading of generateCoreNR is wrong); nothing is added"
      let bs := ys.extract 0 10 ++ #[hBnd, hT]
      let value ← mkLambdaFVars bs body'
      let type ← mkForallFVars bs concl
      pure (type, value)
  let type ← instantiateMVars type
  let value ← instantiateMVars value
  if (type.find? (·.isConstOf ``Tools.ShippingChildInv.MachineClosesAt)).isSome then
    -- the boundary may mention a CHILD's closing; `f`'s own must be gone
    logInfo m!"{newName}: its statement still mentions MachineClosesAt (a descendant's closing inside the boundary); the binder of {f}'s own closing is removed"
  addTheorem newName type value

/-- `RanAt.ran (hBndR.2) hcore`. -/
def ranOf (hBndR hcore : Lean.Expr) : MetaM Lean.Expr := do
  mkAppM ``Tools.ShippingOutermost.RanAt.ran #[← mkAppM ``And.right #[hBndR], hcore]

/-- **The head `machine_design_noPorts` at `C := True` and the boundary
`Bnd₀ ∧ RanAt`**: statement and proof. `composedT`: the theorem
`composedOfTrace` added. `facts`, `outs`, `masked`, `design`: theorems whose
first explicit arguments are `hpost ran` (the output check: then `hg`), every
further premise a conjunct of `Bnd₀` or one of the extra reflections.
Nothing is added to the environment. -/
def openTerm (f : Name) (n : Nat) (extraM gates : List Name) (composedT : Name)
    (facts outs masked design : Name) : MetaM (Lean.Expr × Lean.Expr) := do
  let ships := f ++ Name.mkSimple s!"machine_ships_hierNR{n}"
  let some (.thmInfo ti) := (← getEnv).find? ships
    | throwError "{ships}: not a theorem (run #machine_design_svNR first)"
  let v := ti.value
  unless v.isAppOf ``Tools.ShippingMachineShipsHier.machine_ships_hierC do
    throwError "{ships}: not built from machine_ships_hierC"
  let a := v.getAppArgs
  unless a.size == 25 do throwError "{ships}: {a.size} arguments of machine_ships_hierC, expected 25"
  let (_, headRan, hargs) ← ranHead f
  let shapeE ← mkAppM ``Tools.ShippingMachineAuto.MachineData.shape #[a[11]!]
  -- the boundary with the run's machine synthesis; the closing predicate `True`
  let bndR ← lambdaBoundedTelescope a[4]! 7 fun bs body => do
    unless bs.size == 7 do
      throwError "{ships}: its boundary is not a function of 7 arguments"
    let ranT := mkAppN (mkConst ``Tools.ShippingOutermost.RanAt)
      #[bs[0]!, bs[1]!, bs[2]!, bs[3]!, toExpr f, shapeE, bs[4]!, bs[5]!, bs[6]!]
    mkLambdaFVars bs (mkAnd body ranT)
  let cTrue ← lambdaBoundedTelescope a[5]! 4 fun cs _ => do
    unless cs.size == 4 do
      throwError "{ships}: its closing predicate is not a function of 4 arguments"
    mkLambdaFVars cs (mkConst ``True)
  let value ← forallTelescope (← inferType (mkConst ships)) fun xs _ => do
    unless xs.size == 11 do throwError "{ships}: {xs.size} binders, expected 11"
    let mDecls : Array (Name × (Array Lean.Expr → MetaM Lean.Expr)) :=
      extraM.toArray.mapIdx fun i s =>
        (Name.mkSimple s!"hX{i}", fun (_ : Array Lean.Expr) => do
          let shape ← mkAppM ``Tools.ShippingMachineAuto.MachineData.shape
            #[mkConst (s ++ `machineData)]
          mkAppM ``Tools.ShippingMachineEntry.MachineDefines
            #[xs[0]!, xs[1]!, xs[2]!, xs[3]!, toExpr s, shape])
    let gDecls : Array (Name × (Array Lean.Expr → MetaM Lean.Expr)) :=
      gates.toArray.mapIdx fun i g =>
        (Name.mkSimple s!"hG{i}", fun (_ : Array Lean.Expr) =>
          mkAppM ``Tools.ShippingInlineSoundness.EntryDefines
            #[xs[0]!, xs[1]!, xs[2]!, xs[3]!, toExpr g, mkConst (g ++ `gateValue)])
    withLocalDeclsD (mDecls ++ gDecls) fun hEx => do
    let args0 : Array (Option Lean.Expr) :=
      #[some (mkNatLit n), some a[3]!, some bndR, some cTrue, some a[6]!, some a[7]!,
        some a[8]!, some a[9]!, some a[10]!, some a[11]!,
        some a[12]!, some a[13]!, some a[14]!, some a[15]!, some a[16]!, some a[17]!,
        some a[18]!, some a[19]!, some a[20]!, some a[21]!]
    let pre0 ← instantiateMVars
      (← mkAppOptM ``Tools.ShippingNoPorts.machine_design_noPorts args0)
    if pre0.hasMVar then throwError "{f}: the head's arguments were not all inferred"
    -- the wired endpoint: zs = mctx mref cctx cref w w' m design hr entry hC hBnd
    let .forallE _ TS _ _ ← whnfR (← inferType pre0)
      | throwError "{f}: the head's wired-endpoint hypothesis is not where it is expected"
    let traceOf (zs : Array Lean.Expr) : MetaM Lean.Expr := do
      let ran ← ranOf zs[11]! zs[8]!
      pure (mkAppN (mkAppN (mkConst headRan) hargs)
        #[zs[0]!, zs[1]!, zs[2]!, zs[3]!, zs[6]!, zs[7]!, ran])
    let soundL ← forallTelescope TS fun zs goal => do
      unless zs.size == 12 do throwError "{f}: the wired-endpoint hypothesis has {zs.size} binders"
      let hT ← traceOf zs
      let p ← mkAppM ``Tools.ShippingMachineTraceX.MachineTraceLBX.toLB #[hT]
      let pT ← inferType p
      unless ← isDefEq pT goal do
        throwError "{headRan}: gives{indentExpr pT}\nbut the head asks{indentExpr goal}"
      mkLambdaFVars zs p
    let pre1 := mkApp pre0 soundL
    -- the composed theorem: zs = … hr entry hC hBnd hm
    let .forallE _ TC _ _ ← whnfR (← inferType pre1)
      | throwError "{f}: the head's composed hypothesis is not where it is expected"
    let composed ← forallTelescope TC fun zs goal => do
      unless zs.size == 13 do throwError "{f}: the composed hypothesis has {zs.size} binders"
      let hT ← traceOf zs
      let hB0 ← mkAppM ``And.left #[zs[11]!]
      let inner := mkAppN (mkConst composedT) (zs.extract 0 10 ++ #[hB0, hT])
      let p ← mkAppM ``Tools.ShippingMachineShipsDepth.composedG_of_NW #[inner]
      let pT ← inferType p
      unless ← isDefEq pT goal do
        throwError "{composedT}: gives{indentExpr pT}\nbut the head asks{indentExpr goal}"
      mkLambdaFVars zs p
    -- the output widths (data), the run's binders through `f`'s reflection, `C := True`
    let pre2 := mkApp (mkApp pre1 composed) a[24]!
    let pre := mkAppN pre2 (xs.extract 0 10 ++ #[mkConst ``True.intro])
    -- the run's facts: zs = raw D w1 hcore hpost hBnd
    let .forallE _ TF _ _ ← whnfR (← inferType pre)
      | throwError "{f}: the head's run-facts hypothesis is not where it is expected"
    let hFacts ← forallBoundedTelescope TF (some 6) fun zs goal => do
      unless zs.size == 6 do throwError "{f}: the run-facts hypothesis has {zs.size} binders"
      let p ← mkAppM facts #[zs[4]!, ← ranOf zs[5]! zs[3]!]
      let hB0 ← mkAppM ``And.left #[zs[5]!]
      mkLambdaFVars zs
        (← Tools.ShippingNoPortsKidsCommand.dischargeWith facts p hB0 goal hEx)
    let pre := mkApp pre hFacts
    -- the output check under the gate: zs = raw D w1 hcore hpost hg hBnd
    let .forallE _ TO _ _ ← whnfR (← inferType pre)
      | throwError "{f}: the head's output-check hypothesis is not where it is expected"
    let hOuts ← forallBoundedTelescope TO (some 7) fun zs goal => do
      unless zs.size == 7 do throwError "{f}: the output-check hypothesis has {zs.size} binders"
      let p ← mkAppM outs #[zs[4]!, ← ranOf zs[6]! zs[3]!, zs[5]!]
      let hB0 ← mkAppM ``And.left #[zs[6]!]
      mkLambdaFVars zs
        (← Tools.ShippingNoPortsKidsCommand.dischargeWith outs p hB0 goal hEx)
    let pre := mkApp pre hOuts
    -- the children's bound: zs = raw D w1 hcore hpost hBnd (cut at 6 binders)
    let .forallE _ TM _ _ ← whnfR (← inferType pre)
      | throwError "{f}: the head's children-bound hypothesis is not where it is expected"
    let hMasked ← forallBoundedTelescope TM (some 6) fun zs goal => do
      unless zs.size == 6 do throwError "{f}: the children-bound hypothesis has {zs.size} binders"
      let p ← mkAppM masked #[zs[4]!, ← ranOf zs[5]! zs[3]!]
      let hB0 ← mkAppM ``And.left #[zs[5]!]
      mkLambdaFVars zs
        (← Tools.ShippingNoPortsKidsCommand.dischargeWith masked p hB0 goal hEx)
    let pre := mkApp pre hMasked
    -- `designCheck` with no check premise: zs = raw D w1 hcore hpost hBnd (cut at 6)
    let .forallE _ TD _ _ ← whnfR (← inferType pre)
      | throwError "{f}: the head's design-check hypothesis is not where it is expected"
    let hDesign ← forallBoundedTelescope TD (some 6) fun zs goal => do
      unless zs.size == 6 do throwError "{f}: the design-check hypothesis has {zs.size} binders"
      let p ← mkAppM design #[zs[4]!, ← ranOf zs[5]! zs[3]!]
      let hB0 ← mkAppM ``And.left #[zs[5]!]
      mkLambdaFVars zs
        (← Tools.ShippingNoPortsKidsCommand.dischargeWith design p hB0 goal hEx)
    let body := mkApp pre hDesign
    if body.containsFVar xs[10]!.fvarId! then
      throwError "{f}: the term depends on the closing binder of {ships}"
    mkLambdaFVars (xs.extract 0 10 ++ hEx) body
  let value ← instantiateMVars value
  let type ← instantiateMVars (← inferType value)
  -- (a descendant's closing inside the built boundary `Bnd₀` is not refused here:
  -- `closeOutermost` refuses any closing constant in the final statement)
  for c in Tools.ShippingNoPortsCommand.forbidden do
    if (type.find? (·.isConstOf c)).isSome then
      throwError "{f}: REFUSED, the statement still mentions {c}"
  return (type, value)

/-- Through the existentials and the conjunction of an open outermost form
`∃ w…, P ∧ ((B₀ ∧ RanAt …) → R)`: a proof of `∃ w…, P ∧ R` from `h`, and
that statement. `hyps`: what `B₀` may be derived from; `ranAt raw D`: a
proof of `RanAt … raw D`. One log line per conjunct of `B₀`. -/
partial def rebuildO (who : Name) (hyps : Array Lean.Expr)
    (ranAt : Lean.Expr → Lean.Expr → MetaM Lean.Expr) (h ty : Lean.Expr)
    (log : IO.Ref (Array String)) : MetaM (Lean.Expr × Lean.Expr) := do
  if ty.isAppOfArity ``Exists 2 then
    let α := ty.getArg! 0
    let p := ty.getArg! 1
    let nm := if p.isLambda then p.bindingName! else `w
    withLocalDeclD nm α fun w => do
      let body := (mkApp p w).headBeta
      withLocalDeclD `hw body fun hw => do
        let (pr, prTy) ← rebuildO who hyps ranAt hw body log
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
    unless ← Tools.ShippingFinalGoalCommand.isPropArrow R do
      throwError "{who}: no antecedent under the existentials:{indentExpr R}"
    let A := (← instantiateMVars R.bindingDomain!).headBeta
    let C := R.bindingBody!
    if ← Tools.ShippingFinalGoalCommand.isPropArrow C then
      throwError "{who}: more than one antecedent under the existentials"
    unless A.isAppOfArity ``And 2 do
      throwError "{who}: the antecedent is not a conjunction:{indentExpr A}"
    let B0 := A.getArg! 0
    let RT := A.getArg! 1
    unless RT.isAppOfArity ``Tools.ShippingOutermost.RanAt 9 do
      throwError "{who}: the second conjunct of the antecedent is not RanAt:{indentExpr RT}"
    let mut missing : Nat := 0
    for c in Tools.ShippingBoundaryClose.conjuncts B0 do
      let ppC := toString (← ppExpr c)
      match ← Tools.ShippingBoundaryClose.solve hyps c with
      | some _ => log.modify (·.push s!"DERIVED from the binders and Start0: {ppC}")
      | none =>
        missing := missing + 1
        log.modify (·.push s!"NOT DERIVED: {ppC}")
    if missing > 0 then
      let lines ← log.get
      let text : String := String.intercalate "\n" lines.toList
      throwError "{who}: {missing} conjunct(s) of the boundary do not follow from the binders and Start0:\n{text}"
    let some pB ← Tools.ShippingBoundaryClose.solve hyps B0
      | throwError "{who}: every conjunct of the boundary was derived but not their conjunction{indentExpr B0}"
    let pR ← ranAt (RT.getArg! 7) (RT.getArg! 8)
    let pRT ← inferType pR
    unless ← isDefEq pRT RT do
      throwError "{who}: the RanAt proof has type{indentExpr pRT}\nbut the boundary asks{indentExpr RT}"
    let pA := mkApp4 (mkConst ``And.intro) B0 RT pB pR
    return (mkApp4 (mkConst ``And.intro) P C hP (mkApp hR pA), mkAnd P C)
  else
    throwError "{who}: expected ∃ … , P ∧ (…), found{indentExpr ty}"

/-- **The outermost endpoint from its open form.** `openN`: a theorem built
by `openTerm` (ten binders through `f`'s reflection, then extra
reflections). `kids`: the reflections the new statement takes after `f`'s —
binder name, declaration, `true` for a gate (`EntryDefines … g.gateValue`),
`false` for a machine (`MachineDefines … k.machineData.shape`) — in order;
then `h0 : Start0 mref cref w`. `ranAtThm`: a theorem whose explicit
arguments are `f`'s reflection, the `kids` reflections in that order, `h0`,
a module and a design, concluding `RanAt … w M D`. Adds `newName`; returns
the log lines. -/
def closeOutermost (openN newName : Name) (kids : List (Name × Name × Bool)) (ranAtThm : Name) :
    MetaM (Array String) := do
  if (← getEnv).contains newName then throwError "{newName}: exists already"
  let info ← getConstInfo openN
  let log ← IO.mkRef (#[] : Array String)
  let (type, value) ← forallBoundedTelescope info.type (some 10) fun xs _ => do
    unless xs.size == 10 do throwError "{openN}: {xs.size} binders, expected at least 10"
    let ctx : Array Lean.Expr := #[xs[0]!, xs[1]!, xs[2]!, xs[3]!]
    let kDecls : Array (Name × (Array Lean.Expr → MetaM Lean.Expr)) :=
      kids.toArray.map fun (bn, k, isGate) =>
        (bn, fun (_ : Array Lean.Expr) => do
          if isGate then
            mkAppM ``Tools.ShippingInlineSoundness.EntryDefines
              (ctx ++ #[toExpr k, mkConst (k ++ `gateValue)])
          else
            let shape ← mkAppM ``Tools.ShippingMachineAuto.MachineData.shape
              #[mkConst (k ++ `machineData)]
            mkAppM ``Tools.ShippingMachineEntry.MachineDefines (ctx ++ #[toExpr k, shape]))
    let start0 := mkAppN (mkConst ``Tools.ShippingMachineRan.Start0) #[xs[1]!, xs[3]!, xs[4]!]
    let decls := kDecls.push (`h0, fun (_ : Array Lean.Expr) => pure start0)
    withLocalDeclsD decls fun hs => do
      let h0 := hs[hs.size - 1]!
      let refl := hs.extract 0 (hs.size - 1)
      -- the open form at its binders, then at its extra reflections
      let mut h := mkAppN (mkConst openN) xs
      for _ in [0:64] do
        let t ← whnfR (← instantiateMVars (← inferType h))
        unless t.isForall do break
        let dom := t.bindingDomain!
        let mut arg? : Option Lean.Expr := none
        for r in refl do
          if arg?.isNone then
            if ← isDefEq (← inferType r) dom then arg? := some r
        let some arg := arg?
          | throwError "{openN}: asks{indentExpr dom}\nwhich is not one of the reflections given to closeOutermost"
        h := mkApp h arg
      let body ← instantiateMVars (← inferType h)
      let cb ← mkAppM ``Tools.ShippingMachineRan.Start0.childBnd #[h0]
      let mut hyps : Array Lean.Expr := #[]
      for x in xs do
        if ← isProp (← inferType x) then hyps := hyps.push x
      hyps := hyps ++ refl ++ #[cb]
      let entry := xs[9]!
      let ranAt (raw D : Lean.Expr) : MetaM Lean.Expr :=
        mkAppM ranAtThm (#[entry] ++ refl ++ #[h0, raw, D])
      let (pr, prTy) ← rebuildO openN hyps ranAt h body log
      let bs := xs ++ hs
      return (← mkForallFVars bs prTy, ← mkLambdaFVars bs pr)
  let type ← instantiateMVars type
  let value ← instantiateMVars value
  for c in Tools.ShippingNoPortsCommand.forbidden ++
      [``Tools.ShippingChildInv.MachineClosesAt, ``Tools.ShippingMachineEntry.MachineCloses,
       ``Tools.ShippingChildInv.ChildRanIn, ``Tools.ShippingOutermost.RanAt] do
    if (type.find? (·.isConstOf c)).isSome then
      throwError "{newName}: REFUSED, the statement mentions {c}"
  addTheorem newName type value
  return ← log.get

end Tools.ShippingOutermostCommand
