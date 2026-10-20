import Tools.ShippingNoPortsTyped
import Tools.ShippingShipsNoOutsCommand
import Tools.ShippingMachineLinkedCommand
-- Round par/tgen. BUILT as written: tg1 (exit 0); exercised by `Tests.Compiler.MemNameCollisionGateTypedAllTest` (tg2, exit 0).

/-! # Generator: the typed design endpoint of a gate-collision parent (round par/tgen)

`Tests/Compiler/MemNameCollisionGateTypedTest.lean`'s `addTyped` assembled
`collMixSame_designClosedT` by hand (MetaM; the kernel checks the result). This file is that
assembly as a reusable generator, parameterized by

* the parent `f` (its `f.machine_ships_hierRG`, from `#machine_design_svRG0 f`, must be an
  application of `Tools.ShippingMachineShipsHier.machine_ships_hierC` with 25 arguments and the
  invariant `mixInv`);
* the reflection premise `hR0 : EntryDefines mctx mref cctx cref <childConst> <gateValue>`
  (`childConst` a constant of type `Lean.Name` naming the colliding declaration, `gateValue` the
  gate's reading of its SOURCE, e.g. `fakeSrc.gateValue`);
* `valueEq?`: a theorem `c.gateValue = gateValue` (e.g. `syncGate_value`) used to merge the
  boundary's reflection conjunct `EntryDefines … c c.gateValue` (as `#machine_composedTRG` writes
  it) with `hR0`; `none` when the boundary already mentions `gateValue` itself;
* the per-parent lemmas (`runFacts`, `outsG0`, `typedRun`, `designP0`: each with explicit
  arguments `hcore hpost entry hR0 [hg] hB`, as `collMixSame_runFacts` etc.; `closesR` with
  implicit contexts and the explicit `hR0`, as `collMixSame_closesR`);
* the HEAD (default `Tools.ShippingNoPortsTyped.machine_design_noPortsT`); another head must
  have the identical binder layout (20 leading arguments, then the 11 run binders, then the four
  run hypotheses `hFacts`, `hOuts`, `hTyped`, `hDesign` in this order).

Steps (exactly `addTyped`'s): argument-extraction checks; the closing binder
`MachineClosesAt f` replaced by `closesR hR0`; the four run hypotheses discharged by the lemmas
through the boundary's conjuncts (`dischargeWith`, copied from
`Tests.Compiler.NoPortsGrandHTest`); the boundary's reflection conjunct merged with `hR0`
(`exists_bnd_merge`); REFUSAL if the statement still mentions `shipsHierCheck`, `designCheck`,
`outsCheck`, `MachineClosesAt`, `kidsMixed`, `kidsMixedC` or `combOk`.

No test module is imported: the test-specific constants of the old `hEOf` (`syncGate_value`,
`memChildName false 4 8`) are parameters here (`valueEq?`). -/
namespace Tools.ShippingGateTypedCommand
open Lean Meta

/-- The generator's input. -/
structure Spec where
  /-- The parent declaration (`f`); `f.machine_ships_hierRG` is read. -/
  parent : Name
  /-- The theorem to add. -/
  name : Name
  /-- A constant of type `Lean.Name`: the colliding declaration's name (e.g. `…syncName`). -/
  childConst : Name
  /-- The gate's reading of the source declaration (e.g. `…fakeSrc.gateValue`). -/
  gateValue : Name
  /-- `c.gateValue = gateValue` for the boundary's child `c` (e.g. `…syncGate_value`). -/
  valueEq? : Option Name := none
  runFacts : Name
  outsG0 : Name
  typedRun : Name
  designP0 : Name
  closesR : Name
  /-- The head; same binder layout as `machine_design_noPortsT`. -/
  head : Name := ``Tools.ShippingNoPortsTyped.machine_design_noPortsT
  /-- For a head with a FIFTH run hypothesis `hNames` after `hDesign`
  (`Tools.ShippingNoPortsTyped.machine_design_noPortsTB`): the per-parent lemma discharging it
  (same explicit arguments as `designP0`). Then the statement must not mention `BoundOff`. -/
  names? : Option Name := none

/-- The constants a generated statement must not mention. -/
def refused : List Name :=
  [``Tools.ShippingHierPremisesBase.shipsHierCheck, ``Tools.ShippingDesignSV.designCheck,
   ``Tools.ShippingDesignSVBack.outsCheck, ``Tools.ShippingChildInv.MachineClosesAt,
   ``Tools.ShippingMachineShipsHier.kidsMixed, ``Tools.ShippingKidsMixedC.kidsMixedC,
   ``Tools.ShippingKidsMixedC.combOk]

/-- `Tests.Compiler.NoPortsGrandHTest.dischargeWith`, copied: apply `p0` to the conjuncts of
`hBnd` (and `extra`) until its type is `goal`. -/
def dischargeWith (thm : Name) (p0 hBnd goal : Lean.Expr) (extra : Array Lean.Expr) :
    MetaM Lean.Expr := do
  let parts := (← Tools.ShippingShipsNoOutsCommand.andParts hBnd) ++ extra
  let mut p := p0
  repeat
    let t ← whnfR (← instantiateMVars (← inferType p))
    let .forallE _ dom _ _ := t | break
    let mut found := false
    for q in parts do
      if ← isDefEq (← inferType q) dom then
        p := mkApp p q
        found := true
        break
    unless found do
      throwError "{thm}: asks{indentExpr dom}\nwhich is neither a conjunct of the endpoint's boundary{indentExpr (← inferType hBnd)}\nnor an extra hypothesis"
  unless ← isDefEq (← inferType p) goal do
    throwError "{thm}: proves{indentExpr (← inferType p)}\nbut the head asks{indentExpr goal}"
  instantiateMVars p

/-- The boundary's reflection conjunct `E` (`EntryDefines … c c.gateValue`, as the generator
writes it) from the binder `hR0` (`EntryDefines … childConst gateValue`): `hR0` itself when `E`
mentions `gateValue`, otherwise rewritten by `valueEq : c.gateValue = gateValue`
(`addTyped`'s `hEOf`, its constants parameterized). The child-name argument is left to the
kernel's definitional check (as `hEOf`). -/
def reflOf (gateValue : Name) (valueEq? : Option Name) (hR0 E : Lean.Expr) : MetaM Lean.Expr := do
  unless E.isAppOfArity ``Tools.ShippingInlineSoundness.EntryDefines 6 do
    throwError "the boundary's second conjunct is not an EntryDefines:{indentExpr E}"
  let a := E.getAppArgs
  let some cv := a[5]!.constName? |
    throwError "the boundary's reflected value is not a constant:{indentExpr E}"
  if cv == gateValue then
    unless ← isDefEq (← inferType hR0) E do
      throwError "the reflection binder does not prove{indentExpr E}"
    return ← mkExpectedTypeHint hR0 E
  let some eqN := valueEq? |
    throwError "the boundary reflects {cv}, not {gateValue}, and no value equation was given"
  let eqT ← inferType (mkConst eqN)
  let some (_, lhs, rhs) := eqT.eq? | throwError "{eqN}: not an equation:{indentExpr eqT}"
  unless lhs.isConstOf cv && rhs.isConstOf gateValue do
    throwError "{eqN} is not {cv} = {gateValue}:{indentExpr eqT}"
  let fn := mkAppN (mkConst ``Tools.ShippingInlineSoundness.EntryDefines) (a.extract 0 5)
  -- fn c.gateValue = fn gateValue
  let h ← mkCongrArg fn (mkConst eqN)
  let pf ← mkEqMPR h hR0
  unless ← isDefEq (← inferType pf) E do
    throwError "the merged reflection does not prove{indentExpr E}"
  mkExpectedTypeHint pf E

/-- `∃ a b, P ∧ (B ∧ E → R)` ↦ `∃ a b, P ∧ (B → R)` by `exists_bnd_merge`, `E` from `mkHE`
(copied from `MemNameCollisionGateClosedTest.mergeBoundary`). -/
def mergeBoundary (pf : Lean.Expr) (mkHE : Lean.Expr → MetaM Lean.Expr) :
    MetaM (Lean.Expr × Lean.Expr) := do
  let T ← instantiateMVars (← inferType pf)
  unless T.isAppOfArity ``Exists 2 do throwError "not ∃ raw:{indentExpr T}"
  let α := T.appFn!.appArg!
  let .lam nA _ bodyA _ := T.appArg! | throwError "∃ raw: not a lambda"
  withLocalDeclD nA α fun ra => do
  let TA := bodyA.instantiate1 ra
  unless TA.isAppOfArity ``Exists 2 do throwError "not ∃ D:{indentExpr TA}"
  let β := TA.appFn!.appArg!
  let .lam nB _ bodyB _ := TA.appArg! | throwError "∃ D: not a lambda"
  withLocalDeclD nB β fun dd => do
  let TB := bodyB.instantiate1 dd
  let some (P, X) := TB.and? | throwError "not P ∧ …:{indentExpr TB}"
  let .forallE nX dom rest biX := X | throwError "no antecedent:{indentExpr X}"
  if rest.hasLooseBVars then throwError "the conclusion depends on the boundary"
  let dom' ← instantiateMVars dom.headBeta
  let some (B, E) := dom'.and? | throwError "the boundary is not B ∧ E:{indentExpr dom'}"
  for x in [B, E] do
    if x.containsFVar ra.fvarId! || x.containsFVar dd.fvarId! then
      throwError "the boundary depends on raw / D:{indentExpr x}"
  let hE ← mkHE E
  let Plam ← mkLambdaFVars #[ra, dd] P
  let Rlam ← mkLambdaFVars #[ra, dd] rest
  let newTB := mkApp2 (mkConst ``And) P (Lean.Expr.forallE nX B rest biX)
  let newT := mkApp T.appFn! (← mkLambdaFVars #[ra] (mkApp TA.appFn! (← mkLambdaFVars #[dd] newTB)))
  let prf := mkAppN (mkConst ``Tools.ShippingMemKid.exists_bnd_merge) #[α, β, Plam, B, E, Rlam, hE, pf]
  unless ← isDefEq (← inferType prf) newT do
    throwError "exists_bnd_merge does not give{indentExpr newT}"
  pure (← mkExpectedTypeHint prf newT, newT)

/-- The occurrences of `k` applied to `n` arguments in `e` (for audits; copied from
`MemNameCollisionGateClosedTest.countApps`). -/
partial def countApps (k : Name) (n : Nat) : Lean.Expr → Nat
  | e@(.app f a) => (if e.isAppOfArity k n then 1 else 0) + countApps k n f + countApps k n a
  | .lam _ t b _ => countApps k n t + countApps k n b
  | .forallE _ t b _ => countApps k n t + countApps k n b
  | .letE _ t v b _ => countApps k n t + countApps k n v + countApps k n b
  | .mdata _ e => countApps k n e
  | .proj _ _ e => countApps k n e
  | _ => 0

/-- **The generator** (`addTyped`, parameterized): the head at `f.machine_ships_hierRG`'s
arguments, the four run hypotheses discharged by the per-parent lemmas, the closing by
`closesR hR0`, the boundary's reflection merged with `hR0`. Returns the added theorem's name. -/
def generate (s : Spec) : MetaM Name := do
  let f := s.parent
  let ships := f ++ `machine_ships_hierRG
  let name := s.name
  if (← getEnv).contains name then throwError "{name}: exists already"
  for n in [s.childConst, s.gateValue, s.runFacts, s.outsG0, s.typedRun, s.designP0, s.closesR,
      s.head] ++ s.valueEq?.toList ++ s.names?.toList do
    unless (← getEnv).contains n do throwError "{n}: unknown constant"
  let some (.thmInfo ti) := (← getEnv).find? ships
    | throwError "{ships}: not a theorem (run #machine_design_svRG0 first)"
  let v := ti.value
  unless v.isAppOf ``Tools.ShippingMachineShipsHier.machine_ships_hierC do
    throwError "{ships}: not built from machine_ships_hierC"
  let a := v.getAppArgs
  unless a.size == 25 do throwError "{ships}: {a.size} arguments of machine_ships_hierC, expected 25"
  unless (← instantiateMVars a[7]!).isConstOf ``Tools.ShippingMachineShipsHier.mixInv do
    throwError "{ships}: the invariant is not mixInv:{indentExpr a[7]!}"
  let (type, value) ← forallTelescope (← inferType (mkConst ships)) fun xs _ => do
    unless xs.size == 11 do throwError "{ships}: {xs.size} binders, expected 11"
    let clT ← instantiateMVars (← inferType xs[10]!)
    unless clT.isAppOf ``Tools.ShippingChildInv.MachineClosesAt do
      throwError "{ships}: the last binder is not MachineClosesAt:{indentExpr clT}"
    let hR0T := mkAppN (mkConst ``Tools.ShippingInlineSoundness.EntryDefines)
      #[xs[0]!, xs[1]!, xs[2]!, xs[3]!, mkConst s.childConst, mkConst s.gateValue]
    withLocalDeclD `hR0 hR0T fun hR0 => do
    let closesPf ← mkAppOptM s.closesR #[xs[0]!, xs[1]!, xs[2]!, xs[3]!, hR0]
    unless ← isDefEq (← inferType closesPf) clT do
      throwError "{s.closesR} does not prove the closing binder{indentExpr clT}"
    let xs' := xs.set! 10 closesPf
    -- machine_design_noPortsT: Reset Bnd C Inv hRI declName d kD ι dom src ext extB lsrc srcL
    -- extL extBL soundL composed houtTy, then the run's binders
    let args : Array (Option Lean.Expr) :=
      #[some a[3]!, some a[4]!, some a[5]!, some a[7]!, some a[9]!,
        some a[10]!, some a[11]!, some a[12]!, some a[13]!, some a[14]!, some a[15]!,
        some a[16]!, some a[17]!, some a[18]!, some a[19]!, some a[20]!, some a[21]!,
        some a[22]!, some a[23]!, some a[24]!] ++ xs'.map some
    let pre ← instantiateMVars (← mkAppOptM s.head args)
    if pre.hasMVar then throwError "{f}: the head's arguments were not all inferred"
    -- the run's facts: zs = raw D w1 hcore hpost hBnd ; xs[9] = entry
    let .forallE _ TF _ _ ← whnfR (← inferType pre)
      | throwError "{f}: the head's run-facts hypothesis is not where it is expected"
    let hFacts ← forallTelescope TF fun zs goal => do
      unless zs.size == 6 do throwError "{f}: the run-facts hypothesis has {zs.size} binders"
      let p ← mkAppM s.runFacts #[zs[3]!, zs[4]!, xs[9]!, hR0]
      mkLambdaFVars zs (← dischargeWith s.runFacts p zs[5]! goal #[])
    let pre := mkApp pre hFacts
    -- the output check under the gate: zs = raw D w1 hcore hpost hg hBnd
    let .forallE _ TO _ _ ← whnfR (← inferType pre)
      | throwError "{f}: the head's output-check hypothesis is not where it is expected"
    let hOuts ← forallTelescope TO fun zs goal => do
      unless zs.size == 7 do throwError "{f}: the output-check hypothesis has {zs.size} binders"
      let p ← mkAppM s.outsG0 #[zs[3]!, zs[4]!, xs[9]!, hR0, zs[5]!]
      mkLambdaFVars zs (← dischargeWith s.outsG0 p zs[6]! goal #[])
    let pre := mkApp pre hOuts
    -- the typed children bound: zs = raw D w1 hcore hpost hBnd (cut at 6)
    let .forallE _ TT _ _ ← whnfR (← inferType pre)
      | throwError "{f}: the head's typed-bound hypothesis is not where it is expected"
    let hTyp ← forallBoundedTelescope TT (some 6) fun zs goal => do
      unless zs.size == 6 do throwError "{f}: the typed-bound hypothesis has {zs.size} binders"
      let p ← mkAppM s.typedRun #[zs[3]!, zs[4]!, xs[9]!, hR0]
      mkLambdaFVars zs (← dischargeWith s.typedRun p zs[5]! goal #[])
    let pre := mkApp pre hTyp
    -- `designCheck` with no check premise: zs = raw D w1 hcore hpost hBnd (cut at 6)
    let .forallE _ TD _ _ ← whnfR (← inferType pre)
      | throwError "{f}: the head's design-check hypothesis is not where it is expected"
    let hDesign ← forallBoundedTelescope TD (some 6) fun zs goal => do
      unless zs.size == 6 do throwError "{f}: the design-check hypothesis has {zs.size} binders"
      let p ← mkAppM s.designP0 #[zs[3]!, zs[4]!, xs[9]!, hR0]
      mkLambdaFVars zs (← dischargeWith s.designP0 p zs[5]! goal #[])
    let pre ← instantiateMVars (mkApp pre hDesign)
    -- the name facts (TB head only): zs = raw D w1 hcore hpost hBnd (cut at 6)
    let pre ← match s.names? with
      | none => pure pre
      | some nm => do
        let .forallE _ TN _ _ ← whnfR (← inferType pre)
          | throwError "{f}: the head's name-facts hypothesis is not where it is expected"
        let hN ← forallBoundedTelescope TN (some 6) fun zs goal => do
          unless zs.size == 6 do throwError "{f}: the name-facts hypothesis has {zs.size} binders"
          let p ← mkAppM nm #[zs[3]!, zs[4]!, xs[9]!, hR0]
          mkLambdaFVars zs (← dischargeWith nm p zs[5]! goal #[])
        instantiateMVars (mkApp pre hN)
    -- the boundary's reflection conjunct, merged with `hR0`
    let (merged, mergedT) ← mergeBoundary pre (reflOf s.gateValue s.valueEq? hR0)
    if merged.containsFVar xs[10]!.fvarId! || mergedT.containsFVar xs[10]!.fvarId! then
      throwError "{name}: the closing binder is still used"
    let newXs := (xs.extract 0 10).push hR0
    pure (← mkForallFVars newXs mergedT, ← mkLambdaFVars newXs merged)
  let type ← instantiateMVars type
  let value ← instantiateMVars value
  for c in refused ++ (if s.names?.isSome then [``Tools.ShippingHierTyped.BoundOff] else []) do
    if (type.find? (·.isConstOf c)).isSome then
      throwError "{name}: REFUSED, the statement still mentions {c}"
  Tools.ShippingMachineLinkedCommand.addTheorem name type value
  return name

/-- `generate` with elaboration-async off and a large recursion depth (as `addTyped`'s caller). -/
def generateTop (s : Spec) : MetaM Name :=
  withOptions (fun o => maxRecDepth.set (Lean.Elab.async.set o false) 1000000) <|
    withTheReader Core.Context (fun c => { c with maxRecDepth := 1000000 }) (generate s)

/-- `#gate_design_typed f name childConst gateValue runFacts outsG0 typedRun designP0 closesR
[value_eq eqThm] [head headThm]`: `generate`. `name` is added under the current namespace;
every other identifier is resolved as a global constant. -/
syntax (name := gateDesignTyped) "#gate_design_typed " ident ident ident ident ident ident ident
  ident ident (&"value_eq" ident)? (&"head" ident)? : command

open Lean.Elab Lean.Elab.Command in
-- (writing-time guess, accepted by build tg1/tg2): the node layout of the optional groups (`(&"value_eq" ident)?` read as a null node
-- with two children when present); read by position, not by a quotation pattern.
@[command_elab gateDesignTyped] def elabGateDesignTyped : CommandElab := fun stx => do
  unless stx.getNumArgs == 12 do throwUnsupportedSyntax
  let res (i : Syntax) : CommandElabM Name :=
    liftCoreM <| realizeGlobalConstNoOverloadWithInfo i
  let opt (s : Syntax) : Option Syntax := if s.getNumArgs == 2 then some s[1] else none
  let parent ← res stx[1]
  let name := (← getCurrNamespace) ++ stx[2].getId
  let childConst ← res stx[3]
  let gateValue ← res stx[4]
  let runFacts ← res stx[5]
  let outsG0 ← res stx[6]
  let typedRun ← res stx[7]
  let designP0 ← res stx[8]
  let closesR ← res stx[9]
  let valueEq? ← (opt stx[10]).mapM res
  let head ← match opt stx[11] with
    | some h => res h
    | none => pure ``Tools.ShippingNoPortsTyped.machine_design_noPortsT
  let n ← liftTermElabM <| generateTop
    { parent, name, childConst, gateValue, valueEq?, runFacts, outsG0, typedRun, designP0,
      closesR, head }
  logInfo m!"{n}: the typed design endpoint of {parent} (head {head}); checks discharged, the closing by {closesR}, the boundary's reflection merged; checked by the kernel"

end Tools.ShippingGateTypedCommand
