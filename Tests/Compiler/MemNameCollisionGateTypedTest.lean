import Tests.Compiler.MemNameCollisionGateClosedTest
import Tools.ShippingKidsTyped
import Tools.ShippingNoPortsTyped

/-! # The design endpoint of `collMixSame` without `hchain`: the TYPED children bound (round par/o-typed)

BUILT as written: ty2 (`lake build Tests.Compiler.MemNameCollisionGateTypedTest`, exit 0, 653 jobs),
committed in 64e813fd; in `Tests.AllTests` (all2, exit 0).

`collMixSame_designClosed` (`MemNameCollisionGateClosedTest`) keeps one outer binder `hchain :
∀ y, RealChild mref cref syncName y → combOk y.1 (declWidth y.1) = true` — a syntactic fact about
the gate child's emitted module — because its head bounds the children in EVERY environment
(`KSBoundedIn`, via `kidsMixedC` / `mixCKS_boundedIn`).

`collMixSame_designClosedT` (this file) uses the head `Tools.ShippingNoPortsTyped.machine_design_noPortsT`:
the children are bounded only on the environments the run reaches (`TypedRun`,
`Tools.ShippingKidsTyped`). Per kid, by ORIGIN: the memory entry `FlatOk`
(`memKidT_facts.flat`), the `.ord` entry `KidTyped` (`kidTyped_of_gate` of `gate_real_ports`,
from the reflection `hR0` and the gate facts). The parent side (typed assignments, argument
connections at the argument widths) is DERIVED from the core run (`core_typedRunMT`). The run
facts, the output check and `designCheck` are discharged as in `collMixSame_designClosed`
(`collMixSame_runFacts`, `_outsG0`, `_designP0`), the closing by `collMixSame_closesR hR0`, the
boundary's reflection merged with `hR0`.

Outer Prop binders: the run, `MachineDefines collMixSame`, `EntryDefines syncName
fakeSrc.gateValue`. Under `∃ raw D`: `ChildBnd`. The conclusion's run hypotheses gain ONE
initial-state condition, `BoundOff (declWidth b) (b.outputs.map (·.name)) st0` (see the head). -/

namespace Sparkle.Tests.Compiler.MemNameCollisionGateTypedTest
open Sparkle.Tests.Compiler.MemNameCollisionGateCertTest
open Sparkle.Tests.Compiler.MemNameCollisionGateClosedTest
open Sparkle.Compiler.MachInstOrigin (InstOrigin)
open Tools.ShippingInstTagged (originAt)

/-- Per kid, by origin: the memory entry is `FlatOk`, the `.ord` entry (the gate child) is
`KidTyped`. -/
theorem collMixSame_kidTyped {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref syncName fakeSrc.gateValue) :
    ∀ (k : Nat) (hk : k < (collMixSame.machineData).shape.insts.length) (y : Tools.ShippingChildInv.Res),
      Tools.ShippingInstTagged.KidT mref cref (originAt (collMixSame.machineData).shape k)
        ((collMixSame.machineData).shape.insts[k]).1 y →
      Tools.ShippingMemKid.FlatOk y.1 ∨ Tools.ShippingKidsTyped.KidTyped y.1 := by
  intro k hk y hy
  obtain ⟨hn, ho⟩ := collMixSame_entry k hk
  rcases ho with ho | ho
  · rw [ho] at hy
    exact Or.inl ((Tools.ShippingMemKid.memKidT_facts
      (Tools.ShippingInstTagged.child?_mem false 4 8)).flat y hy)
  · rw [ho, hn] at hy
    exact Or.inr (Tools.ShippingKidsTyped.kidTyped_of_gate
      (Tools.ShippingGatePorts.gate_real_ports (bs := fakeSrc.gateBinders) hR0
        fakeSrc.gate_old fakeSrc.gate_peel fakeSrc.gate_wf
        (Tools.ShippingGateChild.bool_positions (by decide))
        (Tools.ShippingGateChild.bits_positions (by decide))
        (Tools.ShippingInstTagged.KidT.real hy rfl)))

set_option maxHeartbeats 4000000 in
/-- **The typed children bound of `collMixSame`'s full-entry module** (`core_typedRunMT`), from
the core run, the reflection `hR0` and the boundary. -/
theorem collMixSame_typedRun {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``collMixSame [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``collMixSame
      (collMixSame.machineData).shape)
    (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref syncName fakeSrc.gateValue)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w) :
    Tools.ShippingKidsTyped.TypedRun (Tools.ShippingMachineLinked.childMap D.modules) b
      Tools.ShippingMachineShipsHier.mixInv :=
  Tools.ShippingKidsTyped.core_typedRunMT (nDecl := 3)
    collMixSame.machineData collMixSame.machine_ok collMixSame.machine_body
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel)
    (fun k => outsG (originAt (collMixSame.machineData).shape k))
    (fun k => insG (originAt (collMixSame.machineData).shape k)) 0
    (collMixSame_kids hR0) collMixSame_callArgs (collMixSame_kidTyped hR0)
    hB hcore hpost entry (collMixSame_closesR hR0)
    (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (collMixSame_outChars o ho))
    (by first | decide | decide +kernel)

/-! ## The endpoint (MetaM assembly; the kernel checks the result) -/

open Lean Meta

/-- **`collMixSame_designClosedT`**: `machine_design_noPortsT` at `collMixSame.machine_ships_hierRG`'s
arguments, the four run hypotheses discharged by `collMixSame_runFacts` / `_outsG0` /
`_typedRun` / `_designP0`, the closing by `collMixSame_closesR hR0`, the boundary's reflection
merged with `hR0`. -/
def addTyped : MetaM Name := do
  let ns := `Sparkle.Tests.Compiler.MemNameCollisionGateCertTest
  let cn := `Sparkle.Tests.Compiler.MemNameCollisionGateClosedTest
  let tn := `Sparkle.Tests.Compiler.MemNameCollisionGateTypedTest
  let f := ns ++ `collMixSame
  let ships := f ++ `machine_ships_hierRG
  let name := tn ++ `collMixSame_designClosedT
  if (← getEnv).contains name then throwError "{name}: exists already"
  let some (.thmInfo ti) := (← getEnv).find? ships
    | throwError "{ships}: not a theorem (run #machine_design_svRG0 first)"
  let v := ti.value
  unless v.isAppOf ``Tools.ShippingMachineShipsHier.machine_ships_hierC do
    throwError "{ships}: not built from machine_ships_hierC"
  let a := v.getAppArgs
  unless a.size == 25 do throwError "{ships}: {a.size} arguments of machine_ships_hierC, expected 25"
  unless (← instantiateMVars a[7]!).isConstOf ``Tools.ShippingMachineShipsHier.mixInv do
    throwError "{ships}: the invariant is not mixInv:{indentExpr a[7]!}"
  let factsN := cn ++ `collMixSame_runFacts
  let outsN := cn ++ `collMixSame_outsG0
  let typedN := tn ++ `collMixSame_typedRun
  let designN := cn ++ `collMixSame_designP0
  let (type, value) ← forallTelescope (← inferType (mkConst ships)) fun xs _ => do
    unless xs.size == 11 do throwError "{ships}: {xs.size} binders, expected 11"
    let clT ← instantiateMVars (← inferType xs[10]!)
    unless clT.isAppOf ``Tools.ShippingChildInv.MachineClosesAt do
      throwError "{ships}: the last binder is not MachineClosesAt:{indentExpr clT}"
    let hR0T := mkAppN (mkConst ``Tools.ShippingInlineSoundness.EntryDefines)
      #[xs[0]!, xs[1]!, xs[2]!, xs[3]!, mkConst (ns ++ `syncName), mkConst (ns ++ `fakeSrc ++ `gateValue)]
    withLocalDeclD `hR0 hR0T fun hR0 => do
    let closesPf ← mkAppOptM (ns ++ `collMixSame_closesR) #[xs[0]!, xs[1]!, xs[2]!, xs[3]!, hR0]
    unless ← isDefEq (← inferType closesPf) clT do
      throwError "collMixSame_closesR does not prove the closing binder{indentExpr clT}"
    let xs' := xs.set! 10 closesPf
    -- machine_design_noPortsT: Reset Bnd C Inv hRI declName d kD ι dom src ext extB lsrc srcL
    -- extL extBL soundL composed houtTy, then the run's binders
    let args : Array (Option Lean.Expr) :=
      #[some a[3]!, some a[4]!, some a[5]!, some a[7]!, some a[9]!,
        some a[10]!, some a[11]!, some a[12]!, some a[13]!, some a[14]!, some a[15]!,
        some a[16]!, some a[17]!, some a[18]!, some a[19]!, some a[20]!, some a[21]!,
        some a[22]!, some a[23]!, some a[24]!] ++ xs'.map some
    let pre ← instantiateMVars
      (← mkAppOptM ``Tools.ShippingNoPortsTyped.machine_design_noPortsT args)
    if pre.hasMVar then throwError "{f}: the head's arguments were not all inferred"
    -- the run's facts: zs = raw D w1 hcore hpost hBnd ; xs[9] = entry
    let .forallE _ TF _ _ ← whnfR (← inferType pre)
      | throwError "{f}: the head's run-facts hypothesis is not where it is expected"
    let hFacts ← forallTelescope TF fun zs goal => do
      unless zs.size == 6 do throwError "{f}: the run-facts hypothesis has {zs.size} binders"
      let p ← mkAppM factsN #[zs[3]!, zs[4]!, xs[9]!, hR0]
      mkLambdaFVars zs (← Tests.Compiler.NoPortsGrandHTest.dischargeWith factsN p zs[5]! goal #[])
    let pre := mkApp pre hFacts
    -- the output check under the gate: zs = raw D w1 hcore hpost hg hBnd
    let .forallE _ TO _ _ ← whnfR (← inferType pre)
      | throwError "{f}: the head's output-check hypothesis is not where it is expected"
    let hOuts ← forallTelescope TO fun zs goal => do
      unless zs.size == 7 do throwError "{f}: the output-check hypothesis has {zs.size} binders"
      let p ← mkAppM outsN #[zs[3]!, zs[4]!, xs[9]!, hR0, zs[5]!]
      mkLambdaFVars zs (← Tests.Compiler.NoPortsGrandHTest.dischargeWith outsN p zs[6]! goal #[])
    let pre := mkApp pre hOuts
    -- the typed children bound: zs = raw D w1 hcore hpost hBnd (cut at 6)
    let .forallE _ TT _ _ ← whnfR (← inferType pre)
      | throwError "{f}: the head's typed-bound hypothesis is not where it is expected"
    let hTyp ← forallBoundedTelescope TT (some 6) fun zs goal => do
      unless zs.size == 6 do throwError "{f}: the typed-bound hypothesis has {zs.size} binders"
      let p ← mkAppM typedN #[zs[3]!, zs[4]!, xs[9]!, hR0]
      mkLambdaFVars zs (← Tests.Compiler.NoPortsGrandHTest.dischargeWith typedN p zs[5]! goal #[])
    let pre := mkApp pre hTyp
    -- `designCheck` with no check premise: zs = raw D w1 hcore hpost hBnd (cut at 6)
    let .forallE _ TD _ _ ← whnfR (← inferType pre)
      | throwError "{f}: the head's design-check hypothesis is not where it is expected"
    let hDesign ← forallBoundedTelescope TD (some 6) fun zs goal => do
      unless zs.size == 6 do throwError "{f}: the design-check hypothesis has {zs.size} binders"
      let p ← mkAppM designN #[zs[3]!, zs[4]!, xs[9]!, hR0]
      mkLambdaFVars zs (← Tests.Compiler.NoPortsGrandHTest.dischargeWith designN p zs[5]! goal #[])
    let pre ← instantiateMVars (mkApp pre hDesign)
    -- the boundary's reflection conjunct, merged with `hR0`
    let (merged, mergedT) ← mergeBoundary pre (hEOf hR0)
    if merged.containsFVar xs[10]!.fvarId! || mergedT.containsFVar xs[10]!.fvarId! then
      throwError "{name}: the closing binder is still used"
    let newXs := (xs.extract 0 10).push hR0
    pure (← mkForallFVars newXs mergedT, ← mkLambdaFVars newXs merged)
  let type ← instantiateMVars type
  let value ← instantiateMVars value
  for c in [``Tools.ShippingHierPremisesBase.shipsHierCheck, ``Tools.ShippingDesignSV.designCheck,
      ``Tools.ShippingDesignSVBack.outsCheck, ``Tools.ShippingChildInv.MachineClosesAt,
      ``Tools.ShippingMachineShipsHier.kidsMixed, ``Tools.ShippingKidsMixedC.kidsMixedC,
      ``Tools.ShippingKidsMixedC.combOk] do
    if (type.find? (·.isConstOf c)).isSome then
      throwError "{name}: REFUSED, the statement still mentions {c}"
  Tools.ShippingMachineLinkedCommand.addTheorem name type value
  return name

end Sparkle.Tests.Compiler.MemNameCollisionGateTypedTest

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let name ← Lean.withOptions (fun o => Lean.Elab.async.set o false) <|
    Sparkle.Tests.Compiler.MemNameCollisionGateTypedTest.addTyped
  Lean.logInfo m!"GATETYPED [{name}]: shipsHierCheck, designCheck, outsCheck discharged (as GATECLOSED); the children bound TYPED (TypedRun by core_typedRunMT: memory FlatOk, gate KidTyped by kidTyped_of_gate); MachineClosesAt by collMixSame_closesR; the boundary's reflection merged with hR0; hchain ELIMINATED; ADDED run hypothesis of the conclusion: BoundOff (declWidth b) outputs st0"

/-! ## The audit (an error on any failure) -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let cn := `Sparkle.Tests.Compiler.MemNameCollisionGateClosedTest
  let tn := `Sparkle.Tests.Compiler.MemNameCollisionGateTypedTest
  let old := cn ++ `collMixSame_designClosed
  let fin := tn ++ `collMixSame_designClosedT
  -- (a) standard axioms
  for n in [``Tools.ShippingKidsTyped.noMemB_of_memFree, ``Tools.ShippingKidsTyped.noMemB_of_childTyped,
      ``Tools.ShippingKidsTyped.noMem_of_childTyped, ``Tools.ShippingKidsTyped.boundOff_applyNexts,
      ``Tools.ShippingKidsTyped.connEnvS_boundOffT, ``Tools.ShippingKidsTyped.typed_step_out,
      ``Tools.ShippingKidsTyped.typed_step_state, ``Tools.ShippingKidsTyped.evalAssignsKG_boundOff,
      ``Tools.ShippingKidsTyped.runModuleTG_typed, ``Tools.ShippingKidsTyped.fitX_of_runTyped,
      ``Tools.ShippingKidsTyped.gate_weS_le, ``Tools.ShippingKidsTyped.kidTyped_of_gate,
      ``Tools.ShippingKidsTyped.core_typedRunMT,
      ``Tools.ShippingNoPortsTyped.machine_design_noPortsT,
      tn ++ `collMixSame_kidTyped, tn ++ `collMixSame_typedRun, old, fin] do
    unless (← Lean.getEnv).contains n do throwError "{n}: missing"
    Tests.Compiler.NoPortsTest.stdAxioms n
  -- (b) the final statement: no checker, no children bound (old or new), no chain, no closing,
  -- no TagsAgree
  let finT := (← Lean.getConstInfo fin).type
  for k in Tests.Compiler.NoPortsTest.checkers ++
      [``Tools.ShippingMachineShipsHier.kidsMem, ``Tools.ShippingMachineShipsHier.kidsMasked,
       ``Tools.ShippingMachineShipsHier.kidsMixed, ``Tools.ShippingKidsMixedC.kidsMixedC,
       ``Tools.ShippingKidsMixedC.combAt, ``Tools.ShippingKidsMixedC.combOk,
       ``Tools.ShippingKidsMixedC.combChain,
       ``Tools.ShippingKidsTyped.TypedRun, ``Tools.ShippingKidsTyped.KidTyped,
       ``Tools.ShippingInstTagged.TagsAgree, ``Tools.ShippingInstTagged.tagAgrees,
       ``Tools.ShippingChildInv.MachineClosesAt] do
    if (finT.find? (·.isConstOf k)).isSome then
      throwError "{fin}: the statement mentions {k}"
  -- the added run hypothesis of the conclusion is there (reported, not hidden)
  unless (finT.find? (·.isConstOf ``Tools.ShippingHierTyped.BoundOff)).isSome do
    throwError "{fin}: does not mention BoundOff (the report says the initial-state condition was added)"
  -- (c) the Prop binders and the antecedents under the existentials, LOGGED
  let bindersOf (t : Lean.Expr) : Lean.MetaM (Array String) :=
    Lean.Meta.forallTelescope t fun xs _ => do
      let mut out : Array String := #[]
      for x in xs do
        let ty ← Lean.instantiateMVars (← Lean.Meta.inferType x)
        if ← Lean.Meta.isProp ty then out := out.push (toString (← Lean.Meta.ppExpr ty))
      return out
  let inner (t : Lean.Expr) := Lean.Meta.forallTelescope t fun _ body =>
    Tests.Compiler.NoPortsTest.innerAntecedents body
  let oldT := (← Lean.getConstInfo old).type
  for (n, t) in [(old, oldT), (fin, finT)] do
    let bs ← bindersOf t
    let ia ← inner t
    Lean.logInfo m!"GATETYPED PREMISES {n}: {bs.size} Prop binders {bs}; {ia.size} antecedents under the existentials {ia.map (·.1)}"
  let bFin ← bindersOf finT
  unless bFin.size == 3 do
    throwError "{fin}: {bFin.size} Prop binders, expected 3 (the run, MachineDefines collMixSame, EntryDefines syncName fakeSrc.gateValue)"
  let iFin ← inner finT
  unless iFin.size == 1 do
    throwError "{fin}: {iFin.size} antecedents under the existentials, expected 1 (ChildBnd): {iFin.map (·.1)}"
  -- exactly ONE reflection (`EntryDefines`) in the whole statement: the merged binder
  let cnt := Sparkle.Tests.Compiler.MemNameCollisionGateClosedTest.countApps
    ``Tools.ShippingInlineSoundness.EntryDefines 6 finT
  unless cnt == 1 do
    throwError "{fin}: {cnt} EntryDefines occurrences, expected 1"
  Lean.logInfo m!"GATETYPED {fin}: EntryDefines occurrences {cnt}; hchain eliminated (no combOk in the statement, 3 Prop binders)"

#print axioms Sparkle.Tests.Compiler.MemNameCollisionGateTypedTest.collMixSame_designClosedT
