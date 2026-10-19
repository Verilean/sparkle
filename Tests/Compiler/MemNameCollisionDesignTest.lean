import Tests.Compiler.MemNameCollisionCertTest
import Tests.Compiler.NoPortsMemSeqMemTest
import Tools.ShippingMachineSeqCommandR
import Tools.ShippingPortsMatchRawLeaf

/-! # Design-level endpoint of a COLLISION parent: `collSameR` (round par/o-kidt2)

`collSameR` (`Tests/Compiler/MemNameCollisionCertTest.lean`): a parent with a register,
a synchronous 4/8 memory (`Signal.memory wa wd we ra`, origin `.mem false 4 8`) and a call,
on the SAME argument `let`s, of a `@[hardware_module]` leaf register machine (`fakeReg`)
declared under the memory's placeholder name `memChildName false 4 8` (origin `.ord`).
Both call entries carry the one name `SparkleMem.sync.4.8`; `TagsAgree` is false
(`collSame_not_agree`). Before this round no design-level statement covered it:

* `#machine_design_svR0` refused ("no sequential child": the generator classified entries by
  NAME, `memWidths?`) — now it classifies by the entries' stored ORIGIN
  (`Tools.ShippingMachineMemCommand.originMem?` / `seqCallees` / `allMemOrigins`);
* the four check premises of `machine_design_svR0` (`shipsHierCheck`, `kidsMixed`,
  `designCheck`, `outsCheck`) were discharged only by the `TagsAgree` chain
  (`Tools.ShippingMemKid.kidsM_*`) — here by its origin-based form `kidsM_*T` over `KidFactsT`
  (kids by ORIGIN: `KidT`), tables keyed by the entry's origin (both entries have one name);
* the closing `MachineClosesAt collSameR` was a binder — here it is discharged by
  `collSame_closes` (kernel-checked, origin-based closing).

## Premises: before → after

| statement | premises (Prop binders / antecedents) |
|---|---|
| `collSameR.machine_design_svR0` (generated) | run, `MachineDefines collSameR`, `MachineClosesAt collSameR`; under the existentials `shipsHierCheck`, `designCheck … 0`, `outsCheck … 0`, `kidsMixed`, the boundary (`ChildBnd ∧` reflection of `SparkleMem.sync.4.8`) |
| `collSameR.machine_design_noPortsR0` (generated, `generateR0`) | run, `MachineDefines collSameR`, `MachineClosesAt collSameR`; the boundary only |
| `collSame_design` (this file) | run, `MachineDefines collSameR`, `MachineDefines SparkleMem.sync.4.8` (the colliding declaration's reflection, at the parent's contexts, explicit); the boundary only. NO `TagsAgree`, NO name half of `hnomem`, NO `MachineClosesAt` |

The conclusion is the generated one, unchanged: the shipped design's `DesignSV` at depth 0
(the module list, not the SV string, not `#sim`). The compiler's guards with fallback stay.
SCOPE: one declaration (same arguments); `collArgsR` is the next unit.

BUILT (par/o-kidt2; runs dt1/dt2 failed — `outName` by `decide` on `sanitizeName` stuck (now via
`sanitizeName_of_clean`), a `Bool` used as a monadic condition, a double-backtick name of a constant
added later; dt3 exit 0, peak 0.35 GB; `collSame_design`: [propext, Classical.choice, Quot.sound];
the audit `run_cmd` asserts the premise counts above). -/

namespace Sparkle.Tests.Compiler.MemNameCollisionCertTest

#machine_endpoint collSameR
#machine_design_svR0 collSameR

end Sparkle.Tests.Compiler.MemNameCollisionCertTest

namespace Sparkle.Tests.Compiler.MemNameCollisionDesignTest
open Sparkle.Tests.Compiler.MemNameCollisionCertTest
open Sparkle.Compiler.MachInstOrigin (InstOrigin)
open Tools.ShippingInstTagged (originAt)
open Tools.ShippingMemKid (KidFactsT memOuts memIns)

/-- The callee's outputs, keyed by the entry's ORIGIN. -/
noncomputable def outsT : InstOrigin → List Sparkle.IR.Machine.OutField
  | .mem _ _ dw => memOuts dw
  | .ord => fakeD.shape.layout.outs
  | .field _ => fakeD.shape.layout.outs

/-- The callee's argument widths, keyed by the entry's ORIGIN. -/
noncomputable def insT : InstOrigin → List Nat
  | .mem _ aw dw => memIns aw dw
  | .ord => Tools.ShippingPortWidthsPure.declWidths fakeD
  | .field _ => Tools.ShippingPortWidthsPure.declWidths fakeD

/-- Every entry is named `SparkleMem.sync.4.8`, of origin the memory or `.ord` (decided). -/
theorem collSame_entry : ∀ (k : Nat) (hk : k < (collSameR.machineData).shape.insts.length),
    ((collSameR.machineData).shape.insts[k]).1 = syncName ∧
      (originAt (collSameR.machineData).shape k = .mem false 4 8 ∨
        originAt (collSameR.machineData).shape k = .ord) := by
  first | decide | decide +kernel

theorem fake_outChars :
    ∀ o ∈ fakeD.shape.layout.outs, ∀ c ∈ o.name.toList, Sparkle.IR.NameHints.charOk c = true := by
  first | decide | decide +kernel

/-- `fakeReg` (under the placeholder name) is a leaf kid, from its reflection. -/
theorem fake_leafKid {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hRc : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref syncName fakeD.shape) :
    Tools.ShippingPortsMatchRawLeaf.LeafKid mctx mref cctx cref syncName fakeD :=
  { ok := fake_ok
    body := fake_body
    calls := by first | decide | decide +kernel
    dom := by first | decide | decide +kernel
    leaf := fake_leaf
    slots := fun h0 => absurd (congrArg List.length h0) (by first | decide | decide +kernel)
    ss := by first | decide | decide +kernel
    outTy := fake_outTy
    outName := fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (fake_outChars o ho)
    outScalar := by first | decide | decide +kernel
    entry := hRc
    closes := fun mc cc => fake_closes mc _ cc _ }

/-- **`KidFactsT` of every call entry of `collSameR`, by ORIGIN**, at depth 0: the memory
origin by `memKidT_facts`, the `.ord` entry (named as the memory!) by `leafKid_facts` of
`fakeReg` through `kidFactsT_of`. -/
theorem collSame_kids {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hRc : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref syncName fakeD.shape) :
    ∀ (k : Nat) (hk : k < (collSameR.machineData).shape.insts.length),
      KidFactsT mref cref (originAt (collSameR.machineData).shape k)
        ((collSameR.machineData).shape.insts[k]).1
        (outsT (originAt (collSameR.machineData).shape k))
        (insT (originAt (collSameR.machineData).shape k)) 0 := by
  intro k hk
  obtain ⟨hn, ho⟩ := collSame_entry k hk
  rcases ho with ho | ho
  · rw [ho]
    exact Tools.ShippingMemKid.memKidT_facts (Tools.ShippingInstTagged.child?_mem false 4 8)
  · rw [ho, hn]
    exact Tools.ShippingMemKid.kidFactsT_of
      (Tools.ShippingLeafKidFacts.leafKid_facts (fake_leafKid hRc) 0) rfl

theorem collSame_callWidths : Tools.ShippingCallWidths.callWidthsOk collSameR.machineData 4
    (fun k => outsT (originAt (collSameR.machineData).shape k)) = true := by
  first | decide | decide +kernel

theorem collSame_callArgs : Tools.ShippingPortsMatchRaw.callArgsOk collSameR.machineData 4
    (fun k => insT (originAt (collSameR.machineData).shape k)) = true := by
  first | decide | decide +kernel

theorem collSame_outChars :
    ∀ o ∈ (collSameR.machineData).shape.layout.outs,
      ∀ c ∈ o.name.toList, Sparkle.IR.NameHints.charOk c = true := by
  first | decide | decide +kernel

set_option maxHeartbeats 4000000 in
/-- **The run's facts of `collSameR`'s full-entry module** (`kidsM_runFactsT`). -/
theorem collSame_runFacts {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``collSameR [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``collSameR
      (collSameR.machineData).shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref ``collSameR
      (collSameR.machineData).shape)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w)
    (hRc : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref syncName fakeD.shape) :
    Tools.ShippingGuardsSound.RunFacts (Tools.ShippingMachineLinked.childMap D.modules) b :=
  Tools.ShippingMemKid.kidsM_runFactsT (nDecl := 4)
    collSameR.machineData collSameR.machine_ok collSameR.machine_body
    (by decide) (by decide) (by decide)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by decide)
    (fun k => outsT (originAt (collSameR.machineData).shape k))
    (fun k => insT (originAt (collSameR.machineData).shape k)) 0
    (collSame_kids hRc) collSame_callWidths
    hB hcore hpost entry closes

set_option maxHeartbeats 4000000 in
/-- **The output check at depth 0 under the statement-kind gate** (`kidsM_outsCheckT`). -/
theorem collSame_outsG0 {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``collSameR [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``collSameR
      (collSameR.machineData).shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref ``collSameR
      (collSameR.machineData).shape)
    (hg : Sparkle.IR.RefineCheck.hierGate b = true)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w)
    (hRc : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref syncName fakeD.shape) :
    Tools.ShippingDesignSVBack.outsCheck (Tools.ShippingMachineLinked.childMap D.modules) 0
      (Sparkle.IR.OptCheck.checkedOptimize b) = true :=
  Tools.ShippingMemKid.kidsM_outsCheckT (nDecl := 4)
    collSameR.machineData collSameR.machine_ok collSameR.machine_body
    (by decide) (by decide) (by decide)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by decide)
    (fun k => outsT (originAt (collSameR.machineData).shape k))
    (fun k => insT (originAt (collSameR.machineData).shape k)) 0
    (collSame_kids hRc)
    hB hcore hpost entry closes hg

set_option maxHeartbeats 4000000 in
/-- **The children's flat bound `kidsMixed`** (`kidsM_mixedT`). -/
theorem collSame_mixedG {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``collSameR [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``collSameR
      (collSameR.machineData).shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref ``collSameR
      (collSameR.machineData).shape)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w)
    (hRc : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref syncName fakeD.shape) :
    Tools.ShippingMachineShipsHier.kidsMixed (Tools.ShippingMachineLinked.childMap D.modules)
      b.body = true :=
  Tools.ShippingMemKid.kidsM_mixedT (nDecl := 4)
    collSameR.machineData collSameR.machine_ok collSameR.machine_body
    (by decide) (by decide) (by decide)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by decide)
    (fun k => outsT (originAt (collSameR.machineData).shape k))
    (fun k => insT (originAt (collSameR.machineData).shape k)) 0
    (collSame_kids hRc)
    hB hcore hpost entry closes

set_option maxHeartbeats 4000000 in
/-- **`designCheck` at depth 0 of the shipped module, with no check premise**
(`kidsM_designCheckT`). -/
theorem collSame_designP0 {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``collSameR [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``collSameR
      (collSameR.machineData).shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref ``collSameR
      (collSameR.machineData).shape)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w)
    (hRc : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref syncName fakeD.shape) :
    Tools.ShippingDesignSV.designCheck (Tools.ShippingMachineLinked.childMap D.modules) 0
      (Sparkle.IR.OptCheck.checkedOptimize b) = true :=
  Tools.ShippingMemKid.kidsM_designCheckT (nDecl := 4)
    collSameR.machineData collSameR.machine_ok collSameR.machine_body
    (by decide) (by decide) (by decide)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by decide)
    (fun k => outsT (originAt (collSameR.machineData).shape k))
    (fun k => insT (originAt (collSameR.machineData).shape k)) 0
    (collSame_kids hRc) collSame_callWidths collSame_callArgs
    hB hcore hpost entry closes
    (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (collSame_outChars o ho))
    (by decide)

set_option maxHeartbeats 4000000 in
/-- `collSame_closes` at the endpoint's data constant (the same reader data). -/
theorem collSame_closesR {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hRc : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref syncName fakeD.shape) :
    Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref ``collSameR
      (collSameR.machineData).shape :=
  collSame_closes hRc

end Sparkle.Tests.Compiler.MemNameCollisionDesignTest

/-! ## The endpoint without the four check premises, then without the closing -/

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let f := ``Sparkle.Tests.Compiler.MemNameCollisionCertTest.collSameR
  let name ← Lean.withOptions (fun o => Lean.Elab.async.set o false) <|
    Tests.Compiler.NoPortsMemSeqMemTest.generateR0 f
      ``Sparkle.Tests.Compiler.MemNameCollisionDesignTest.collSame_runFacts
      ``Sparkle.Tests.Compiler.MemNameCollisionDesignTest.collSame_outsG0
      ``Sparkle.Tests.Compiler.MemNameCollisionDesignTest.collSame_mixedG
      `Sparkle.Tests.Compiler.MemNameCollisionDesignTest.collSame_designP0
  Lean.logInfo m!"COLLDESIGN [{name}]: the four check premises discharged by the origin-based chain (kidsM_*T, KidFactsT by origin); MachineClosesAt still a binder here"

open Lean Meta in
/-- **`collSame_design`**: `collSameR.machine_design_noPortsR0` with its `MachineClosesAt`
binder replaced by the colliding declaration's reflection `hRc` (at the same contexts),
the closing given by `collSame_closesR hRc`. -/
def addDesign : MetaM Unit := do
  let base := ``Sparkle.Tests.Compiler.MemNameCollisionCertTest.collSameR ++ `machine_design_noPortsR0
  let name := `Sparkle.Tests.Compiler.MemNameCollisionDesignTest.collSame_design
  let ci ← getConstInfo base
  unless ci.levelParams.isEmpty do throwError "{base}: universe parameters"
  let (type, value) ← forallTelescope ci.type fun xs body => do
    let mut idx? : Option Nat := none
    for i in [0:xs.size] do
      if (← instantiateMVars (← inferType xs[i]!)).isAppOf ``Tools.ShippingChildInv.MachineClosesAt then
        if idx?.isSome then throwError "{base}: two MachineClosesAt binders"
        idx? := some i
    let some i := idx? | throwError "{base}: no MachineClosesAt binder"
    let clT ← instantiateMVars (← inferType xs[i]!)
    let a := clT.getAppArgs
    let hRcT := mkAppN (mkConst ``Tools.ShippingMachineEntry.MachineDefines)
      #[a[0]!, a[1]!, a[2]!, a[3]!, mkConst ``Sparkle.Tests.Compiler.MemNameCollisionCertTest.syncName,
        ← mkAppM ``Tools.ShippingMachineAuto.MachineData.shape
          #[mkConst ``Sparkle.Tests.Compiler.MemNameCollisionCertTest.fakeD]]
    withLocalDeclD `hRc hRcT fun hRc => do
      let pf ← mkAppOptM ``Sparkle.Tests.Compiler.MemNameCollisionDesignTest.collSame_closesR
        #[a[0]!, a[1]!, a[2]!, a[3]!, hRc]
      unless ← isDefEq (← inferType pf) clT do
        throwError "collSame_closesR does not prove the binder{indentExpr clT}"
      let args := xs.set! i pf
      let newXs := (xs.extract 0 i).push hRc ++ xs.extract (i + 1) xs.size
      let v := mkAppN (mkConst base) args
      if body.hasAnyFVar (· == xs[i]!.fvarId!) then
        throwError "{base}: the conclusion depends on the closing binder"
      pure (← mkForallFVars newXs body, ← mkLambdaFVars newXs v)
  let type ← instantiateMVars type
  let value ← instantiateMVars value
  Lean.addDecl (.thmDecl { name, levelParams := [], type, value })

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM <|
  Lean.withOptions (fun o => Lean.Elab.async.set o false) addDesign

/-! ## The audit (an error on any failure) -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let f := ``Sparkle.Tests.Compiler.MemNameCollisionCertTest.collSameR
  let old := f ++ `machine_design_svR0
  let openN := f ++ `machine_design_noPortsR0
  let fin := `Sparkle.Tests.Compiler.MemNameCollisionDesignTest.collSame_design
  -- (a) standard axioms
  for n in [``Tools.ShippingMemKid.kidsM_runFactsT, ``Tools.ShippingMemKid.kidsM_outsCheckT,
      ``Tools.ShippingMemKid.kidsM_mixedT, ``Tools.ShippingMemKid.kidsM_designCheckT,
      ``Tools.ShippingMemKid.kidFactsT_of, ``Tools.ShippingMemKid.memKidT_facts,
      ``Sparkle.Tests.Compiler.MemNameCollisionDesignTest.collSame_kids,
      ``Sparkle.Tests.Compiler.MemNameCollisionDesignTest.collSame_closesR, old, openN, fin] do
    unless (← Lean.getEnv).contains n do throwError "{n}: missing"
    Tests.Compiler.NoPortsTest.stdAxioms n
  -- (b) no checker constant, no TagsAgree in the final statement; no MachineClosesAt
  let finT := (← Lean.getConstInfo fin).type
  for k in Tests.Compiler.NoPortsTest.checkers ++ Tests.Compiler.NoPortsMemSeqMemTest.forbiddenMem ++
      [``Tools.ShippingInstTagged.TagsAgree, ``Tools.ShippingInstTagged.tagAgrees,
       ``Tools.ShippingChildInv.MachineClosesAt] do
    if (finT.find? (·.isConstOf k)).isSome then
      throwError "{fin}: the statement mentions {k}"
  -- (c) the inventory of the base endpoint: the four checks and the closing
  let oldT := (← Lean.getConstInfo old).type
  for k in [``Tools.ShippingHierPremisesBase.shipsHierCheck,
      ``Tools.ShippingMachineShipsHier.kidsMixed, ``Tools.ShippingDesignSV.designCheck,
      ``Tools.ShippingDesignSVBack.outsCheck, ``Tools.ShippingChildInv.MachineClosesAt] do
    unless (oldT.find? (·.isConstOf k)).isSome do
      throwError "{old}: does not mention {k} (the inventory is wrong)"
  -- (d) the Prop binders, LOGGED for the before/after list
  let bindersOf (t : Lean.Expr) : Lean.MetaM (Array String) :=
    Lean.Meta.forallTelescope t fun xs _ => do
      let mut out : Array String := #[]
      for x in xs do
        let ty ← Lean.instantiateMVars (← Lean.Meta.inferType x)
        if ← Lean.Meta.isProp ty then out := out.push (toString (← Lean.Meta.ppExpr ty))
      return out
  let inner (t : Lean.Expr) := Lean.Meta.forallTelescope t fun _ body =>
    Tests.Compiler.NoPortsTest.innerAntecedents body
  for (n, t) in [(old, oldT), (openN, (← Lean.getConstInfo openN).type), (fin, finT)] do
    let bs ← bindersOf t
    let ia ← inner t
    Lean.logInfo m!"COLLDESIGN PREMISES {n}: {bs.size} Prop binders {bs}; {ia.size} antecedents under the existentials {ia.map (·.1)}"
  let bFin ← bindersOf finT
  unless bFin.size == 3 do
    throwError "{fin}: {bFin.size} Prop binders, expected 3 (the run, MachineDefines collSameR, MachineDefines SparkleMem.sync.4.8)"
  let iFin ← inner finT
  unless iFin.size == 1 do
    throwError "{fin}: {iFin.size} antecedents under the existentials, expected 1 (the boundary)"

#print axioms Sparkle.Tests.Compiler.MemNameCollisionDesignTest.collSame_design
