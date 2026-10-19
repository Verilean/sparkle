import Tests.Compiler.MemNameCollisionGateDesignTest
import Tests.Compiler.NoPortsGrandHTest
import Tools.ShippingGateKidFactsT
import Tools.ShippingKidsMixedC

/-! # The design endpoint of the original gate-collision parent `collMixSame`, its check antecedents discharged (round par/o-gchk)

WRITTEN, NOT BUILT.

`collMixSame` (`Tests/Compiler/MemNameCollisionGateCertTest.lean`): a register loop, a
synchronous 4/8 memory (origin `.mem false 4 8`) and a call, on the same argument `let`s, of the
combinational gate-route declaration `SparkleMem.sync.4.8` (a copy of `fakeSrc` = `wd + 1`, origin
`.ord`). Both call entries carry the one name `SparkleMem.sync.4.8`.

`collMixSame_designG` (`MemNameCollisionGateDesignTest`) states the shipped design's `DesignSV`
at depth 0 with, under `∃ raw D`, FIVE antecedents: `shipsHierCheck`, `designCheck … 0`,
`outsCheck … 0`, the boundary (`ChildBnd ∧ EntryDefines SparkleMem.sync.4.8
SparkleMem.sync.4.8.gateValue`), `kidsMixed`. `kidsMixed` is FALSE here, as read off the compiler:
the gate child drives `out` by `assign "out" (.ref w)` (`Sparkle.Compiler.Elab.emitLeaves`), so
neither `kidsMasked` nor `kidsMem` holds at its instance. That statement is therefore vacuous.

`collMixSame_designClosed` (this file):

* the children bound is `Tools.ShippingKidsMixedC.kidsMixedC` (masked ∨ memory ∨ COMBINATIONAL
  chain), with `mixCKS_boundedIn` (`KSBoundedIn … flatKS … mixInv`, PROVED) as `hBd`. The head is
  `Tools.ShippingNoPorts.machine_design_noPorts` itself, at `collMixSame.machine_ships_hierRG`'s
  arguments with `Bd`, `hBd` replaced. `composed` / `soundL` do not mention `Bd`;
* `shipsHierCheck`, `designCheck`, `outsCheck` are DISCHARGED (`collMixSame_runFacts` / `_outsG0` /
  `_designP0`, from `KidFactsTC` by origin: memory by `memKidT_facts`, the `.ord` entry by
  `gateKidT_factsC`);
* the children bound `kidsMixedC` is DISCHARGED at run level (`collMixSame_mixedC`, by
  `core_kidsMixedCMT`): memory entry `FlatOk` (`memKidT_facts.flat`), gate entry `combOk`;
* `MachineClosesAt collMixSame` is discharged by `collMixSame_closesR hR0`;
* the boundary's reflection conjunct is MERGED with `hR0` by `syncGate_value`
  (`exists_bnd_merge`). Under `∃` only `ChildBnd` remains.

REMAINING (an explicit binder, NOT derived): `hchain : ∀ y, RealChild mref cref syncName y →
combOk y.1 (declWidth y.1) = true`. It says that the gate child's module reaches `out` by a
self-bounded chain (`w := add(…)`, then `out := w`). Read off the compiler it is TRUE for
`fakeSrc`: `Elab.lean`, the binary-operator arm, `emitAssign resWire (.op op [.ref a, .ref b])`;
`emitLeaves`, `out := ref resWire`; the checked merge leaves three distinct nodes unchanged.
Deriving it needs a SYNTACTIC fact about the mixed gate translator's top node. No current
theorem pins the module beyond values on bounded inputs (`RawValueAt`) and typedness. That
is a separate compiler-facing unit. -/

namespace Sparkle.Tests.Compiler.MemNameCollisionGateClosedTest
open Sparkle.Tests.Compiler.MemNameCollisionGateCertTest
open Sparkle.Compiler.MachInstOrigin (InstOrigin)
open Tools.ShippingInstTagged (originAt)
open Tools.ShippingMemKid (KidFactsTC memOuts memIns gateOuts gateIns)

/-- The callee's outputs, keyed by the entry's ORIGIN. -/
noncomputable def outsG : InstOrigin → List Sparkle.IR.Machine.OutField
  | .mem _ _ dw => memOuts dw
  | .ord => gateOuts fakeSrc.gateSort.width
  | .field _ => gateOuts fakeSrc.gateSort.width

/-- The callee's argument widths, keyed by the entry's ORIGIN. -/
noncomputable def insG : InstOrigin → List Nat
  | .mem _ aw dw => memIns aw dw
  | .ord => gateIns fakeSrc.gateBinders
  | .field _ => gateIns fakeSrc.gateBinders

/-- Every entry is named `SparkleMem.sync.4.8`, of origin the memory or `.ord` (decided). -/
theorem collMixSame_entry : ∀ (k : Nat) (hk : k < (collMixSame.machineData).shape.insts.length),
    ((collMixSame.machineData).shape.insts[k]).1 = syncName ∧
      (originAt (collMixSame.machineData).shape k = .mem false 4 8 ∨
        originAt (collMixSame.machineData).shape k = .ord) := by
  first | decide | decide +kernel

/-- `fakeSrc`'s result is 8 bits wide (≠ 1). -/
theorem fakeSrc_width : fakeSrc.gateSort.width ≠ 1 := by
  first | decide | decide +kernel

/-- **`KidFactsTC` of every call entry of `collMixSame`, by ORIGIN**, at depth 0: the memory
origin by `memKidT_facts`, the `.ord` entry (named as the memory!) by `gateKidT_factsC` at
`fakeSrc`'s gate reading, through the colliding declaration's reflection `hR0`. -/
theorem collMixSame_kids {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref syncName fakeSrc.gateValue) :
    ∀ (k : Nat) (hk : k < (collMixSame.machineData).shape.insts.length),
      KidFactsTC mref cref (originAt (collMixSame.machineData).shape k)
        ((collMixSame.machineData).shape.insts[k]).1
        (outsG (originAt (collMixSame.machineData).shape k))
        (insG (originAt (collMixSame.machineData).shape k)) 0 := by
  intro k hk
  obtain ⟨hn, ho⟩ := collMixSame_entry k hk
  rcases ho with ho | ho
  · rw [ho]
    exact (Tools.ShippingMemKid.memKidT_facts (Tools.ShippingInstTagged.child?_mem false 4 8)).toC
  · rw [ho, hn]
    exact Tools.ShippingMemKid.gateKidT_factsC (o := InstOrigin.ord) (c := syncName)
      (bs := fakeSrc.gateBinders) rfl hR0
      fakeSrc.gate_old fakeSrc.gate_peel fakeSrc.gate_wf
      (Tools.ShippingGateChild.bool_positions (by decide))
      (Tools.ShippingGateChild.bits_positions (by decide)) fakeSrc_width 0

theorem collMixSame_callWidths : Tools.ShippingCallWidths.callWidthsOk collMixSame.machineData 3
    (fun k => outsG (originAt (collMixSame.machineData).shape k)) = true := by
  first | decide | decide +kernel

theorem collMixSame_callArgs : Tools.ShippingPortsMatchRaw.callArgsOk collMixSame.machineData 3
    (fun k => insG (originAt (collMixSame.machineData).shape k)) = true := by
  first | decide | decide +kernel

theorem collMixSame_outChars :
    ∀ o ∈ (collMixSame.machineData).shape.layout.outs,
      ∀ c ∈ o.name.toList, Sparkle.IR.NameHints.charOk c = true := by
  first | decide | decide +kernel

set_option maxHeartbeats 4000000 in
/-- **The run's facts of `collMixSame`'s full-entry module** (`kidsC_runFactsT`); the closing
from `hR0`. -/
theorem collMixSame_runFacts {mctx : Lean.Meta.Context}
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
    Tools.ShippingGuardsSound.RunFacts (Tools.ShippingMachineLinked.childMap D.modules) b :=
  Tools.ShippingMemKid.kidsC_runFactsT (nDecl := 3)
    collMixSame.machineData collMixSame.machine_ok collMixSame.machine_body
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel)
    (fun k => outsG (originAt (collMixSame.machineData).shape k))
    (fun k => insG (originAt (collMixSame.machineData).shape k)) 0
    (collMixSame_kids hR0) collMixSame_callWidths
    hB hcore hpost entry (collMixSame_closesR hR0)

set_option maxHeartbeats 4000000 in
/-- **The output check at depth 0 under the statement-kind gate** (`kidsC_outsCheckT`). -/
theorem collMixSame_outsG0 {mctx : Lean.Meta.Context}
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
    (hg : Sparkle.IR.RefineCheck.hierGate b = true)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w) :
    Tools.ShippingDesignSVBack.outsCheck (Tools.ShippingMachineLinked.childMap D.modules) 0
      (Sparkle.IR.OptCheck.checkedOptimize b) = true :=
  Tools.ShippingMemKid.kidsC_outsCheckT (nDecl := 3)
    collMixSame.machineData collMixSame.machine_ok collMixSame.machine_body
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel)
    (fun k => outsG (originAt (collMixSame.machineData).shape k))
    (fun k => insG (originAt (collMixSame.machineData).shape k)) 0
    (collMixSame_kids hR0)
    hB hcore hpost entry (collMixSame_closesR hR0) hg

set_option maxHeartbeats 4000000 in
/-- **`designCheck` at depth 0 of the shipped module, with no check premise**
(`kidsC_designCheckT`). -/
theorem collMixSame_designP0 {mctx : Lean.Meta.Context}
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
    Tools.ShippingDesignSV.designCheck (Tools.ShippingMachineLinked.childMap D.modules) 0
      (Sparkle.IR.OptCheck.checkedOptimize b) = true :=
  Tools.ShippingMemKid.kidsC_designCheckT (nDecl := 3)
    collMixSame.machineData collMixSame.machine_ok collMixSame.machine_body
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel)
    (fun k => outsG (originAt (collMixSame.machineData).shape k))
    (fun k => insG (originAt (collMixSame.machineData).shape k)) 0
    (collMixSame_kids hR0) collMixSame_callWidths collMixSame_callArgs
    hB hcore hpost entry (collMixSame_closesR hR0)
    (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (collMixSame_outChars o ho))
    (by first | decide | decide +kernel)


/-! ## The combinational children bound, at run level -/

/-- Per kid: the memory origin is `FlatOk` (the built memory module), the `.ord` entry is
`combOk` by `hchain`. -/
theorem collMixSame_flatC {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hchain : ∀ y : Tools.ShippingChildInv.Res, Tools.ShippingChildInv.RealChild mref cref syncName y →
      Tools.ShippingKidsMixedC.combOk y.1 (Sparkle.IR.RegDedup.declWidth y.1) = true) :
    ∀ (k : Nat) (hk : k < (collMixSame.machineData).shape.insts.length) (y : Tools.ShippingChildInv.Res),
      Tools.ShippingInstTagged.KidT mref cref (originAt (collMixSame.machineData).shape k)
        ((collMixSame.machineData).shape.insts[k]).1 y →
      Tools.ShippingMemKid.FlatOk y.1 ∨
        Tools.ShippingKidsMixedC.combOk y.1 (Sparkle.IR.RegDedup.declWidth y.1) = true := by
  intro k hk y hy
  obtain ⟨hn, ho⟩ := collMixSame_entry k hk
  rcases ho with ho | ho
  · rw [ho] at hy
    exact Or.inl ((Tools.ShippingMemKid.memKidT_facts
      (Tools.ShippingInstTagged.child?_mem false 4 8)).flat y hy)
  · rw [ho, hn] at hy
    exact Or.inr (hchain y (Tools.ShippingInstTagged.KidT.real hy rfl))

set_option maxHeartbeats 4000000 in
/-- **The three-way children bound of `collMixSame`'s shipped module** (`core_kidsMixedCMT`). -/
theorem collMixSame_mixedC {mctx : Lean.Meta.Context}
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
    (hchain : ∀ y : Tools.ShippingChildInv.Res, Tools.ShippingChildInv.RealChild mref cref syncName y →
      Tools.ShippingKidsMixedC.combOk y.1 (Sparkle.IR.RegDedup.declWidth y.1) = true)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w) :
    Tools.ShippingKidsMixedC.kidsMixedC (Tools.ShippingMachineLinked.childMap D.modules)
      b.body = true :=
  Tools.ShippingKidsMixedC.core_kidsMixedCMT (nDecl := 3)
    collMixSame.machineData collMixSame.machine_ok collMixSame.machine_body
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel)
    (collMixSame_flatC hchain)
    hB hcore hpost entry (collMixSame_closesR hR0)

/-! ## The closed endpoint (MetaM assembly; the kernel checks the result) -/

open Lean Meta

/-- The boundary's reflection conjunct `E` (`EntryDefines … SparkleMem.sync.4.8
SparkleMem.sync.4.8.gateValue`, as the generator writes it) from the binder `hR0`
(`EntryDefines … syncName fakeSrc.gateValue`), by `syncGate_value`. -/
def hEOf (hR0 E : Lean.Expr) : MetaM Lean.Expr := do
  let ns := `Sparkle.Tests.Compiler.MemNameCollisionGateCertTest
  unless E.isAppOfArity ``Tools.ShippingInlineSoundness.EntryDefines 6 do
    throwError "the boundary's second conjunct is not an EntryDefines:{indentExpr E}"
  let a := E.getAppArgs
  let syncN := Sparkle.Compiler.MachMemory.memChildName false 4 8
  unless a[5]!.isConstOf (syncN ++ `gateValue) do
    throwError "the boundary's reflection is not of {syncN ++ `gateValue}:{indentExpr E}"
  let fn := mkAppN (mkConst ``Tools.ShippingInlineSoundness.EntryDefines) (a.extract 0 5)
  -- fn SparkleMem.sync.4.8.gateValue = fn fakeSrc.gateValue
  let h ← mkCongrArg fn (mkConst (ns ++ `syncGate_value))
  let pf ← mkEqMPR h hR0
  unless ← isDefEq (← inferType pf) E do
    throwError "the merged reflection does not prove{indentExpr E}"
  mkExpectedTypeHint pf E

/-- `∃ a b, P ∧ (B ∧ E → R)` ↦ `∃ a b, P ∧ (B → R)` by `exists_bnd_merge`, `E` from `mkHE`.
The new statement keeps every other subterm of the old one verbatim. -/
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

/-- **`collMixSame_designClosed`**: `machine_design_noPorts` at `collMixSame.machine_ships_hierRG`'s
arguments with the children bound `kidsMixedC` / `mixCKS_boundedIn`, the four run hypotheses
discharged by `collMixSame_runFacts` / `_outsG0` / `_mixedC` / `_designP0`, the closing by
`collMixSame_closesR hR0`, the boundary's reflection merged with `hR0`. -/
def addClosed : MetaM Name := do
  let ns := `Sparkle.Tests.Compiler.MemNameCollisionGateCertTest
  let tn := `Sparkle.Tests.Compiler.MemNameCollisionGateClosedTest
  let f := ns ++ `collMixSame
  let ships := f ++ `machine_ships_hierRG
  let name := tn ++ `collMixSame_designClosed
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
  let factsN := tn ++ `collMixSame_runFacts
  let outsN := tn ++ `collMixSame_outsG0
  let mixedN := tn ++ `collMixSame_mixedC
  let designN := tn ++ `collMixSame_designP0
  -- the three-way children bound and its `KSBoundedIn`
  let modT := mkConst ``Sparkle.IR.AST.Module
  let desT := mkConst ``Sparkle.IR.AST.Design
  let (bdC, hBdC) ← withLocalDeclD `b modT fun b => withLocalDeclD `D desT fun D => do
    let cm ← mkAppM ``Tools.ShippingMachineLinked.childMap #[← mkAppM ``Sparkle.IR.AST.Design.modules #[D]]
    let body ← mkAppM ``Sparkle.IR.AST.Module.body #[b]
    let bd ← mkEq (← mkAppM ``Tools.ShippingKidsMixedC.kidsMixedC #[cm, body]) (mkConst ``Bool.true)
    let hBd ← withLocalDeclD `h bd fun h => do
      mkLambdaFVars #[b, D, h] (← mkAppM ``Tools.ShippingKidsMixedC.mixCKS_boundedIn #[cm, body, h])
    pure (← mkLambdaFVars #[b, D] bd, hBd)
  let (type, value) ← forallTelescope (← inferType (mkConst ships)) fun xs _ => do
    unless xs.size == 11 do throwError "{ships}: {xs.size} binders, expected 11"
    let clT ← instantiateMVars (← inferType xs[10]!)
    unless clT.isAppOf ``Tools.ShippingChildInv.MachineClosesAt do
      throwError "{ships}: the last binder is not MachineClosesAt:{indentExpr clT}"
    let hR0T := mkAppN (mkConst ``Tools.ShippingInlineSoundness.EntryDefines)
      #[xs[0]!, xs[1]!, xs[2]!, xs[3]!, mkConst (ns ++ `syncName), mkConst (ns ++ `fakeSrc ++ `gateValue)]
    let hchainT ← withLocalDeclD `y (mkConst ``Tools.ShippingChildInv.Res) fun y => do
      let rc := mkAppN (mkConst ``Tools.ShippingChildInv.RealChild) #[xs[1]!, xs[3]!, mkConst (ns ++ `syncName), y]
      let y1 ← mkAppM ``Prod.fst #[y]
      let concl ← mkEq (← mkAppM ``Tools.ShippingKidsMixedC.combOk
        #[y1, ← mkAppM ``Sparkle.IR.RegDedup.declWidth #[y1]]) (mkConst ``Bool.true)
      mkForallFVars #[y] (← mkArrow rc concl)
    withLocalDeclD `hR0 hR0T fun hR0 => do
    withLocalDeclD `hchain hchainT fun hchain => do
    let closesPf ← mkAppOptM (ns ++ `collMixSame_closesR) #[xs[0]!, xs[1]!, xs[2]!, xs[3]!, hR0]
    unless ← isDefEq (← inferType closesPf) clT do
      throwError "collMixSame_closesR does not prove the closing binder{indentExpr clT}"
    let xs' := xs.set! 10 closesPf
    let args : Array (Option Lean.Expr) :=
      #[some (mkNatLit 0), some a[3]!, some a[4]!, some a[5]!, some bdC, some a[7]!,
        some hBdC, some a[9]!, some a[10]!, some a[11]!,
        some a[12]!, some a[13]!, some a[14]!, some a[15]!, some a[16]!, some a[17]!,
        some a[18]!, some a[19]!, some a[20]!, some a[21]!,
        some a[22]!, some a[23]!, some a[24]!] ++ xs'.map some
    let pre ← instantiateMVars
      (← mkAppOptM ``Tools.ShippingNoPorts.machine_design_noPorts args)
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
    -- the children's bound `kidsMixedC`: zs = raw D w1 hcore hpost hBnd (cut at 6)
    let .forallE _ TM _ _ ← whnfR (← inferType pre)
      | throwError "{f}: the head's children-bound hypothesis is not where it is expected"
    let hMixed ← forallBoundedTelescope TM (some 6) fun zs goal => do
      unless zs.size == 6 do throwError "{f}: the children-bound hypothesis has {zs.size} binders"
      let p ← mkAppM mixedN #[zs[3]!, zs[4]!, xs[9]!, hR0, hchain]
      mkLambdaFVars zs (← Tests.Compiler.NoPortsGrandHTest.dischargeWith mixedN p zs[5]! goal #[])
    let pre := mkApp pre hMixed
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
    let newXs := (xs.extract 0 10).push hR0 |>.push hchain
    pure (← mkForallFVars newXs mergedT, ← mkLambdaFVars newXs merged)
  let type ← instantiateMVars type
  let value ← instantiateMVars value
  for c in [``Tools.ShippingHierPremisesBase.shipsHierCheck, ``Tools.ShippingDesignSV.designCheck,
      ``Tools.ShippingDesignSVBack.outsCheck, ``Tools.ShippingChildInv.MachineClosesAt,
      ``Tools.ShippingMachineShipsHier.kidsMixed, ``Tools.ShippingKidsMixedC.kidsMixedC] do
    if (type.find? (·.isConstOf c)).isSome then
      throwError "{name}: REFUSED, the statement still mentions {c}"
  Tools.ShippingMachineLinkedCommand.addTheorem name type value
  return name

/-- The occurrences of `k` applied to `n` arguments in `e` (for the audit). -/
partial def countApps (k : Name) (n : Nat) : Lean.Expr → Nat
  | e@(.app f a) => (if e.isAppOfArity k n then 1 else 0) + countApps k n f + countApps k n a
  | .lam _ t b _ => countApps k n t + countApps k n b
  | .forallE _ t b _ => countApps k n t + countApps k n b
  | .letE _ t v b _ => countApps k n t + countApps k n v + countApps k n b
  | .mdata _ e => countApps k n e
  | .proj _ _ e => countApps k n e
  | _ => 0

end Sparkle.Tests.Compiler.MemNameCollisionGateClosedTest

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let name ← Lean.withOptions (fun o => Lean.Elab.async.set o false) <|
    Sparkle.Tests.Compiler.MemNameCollisionGateClosedTest.addClosed
  Lean.logInfo m!"GATECLOSED [{name}]: shipsHierCheck, designCheck, outsCheck discharged (KidFactsTC by origin: memKidT_facts, gateKidT_factsC); MachineClosesAt by collMixSame_closesR; the boundary's reflection merged with hR0 by syncGate_value; the children bound kidsMixedC (masked ∨ memory ∨ combinational chain, mixCKS_boundedIn) discharged by core_kidsMixedCMT; REMAINING binder: hchain (the gate child's combOk)"

/-! ## The audit (an error on any failure) -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let ns := `Sparkle.Tests.Compiler.MemNameCollisionGateCertTest
  let tn := `Sparkle.Tests.Compiler.MemNameCollisionGateClosedTest
  let old := `Sparkle.Tests.Compiler.MemNameCollisionGateDesignTest.collMixSame_designG
  let fin := tn ++ `collMixSame_designClosed
  -- (a) standard axioms
  for n in [``Tools.ShippingKidsMixedC.selfBounded_lt,
      ``Tools.ShippingKidsMixedC.evalAssigns_ref_final, ``Tools.ShippingKidsMixedC.combChain_bound,
      ``Tools.ShippingKidsMixedC.mixCKS_boundedIn, ``Tools.ShippingKidsMixedC.kidsMixedC_of,
      ``Tools.ShippingKidsMixedC.core_kidsMixedCMT,
      ``Tools.ShippingMemKid.KidFactsT.toC, ``Tools.ShippingMemKid.gateKidT_factsC,
      ``Tools.ShippingMemKid.kidsC_runFactsT, ``Tools.ShippingMemKid.kidsC_outsCheckT,
      ``Tools.ShippingMemKid.kidsC_designCheckT, ``Tools.ShippingMemKid.exists_bnd_merge,
      tn ++ `collMixSame_kids, tn ++ `collMixSame_runFacts, tn ++ `collMixSame_outsG0,
      tn ++ `collMixSame_designP0, tn ++ `collMixSame_flatC, tn ++ `collMixSame_mixedC,
      ns ++ `syncGate_value, old, fin] do
    unless (← Lean.getEnv).contains n do throwError "{n}: missing"
    Tests.Compiler.NoPortsTest.stdAxioms n
  -- (b) the final statement: no checker, no children bound (old or new), no closing, no TagsAgree
  let finT := (← Lean.getConstInfo fin).type
  for k in Tests.Compiler.NoPortsTest.checkers ++
      [``Tools.ShippingMachineShipsHier.kidsMem, ``Tools.ShippingMachineShipsHier.kidsMasked,
       ``Tools.ShippingMachineShipsHier.kidsMixed, ``Tools.ShippingKidsMixedC.kidsMixedC,
       ``Tools.ShippingKidsMixedC.combAt,
       ``Tools.ShippingInstTagged.TagsAgree, ``Tools.ShippingInstTagged.tagAgrees,
       ``Tools.ShippingChildInv.MachineClosesAt] do
    if (finT.find? (·.isConstOf k)).isSome then
      throwError "{fin}: the statement mentions {k}"
  -- the ONE remaining premise is the gate child's chain (a binder, reported, not hidden)
  unless (finT.find? (·.isConstOf ``Tools.ShippingKidsMixedC.combOk)).isSome do
    throwError "{fin}: does not mention combOk (the report says hchain remains)"
  -- (c) the inventory of the base statement: the four checks and the boundary's reflection
  let oldT := (← Lean.getConstInfo old).type
  for k in [``Tools.ShippingHierPremisesBase.shipsHierCheck,
      ``Tools.ShippingMachineShipsHier.kidsMixed, ``Tools.ShippingDesignSV.designCheck,
      ``Tools.ShippingDesignSVBack.outsCheck] do
    unless (oldT.find? (·.isConstOf k)).isSome do
      throwError "{old}: does not mention {k} (the inventory is wrong)"
  -- (d) the Prop binders and the antecedents under the existentials, LOGGED
  let bindersOf (t : Lean.Expr) : Lean.MetaM (Array String) :=
    Lean.Meta.forallTelescope t fun xs _ => do
      let mut out : Array String := #[]
      for x in xs do
        let ty ← Lean.instantiateMVars (← Lean.Meta.inferType x)
        if ← Lean.Meta.isProp ty then out := out.push (toString (← Lean.Meta.ppExpr ty))
      return out
  let inner (t : Lean.Expr) := Lean.Meta.forallTelescope t fun _ body =>
    Tests.Compiler.NoPortsTest.innerAntecedents body
  for (n, t) in [(old, oldT), (fin, finT)] do
    let bs ← bindersOf t
    let ia ← inner t
    Lean.logInfo m!"GATECLOSED PREMISES {n}: {bs.size} Prop binders {bs}; {ia.size} antecedents under the existentials {ia.map (·.1)}"
  let bFin ← bindersOf finT
  unless bFin.size == 4 do
    throwError "{fin}: {bFin.size} Prop binders, expected 4 (the run, MachineDefines collMixSame, EntryDefines syncName fakeSrc.gateValue, hchain)"
  let iFin ← inner finT
  unless iFin.size == 1 do
    throwError "{fin}: {iFin.size} antecedents under the existentials, expected 1 (ChildBnd): {iFin.map (·.1)}"
  -- exactly ONE reflection (`EntryDefines`) in the whole statement: the merged binder
  let cnt := Sparkle.Tests.Compiler.MemNameCollisionGateClosedTest.countApps
    ``Tools.ShippingInlineSoundness.EntryDefines 6 finT
  unless cnt == 1 do
    throwError "{fin}: {cnt} EntryDefines occurrences, expected 1 (the duplicate was not merged)"
  let cntOld := Sparkle.Tests.Compiler.MemNameCollisionGateClosedTest.countApps
    ``Tools.ShippingInlineSoundness.EntryDefines 6 oldT
  Lean.logInfo m!"GATECLOSED {fin}: EntryDefines occurrences {cnt} (was {cntOld} in {old})"

#print axioms Sparkle.Tests.Compiler.MemNameCollisionGateClosedTest.collMixSame_designClosed

/-! ## Shadow (asserting): the closed statement is not vacuous on the compiled design

On the certified compile of `collMixSame` (`synthesizeCombinationalCoreWith`, certified front end — the
route of the run, not the run itself): the OLD children bound `kidsMixed` is FALSE (why the
`machine_design_svRG0` statements are vacuous), the three-way `kidsMixedC` is TRUE, and the colliding
gate child's module satisfies `combOk` (the remaining binder `hchain` holds for this compile). Shadow
evidence about one compile, not a proof of `hchain`. -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let n := ``Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.collMixSame
  let (top, D) ← Sparkle.Compiler.Elab.synthesizeCombinationalCoreWith
    (fun env e h t n => Sparkle.Compiler.Elab.translateExprToWire env e h t n) n [] false
    (certifiedFrontEnd := true)
  let cm := Tools.ShippingMachineLinked.childMap D.modules
  for (lbl, body) in [("top", top.body),
      ("merged", (Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule top)).body)] do
    if Tools.ShippingMachineShipsHier.kidsMixed cm body then
      throwError "{n} ({lbl}): kidsMixed holds — the vacuity finding no longer applies"
    unless Tools.ShippingKidsMixedC.kidsMixedC cm body do
      throwError "{n} ({lbl}): kidsMixedC fails on the compiled design"
  let mn := Sparkle.IR.ModuleName.ofDecl Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.syncName
  let some c := D.modules.find? (·.name == mn) | throwError "{n}: no module {mn}"
  unless Tools.ShippingKidsMixedC.combOk c (Sparkle.IR.RegDedup.declWidth c) do
    throwError "{n}: the colliding gate child's module fails combOk"
  Lean.logInfo m!"GATECLOSED SHADOW {n}: kidsMixed false, kidsMixedC true (top, merged); combOk true on {mn}"
