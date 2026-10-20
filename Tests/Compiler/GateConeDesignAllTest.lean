import Tests.Compiler.GateConeDesignTypedTest
import Tools.ShippingGateDesignAll

/-! # The seven gate-route parents: EVERY closed run (worker N, round 15)

WRITTEN, NOT BUILT. TARGET-ONLY (`lake build Tests.Compiler.GateConeDesignAllTest`;
not in `Tests.AllTests`). GENERATED from the round-14 `…_gate_designSVN3`
statements (`Tests/Compiler/GateConeDesignTypedTest.lean`); the old theorems
are kept.

`…_gate_designSVall` = `…_gate_designSVN3` with the design part in the FULL
form of `Tools.ShippingShipsDesignSVAll.ships_design_svN_all`'s conclusion:
the existence of a closed run of the emitted texts showing the source on
`out` AND that EVERY closed run `envs'` from the same seeding `seedIn b ins`
and the same states `⟨st0, mems, kids⟩` has length `T` and shows the source.

The universal half is `Tools.ShippingGateDesignAll.gate_sv_all`
(`design_sv_all` at depth 0) with every premise derived:
* `hierGate b` — `…_gate_designA`'s `ModOk` and the post-pass shape
  (`hierGate_of_modOk`, as in the round-12 proofs);
* `designCheck … 0 (checkedOptimize b)` and `outsCheck … 0 (checkedOptimize b)`
  — from the six facts of `b` of `gate_combFacts` and `designSideB3` of
  `gate_typedFacts` (`gate_shipped_checks`; `outsCheck` from the shipped
  module's `kidsComb`, `outsCheck0_of_kidsComb`);
* the three width premises (seeding, start state, instance states) — the
  third to fifth conjuncts of `DesignSideR`, the antecedent the
  `…_gate_designSVN3` already carry.

Premises: exactly those of `…_gate_designSVN3` (the run, `GateDefines` NOT
ALLOWED, `ChildBnd`, `EntryDefines childAdd`). Antecedent on the design part:
`DesignSideR` (unchanged). -/
namespace Sparkle.Tests.Compiler.GateConeDesignAllTest

section svn3
open Lean Sparkle.Compiler.Elab Sparkle.IR.Semantics
open Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.Tests.Compiler.ShippingHierarchySoundnessTest
open Sparkle.Tests.Compiler.GateConeRunTest
open Sparkle.Tests.Compiler.GateConeKidTest
open Sparkle.Tests.Compiler.GateConeEntryTest
open Tools.ShippingGateDefines (GateDefines)
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingChildInv (ChildBnd CacheInv Res)
open Tools.ShippingInlineSoundness (EntryDefines)
open Tools.ShippingFirstGateKid (ownChild)
open Tools.ShippingSeqOptSoundness (seedIn)
open Tools.ShippingGateDesignLift (DesignHasChild PostKeeps OptKeepsOut DesignSide
  gate_designSV_of_steps)

/-- **`parentMix` at the design level, EVERY closed run**: `parentMix_gate_designSVN3`
(existence) and every closed run from the same seeding and states has length
`T` and shows the source (`Tools.ShippingGateDesignAll.gate_sv_all`). Left:
`DesignSideR`. -/
theorem parentMix_gate_designSVall {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinational ``parentMix) mctx mref cctx cref w (b, design) w')
    (gdef : GateDefines mctx mref cctx cref ``parentMix parentMixBinders parentMixBody)
    (bnd : ChildBnd mref cref w)
    (centry : EntryDefines mctx mref cctx cref ``childAdd childAddValue) :
    ∃ (M : Sparkle.IR.AST.Module) (envR : Lean.Environment) (mF : Std.HashMap Lean.Name Res)
      (y : Res),
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
        b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)) ∧
      CacheInv mref cref mF ∧
      Sparkle.Compiler.isHardwareModule envR ``childAdd = true ∧
      mF.get? ``childAdd = some y ∧ ParentMixObservesC (ownChild y) M ∧
      DesignHasChild design.modules y ∧ PostKeeps b M ∧
      (∃ (i0 i1 i2 : FVarId) (cache : IO.Ref (Lean.ExprStructMap String)),
        ∀ {D : DomainConfig} (aS bS : Signal D (BitVec 8)) (T : Nat)
          (ins : Nat → String → Nat) (st0 : String → Nat) (mems : MEnv)
          (kids : String → Tools.ShippingHierState.KidState),
          (∀ t st, t < T → ∃ (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n),
            Tools.ShippingMixedEntrySoundness.Admissible bools bits (seedIn b ins t st)
              (parentMixBinders.zip [i0, i1, i2])
              (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
                (Sparkle.IR.ModuleName.ofDecl ``parentMix)) ∧
            (Tools.ShippingMixedEntrySoundness.prepare bools bits
              (parentMixBinders.zip [i0, i1, i2])
              (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
                (Sparkle.IR.ModuleName.ofDecl ``parentMix))).bits i1 =
              some ⟨8, aS.val (T - 1 - t)⟩ ∧
            (Tools.ShippingMixedEntrySoundness.prepare bools bits
              (parentMixBinders.zip [i0, i1, i2])
              (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
                (Sparkle.IR.ModuleName.ofDecl ``parentMix))).bits i2 =
              some ⟨8, bS.val (T - 1 - t)⟩) →
          Tools.ShippingGateCombSide.DesignSideR design.modules b ins st0 kids →
          (∃ envsO, Tools.ShippingDesignSV.DesignSV
              (Tools.ShippingMachineLinked.childMap design.modules) 0
              (Sparkle.IR.OptCheck.checkedOptimize b) (seedIn b ins) T ⟨st0, mems, kids⟩ envsO ∧
            envsO.length = T ∧
            ∀ (j : Nat) (hj : j < envsO.length),
              (envsO[j]'hj) "out" = ((parentMix aS bS).val j).toNat) ∧
          ∀ envs', Tools.ShippingDesignSV.DesignSV
              (Tools.ShippingMachineLinked.childMap design.modules) 0
              (Sparkle.IR.OptCheck.checkedOptimize b) (seedIn b ins) T ⟨st0, mems, kids⟩ envs' →
            envs'.length = T ∧
            ∀ (j : Nat) (hj : j < envs'.length),
              (envs'[j]'hj) "out" = ((parentMix aS bS).val j).toNat) := by
  obtain ⟨M, envR, mF, y, hpost, hcache, tagR, hy, hobs, hA, hB, i0, i1, i2, cache, H⟩ :=
    Sparkle.Tests.Compiler.GateConeDesignTypedTest.parentMix_gate_designSVN3 hr gdef bnd centry
  have hg : Sparkle.IR.RefineCheck.hierGate b = true := by
    obtain ⟨M', _, _, _, hpost', -, -, -, -, -, hmod'⟩ :=
      Sparkle.Tests.Compiler.GateConeDesignWalkTest.parentMix_gate_designA hr gdef bnd centry
    exact Tools.ShippingGateCombSide.hierGate_of_modOk hmod' hpost'
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := Tools.ShippingGateParentRun.gate_combFacts (c := ``childAdd)
    (n := 2) hr gdef bnd (Sparkle.Tests.Compiler.GateConeDesignNamesTest.childAdd_kidN centry (by decide))
    (fun envR' hacc mF' hleaf L' D' hD' cache' ids nd len =>
      Sparkle.Tests.Compiler.GateConeDesignNamesTest.parentMix_walk2 L' hD' (Sparkle.Tests.Compiler.GateConeTagTest.parentMix_tag hacc) hleaf
        cache' ids nd len)
    (Tools.ShippingGateParentRun.binders_pos_of_all rfl)
  obtain ⟨-, hDB⟩ := Tools.ShippingGateParentRun.gate_typedFacts (c := ``childAdd) (n := 2)
    (fun _ => 8) hr gdef bnd (Sparkle.Tests.Compiler.GateConeDesignTypedTest.childAdd_kidT centry (by decide))
    (fun envR' hacc mF' hleaf L' D' hD' cache' ids nd len =>
      Sparkle.Tests.Compiler.GateConeDesignTypedTest.parentMix_walk3 L' hD' (Sparkle.Tests.Compiler.GateConeTagTest.parentMix_tag hacc) (fun y' hy' => (hleaf y' hy').1)
        (fun y' hy' => Sparkle.Tests.Compiler.GateConeDesignTypedTest.childAdd_w8 (hleaf y' hy').2) cache' ids nd len)
    (Tools.ShippingGateParentRun.binders_pos_of_all rfl)
  refine ⟨M, envR, mF, y, hpost, hcache, tagR, hy, hobs, hA, hB, i0, i1, i2, cache, ?_⟩
  intro Dc aS bS T ins st0 mems kids hadm hR
  obtain ⟨envsO, hD, hlen, hob⟩ := H aS bS T ins st0 mems kids hadm hR
  exact ⟨⟨envsO, hD, hlen, hob⟩,
    Tools.ShippingGateDesignAll.gate_sv_all hg h1 h2 h3 h4 h5 h6 hDB hR hD
      (fun e => e.length = T ∧ ∀ (j : Nat) (hj : j < e.length),
        (e[j]'hj) "out" = ((parentMix aS bS).val j).toNat)
      ⟨hlen, hob⟩⟩

/-- **`parentTwoCalls` at the design level, EVERY closed run**: `parentTwoCalls_gate_designSVN3`
(existence) and every closed run from the same seeding and states has length
`T` and shows the source (`Tools.ShippingGateDesignAll.gate_sv_all`). Left:
`DesignSideR`. -/
theorem parentTwoCalls_gate_designSVall {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinational ``parentTwoCalls) mctx mref cctx cref w (b, design) w')
    (gdef : GateDefines mctx mref cctx cref ``parentTwoCalls Sparkle.Tests.Compiler.GateConeTwoCallsTest.parentTwoCallsBinders
      Sparkle.Tests.Compiler.GateConeTwoCallsTest.parentTwoCallsBody)
    (bnd : ChildBnd mref cref w)
    (centry : EntryDefines mctx mref cctx cref ``childAdd childAddValue) :
    ∃ (M : Sparkle.IR.AST.Module) (envR : Lean.Environment) (mF : Std.HashMap Lean.Name Res)
      (y : Res),
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
        b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)) ∧
      CacheInv mref cref mF ∧
      Sparkle.Compiler.isHardwareModule envR ``childAdd = true ∧
      mF.get? ``childAdd = some y ∧ Sparkle.Tests.Compiler.GateConeTwoCallsTest.ParentTwoCallsObservesC (ownChild y) M ∧
      DesignHasChild design.modules y ∧ PostKeeps b M ∧
      (∃ (i0 i1 i2 : FVarId) (cache : IO.Ref (Lean.ExprStructMap String)),
        ∀ {D : DomainConfig} (aS bS : Signal D (BitVec 8)) (T : Nat)
          (ins : Nat → String → Nat) (st0 : String → Nat) (mems : MEnv)
          (kids : String → Tools.ShippingHierState.KidState),
          (∀ t st, t < T → ∃ (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n),
            Tools.ShippingMixedEntrySoundness.Admissible bools bits (seedIn b ins t st)
              (Sparkle.Tests.Compiler.GateConeTwoCallsTest.parentTwoCallsBinders.zip [i0, i1, i2])
              (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
                (Sparkle.IR.ModuleName.ofDecl ``parentTwoCalls)) ∧
            (Tools.ShippingMixedEntrySoundness.prepare bools bits
              (Sparkle.Tests.Compiler.GateConeTwoCallsTest.parentTwoCallsBinders.zip [i0, i1, i2])
              (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
                (Sparkle.IR.ModuleName.ofDecl ``parentTwoCalls))).bits i1 =
              some ⟨8, aS.val (T - 1 - t)⟩ ∧
            (Tools.ShippingMixedEntrySoundness.prepare bools bits
              (Sparkle.Tests.Compiler.GateConeTwoCallsTest.parentTwoCallsBinders.zip [i0, i1, i2])
              (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
                (Sparkle.IR.ModuleName.ofDecl ``parentTwoCalls))).bits i2 =
              some ⟨8, bS.val (T - 1 - t)⟩) →
          Tools.ShippingGateCombSide.DesignSideR design.modules b ins st0 kids →
          (∃ envsO, Tools.ShippingDesignSV.DesignSV
              (Tools.ShippingMachineLinked.childMap design.modules) 0
              (Sparkle.IR.OptCheck.checkedOptimize b) (seedIn b ins) T ⟨st0, mems, kids⟩ envsO ∧
            envsO.length = T ∧
            ∀ (j : Nat) (hj : j < envsO.length),
              (envsO[j]'hj) "out" = ((parentTwoCalls aS bS).val j).toNat) ∧
          ∀ envs', Tools.ShippingDesignSV.DesignSV
              (Tools.ShippingMachineLinked.childMap design.modules) 0
              (Sparkle.IR.OptCheck.checkedOptimize b) (seedIn b ins) T ⟨st0, mems, kids⟩ envs' →
            envs'.length = T ∧
            ∀ (j : Nat) (hj : j < envs'.length),
              (envs'[j]'hj) "out" = ((parentTwoCalls aS bS).val j).toNat) := by
  obtain ⟨M, envR, mF, y, hpost, hcache, tagR, hy, hobs, hA, hB, i0, i1, i2, cache, H⟩ :=
    Sparkle.Tests.Compiler.GateConeDesignTypedTest.parentTwoCalls_gate_designSVN3 hr gdef bnd centry
  have hg : Sparkle.IR.RefineCheck.hierGate b = true := by
    obtain ⟨M', _, _, _, hpost', -, -, -, -, -, hmod'⟩ :=
      Sparkle.Tests.Compiler.GateConeDesignWalkTest.parentTwoCalls_gate_designA hr gdef bnd centry
    exact Tools.ShippingGateCombSide.hierGate_of_modOk hmod' hpost'
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := Tools.ShippingGateParentRun.gate_combFacts (c := ``childAdd)
    (n := 2) hr gdef bnd (Sparkle.Tests.Compiler.GateConeDesignNamesTest.childAdd_kidN centry (by decide))
    (fun envR' hacc mF' hleaf L' D' hD' cache' ids nd len =>
      Sparkle.Tests.Compiler.GateConeDesignNamesTest.parentTwoCalls_walk2 L' hD' (Sparkle.Tests.Compiler.GateConeTwoCallsTest.parentTwoCalls_tag hacc) hleaf
        cache' ids nd len)
    (Tools.ShippingGateParentRun.binders_pos_of_all rfl)
  obtain ⟨-, hDB⟩ := Tools.ShippingGateParentRun.gate_typedFacts (c := ``childAdd) (n := 2)
    (fun _ => 8) hr gdef bnd (Sparkle.Tests.Compiler.GateConeDesignTypedTest.childAdd_kidT centry (by decide))
    (fun envR' hacc mF' hleaf L' D' hD' cache' ids nd len =>
      Sparkle.Tests.Compiler.GateConeDesignTypedTest.parentTwoCalls_walk3 L' hD' (Sparkle.Tests.Compiler.GateConeTwoCallsTest.parentTwoCalls_tag hacc) (fun y' hy' => (hleaf y' hy').1)
        (fun y' hy' => Sparkle.Tests.Compiler.GateConeDesignTypedTest.childAdd_w8 (hleaf y' hy').2) cache' ids nd len)
    (Tools.ShippingGateParentRun.binders_pos_of_all rfl)
  refine ⟨M, envR, mF, y, hpost, hcache, tagR, hy, hobs, hA, hB, i0, i1, i2, cache, ?_⟩
  intro Dc aS bS T ins st0 mems kids hadm hR
  obtain ⟨envsO, hD, hlen, hob⟩ := H aS bS T ins st0 mems kids hadm hR
  exact ⟨⟨envsO, hD, hlen, hob⟩,
    Tools.ShippingGateDesignAll.gate_sv_all hg h1 h2 h3 h4 h5 h6 hDB hR hD
      (fun e => e.length = T ∧ ∀ (j : Nat) (hj : j < e.length),
        (e[j]'hj) "out" = ((parentTwoCalls aS bS).val j).toNat)
      ⟨hlen, hob⟩⟩

/-- **`parentRepeat` at the design level, EVERY closed run**: `parentRepeat_gate_designSVN3`
(existence) and every closed run from the same seeding and states has length
`T` and shows the source (`Tools.ShippingGateDesignAll.gate_sv_all`). Left:
`DesignSideR`. -/
theorem parentRepeat_gate_designSVall {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinational ``parentRepeat) mctx mref cctx cref w (b, design) w')
    (gdef : GateDefines mctx mref cctx cref ``parentRepeat Sparkle.Tests.Compiler.GateConeRepeatTest.parentRepeatBinders
      Sparkle.Tests.Compiler.GateConeRepeatTest.parentRepeatBody)
    (bnd : ChildBnd mref cref w)
    (centry : EntryDefines mctx mref cctx cref ``childAdd childAddValue) :
    ∃ (M : Sparkle.IR.AST.Module) (envR : Lean.Environment) (mF : Std.HashMap Lean.Name Res)
      (y : Res),
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
        b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)) ∧
      CacheInv mref cref mF ∧
      Sparkle.Compiler.isHardwareModule envR ``childAdd = true ∧
      mF.get? ``childAdd = some y ∧ Sparkle.Tests.Compiler.GateConeRepeatTest.ParentRepeatObservesC (ownChild y) M ∧
      DesignHasChild design.modules y ∧ PostKeeps b M ∧
      (∃ (i0 i1 i2 : FVarId) (cache : IO.Ref (Lean.ExprStructMap String)),
        ∀ {D : DomainConfig} (aS bS : Signal D (BitVec 8)) (T : Nat)
          (ins : Nat → String → Nat) (st0 : String → Nat) (mems : MEnv)
          (kids : String → Tools.ShippingHierState.KidState),
          (∀ t st, t < T → ∃ (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n),
            Tools.ShippingMixedEntrySoundness.Admissible bools bits (seedIn b ins t st)
              (Sparkle.Tests.Compiler.GateConeRepeatTest.parentRepeatBinders.zip [i0, i1, i2])
              (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
                (Sparkle.IR.ModuleName.ofDecl ``parentRepeat)) ∧
            (Tools.ShippingMixedEntrySoundness.prepare bools bits
              (Sparkle.Tests.Compiler.GateConeRepeatTest.parentRepeatBinders.zip [i0, i1, i2])
              (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
                (Sparkle.IR.ModuleName.ofDecl ``parentRepeat))).bits i1 =
              some ⟨8, aS.val (T - 1 - t)⟩ ∧
            (Tools.ShippingMixedEntrySoundness.prepare bools bits
              (Sparkle.Tests.Compiler.GateConeRepeatTest.parentRepeatBinders.zip [i0, i1, i2])
              (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
                (Sparkle.IR.ModuleName.ofDecl ``parentRepeat))).bits i2 =
              some ⟨8, bS.val (T - 1 - t)⟩) →
          Tools.ShippingGateCombSide.DesignSideR design.modules b ins st0 kids →
          (∃ envsO, Tools.ShippingDesignSV.DesignSV
              (Tools.ShippingMachineLinked.childMap design.modules) 0
              (Sparkle.IR.OptCheck.checkedOptimize b) (seedIn b ins) T ⟨st0, mems, kids⟩ envsO ∧
            envsO.length = T ∧
            ∀ (j : Nat) (hj : j < envsO.length),
              (envsO[j]'hj) "out" = ((parentRepeat aS bS).val j).toNat) ∧
          ∀ envs', Tools.ShippingDesignSV.DesignSV
              (Tools.ShippingMachineLinked.childMap design.modules) 0
              (Sparkle.IR.OptCheck.checkedOptimize b) (seedIn b ins) T ⟨st0, mems, kids⟩ envs' →
            envs'.length = T ∧
            ∀ (j : Nat) (hj : j < envs'.length),
              (envs'[j]'hj) "out" = ((parentRepeat aS bS).val j).toNat) := by
  obtain ⟨M, envR, mF, y, hpost, hcache, tagR, hy, hobs, hA, hB, i0, i1, i2, cache, H⟩ :=
    Sparkle.Tests.Compiler.GateConeDesignTypedTest.parentRepeat_gate_designSVN3 hr gdef bnd centry
  have hg : Sparkle.IR.RefineCheck.hierGate b = true := by
    obtain ⟨M', _, _, _, hpost', -, -, -, -, -, hmod'⟩ :=
      Sparkle.Tests.Compiler.GateConeDesignWalkTest.parentRepeat_gate_designA hr gdef bnd centry
    exact Tools.ShippingGateCombSide.hierGate_of_modOk hmod' hpost'
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := Tools.ShippingGateParentRun.gate_combFacts (c := ``childAdd)
    (n := 2) hr gdef bnd (Sparkle.Tests.Compiler.GateConeDesignNamesTest.childAdd_kidN centry (by decide))
    (fun envR' hacc mF' hleaf L' D' hD' cache' ids nd len =>
      Sparkle.Tests.Compiler.GateConeDesignNamesTest.parentRepeat_walk2 L' hD' (Sparkle.Tests.Compiler.GateConeRepeatTest.parentRepeat_tag hacc) hleaf
        cache' ids nd len)
    (Tools.ShippingGateParentRun.binders_pos_of_all rfl)
  obtain ⟨-, hDB⟩ := Tools.ShippingGateParentRun.gate_typedFacts (c := ``childAdd) (n := 2)
    (fun _ => 8) hr gdef bnd (Sparkle.Tests.Compiler.GateConeDesignTypedTest.childAdd_kidT centry (by decide))
    (fun envR' hacc mF' hleaf L' D' hD' cache' ids nd len =>
      Sparkle.Tests.Compiler.GateConeDesignTypedTest.parentRepeat_walk3 L' hD' (Sparkle.Tests.Compiler.GateConeRepeatTest.parentRepeat_tag hacc) (fun y' hy' => (hleaf y' hy').1)
        (fun y' hy' => Sparkle.Tests.Compiler.GateConeDesignTypedTest.childAdd_w8 (hleaf y' hy').2) cache' ids nd len)
    (Tools.ShippingGateParentRun.binders_pos_of_all rfl)
  refine ⟨M, envR, mF, y, hpost, hcache, tagR, hy, hobs, hA, hB, i0, i1, i2, cache, ?_⟩
  intro Dc aS bS T ins st0 mems kids hadm hR
  obtain ⟨envsO, hD, hlen, hob⟩ := H aS bS T ins st0 mems kids hadm hR
  exact ⟨⟨envsO, hD, hlen, hob⟩,
    Tools.ShippingGateDesignAll.gate_sv_all hg h1 h2 h3 h4 h5 h6 hDB hR hD
      (fun e => e.length = T ∧ ∀ (j : Nat) (hj : j < e.length),
        (e[j]'hj) "out" = ((parentRepeat aS bS).val j).toNat)
      ⟨hlen, hob⟩⟩

/-- **`parentCmp` at the design level, EVERY closed run**: `parentCmp_gate_designSVN3`
(existence) and every closed run from the same seeding and states has length
`T` and shows the source (`Tools.ShippingGateDesignAll.gate_sv_all`). Left:
`DesignSideR`. -/
theorem parentCmp_gate_designSVall {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinational ``parentCmp) mctx mref cctx cref w (b, design) w')
    (gdef : GateDefines mctx mref cctx cref ``parentCmp Sparkle.Tests.Compiler.GateConeCmpTest.parentCmpBinders
      Sparkle.Tests.Compiler.GateConeCmpTest.parentCmpBody)
    (bnd : ChildBnd mref cref w)
    (centry : EntryDefines mctx mref cctx cref ``childAdd childAddValue) :
    ∃ (M : Sparkle.IR.AST.Module) (envR : Lean.Environment) (mF : Std.HashMap Lean.Name Res)
      (y : Res),
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
        b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)) ∧
      CacheInv mref cref mF ∧
      Sparkle.Compiler.isHardwareModule envR ``childAdd = true ∧
      mF.get? ``childAdd = some y ∧ Sparkle.Tests.Compiler.GateConeCmpTest.ParentCmpObservesC (ownChild y) M ∧
      DesignHasChild design.modules y ∧ PostKeeps b M ∧
      (∃ (i0 i1 i2 : FVarId) (cache : IO.Ref (Lean.ExprStructMap String)),
        ∀ {D : DomainConfig} (aS bS : Signal D (BitVec 8)) (T : Nat)
          (ins : Nat → String → Nat) (st0 : String → Nat) (mems : MEnv)
          (kids : String → Tools.ShippingHierState.KidState),
          (∀ t st, t < T → ∃ (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n),
            Tools.ShippingMixedEntrySoundness.Admissible bools bits (seedIn b ins t st)
              (Sparkle.Tests.Compiler.GateConeCmpTest.parentCmpBinders.zip [i0, i1, i2])
              (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
                (Sparkle.IR.ModuleName.ofDecl ``parentCmp)) ∧
            (Tools.ShippingMixedEntrySoundness.prepare bools bits
              (Sparkle.Tests.Compiler.GateConeCmpTest.parentCmpBinders.zip [i0, i1, i2])
              (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
                (Sparkle.IR.ModuleName.ofDecl ``parentCmp))).bits i1 =
              some ⟨8, aS.val (T - 1 - t)⟩ ∧
            (Tools.ShippingMixedEntrySoundness.prepare bools bits
              (Sparkle.Tests.Compiler.GateConeCmpTest.parentCmpBinders.zip [i0, i1, i2])
              (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
                (Sparkle.IR.ModuleName.ofDecl ``parentCmp))).bits i2 =
              some ⟨8, bS.val (T - 1 - t)⟩) →
          Tools.ShippingGateCombSide.DesignSideR design.modules b ins st0 kids →
          (∃ envsO, Tools.ShippingDesignSV.DesignSV
              (Tools.ShippingMachineLinked.childMap design.modules) 0
              (Sparkle.IR.OptCheck.checkedOptimize b) (seedIn b ins) T ⟨st0, mems, kids⟩ envsO ∧
            envsO.length = T ∧
            ∀ (j : Nat) (hj : j < envsO.length),
              (envsO[j]'hj) "out" = Tools.ShippingMuxLoweringSoundness.encodeBool ((parentCmp aS bS).val j)) ∧
          ∀ envs', Tools.ShippingDesignSV.DesignSV
              (Tools.ShippingMachineLinked.childMap design.modules) 0
              (Sparkle.IR.OptCheck.checkedOptimize b) (seedIn b ins) T ⟨st0, mems, kids⟩ envs' →
            envs'.length = T ∧
            ∀ (j : Nat) (hj : j < envs'.length),
              (envs'[j]'hj) "out" = Tools.ShippingMuxLoweringSoundness.encodeBool ((parentCmp aS bS).val j)) := by
  obtain ⟨M, envR, mF, y, hpost, hcache, tagR, hy, hobs, hA, hB, i0, i1, i2, cache, H⟩ :=
    Sparkle.Tests.Compiler.GateConeDesignTypedTest.parentCmp_gate_designSVN3 hr gdef bnd centry
  have hg : Sparkle.IR.RefineCheck.hierGate b = true := by
    obtain ⟨M', _, _, _, hpost', -, -, -, -, -, hmod'⟩ :=
      Sparkle.Tests.Compiler.GateConeDesignWalkTest.parentCmp_gate_designA hr gdef bnd centry
    exact Tools.ShippingGateCombSide.hierGate_of_modOk hmod' hpost'
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := Tools.ShippingGateParentRun.gate_combFacts (c := ``childAdd)
    (n := 2) hr gdef bnd (Sparkle.Tests.Compiler.GateConeDesignNamesTest.childAdd_kidN centry (by decide))
    (fun envR' hacc mF' hleaf L' D' hD' cache' ids nd len =>
      Sparkle.Tests.Compiler.GateConeDesignNamesTest.parentCmp_walk2 L' hD' (Sparkle.Tests.Compiler.GateConeCmpTest.parentCmp_tag hacc) hleaf
        cache' ids nd len)
    (Tools.ShippingGateParentRun.binders_pos_of_all rfl)
  obtain ⟨-, hDB⟩ := Tools.ShippingGateParentRun.gate_typedFacts (c := ``childAdd) (n := 2)
    Sparkle.Tests.Compiler.GateConeDesignTypedTest.cmpτ hr gdef bnd (Sparkle.Tests.Compiler.GateConeDesignTypedTest.childAdd_kidT centry (by decide))
    (fun envR' hacc mF' hleaf L' D' hD' cache' ids nd len =>
      Sparkle.Tests.Compiler.GateConeDesignTypedTest.parentCmp_walk3 L' hD' (Sparkle.Tests.Compiler.GateConeCmpTest.parentCmp_tag hacc) (fun y' hy' => (hleaf y' hy').1)
        (fun y' hy' => Sparkle.Tests.Compiler.GateConeDesignTypedTest.childAdd_w8 (hleaf y' hy').2) cache' ids nd len)
    (Tools.ShippingGateParentRun.binders_pos_of_all rfl)
  refine ⟨M, envR, mF, y, hpost, hcache, tagR, hy, hobs, hA, hB, i0, i1, i2, cache, ?_⟩
  intro Dc aS bS T ins st0 mems kids hadm hR
  obtain ⟨envsO, hD, hlen, hob⟩ := H aS bS T ins st0 mems kids hadm hR
  exact ⟨⟨envsO, hD, hlen, hob⟩,
    Tools.ShippingGateDesignAll.gate_sv_all hg h1 h2 h3 h4 h5 h6 hDB hR hD
      (fun e => e.length = T ∧ ∀ (j : Nat) (hj : j < e.length),
        (e[j]'hj) "out" = Tools.ShippingMuxLoweringSoundness.encodeBool ((parentCmp aS bS).val j))
      ⟨hlen, hob⟩⟩

/-- **`parentUse` at the design level, EVERY closed run**: `parentUse_gate_designSVN3`
(existence) and every closed run from the same seeding and states has length
`T` and shows the source (`Tools.ShippingGateDesignAll.gate_sv_all`). Left:
`DesignSideR`. -/
theorem parentUse_gate_designSVall {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinational ``parentUse) mctx mref cctx cref w (b, design) w')
    (gdef : GateDefines mctx mref cctx cref ``parentUse parentUseBinders
      Sparkle.Tests.Compiler.GateParentRunGTest.parentUseBody)
    (bnd : ChildBnd mref cref w)
    (centry : EntryDefines mctx mref cctx cref ``childAdd childAddValue) :
    ∃ (M : Sparkle.IR.AST.Module) (envR : Lean.Environment) (mF : Std.HashMap Lean.Name Res)
      (y : Res),
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
        b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)) ∧
      CacheInv mref cref mF ∧
      Sparkle.Compiler.isHardwareModule envR ``childAdd = true ∧
      mF.get? ``childAdd = some y ∧ Sparkle.Tests.Compiler.GateConeUseTest.ParentUseObservesC (ownChild y) M ∧
      DesignHasChild design.modules y ∧ PostKeeps b M ∧
      (∃ (i0 i1 i2 : FVarId) (cache : IO.Ref (Lean.ExprStructMap String)),
        ∀ {D : DomainConfig} (aS bS : Signal D (BitVec 8)) (T : Nat)
          (ins : Nat → String → Nat) (st0 : String → Nat) (mems : MEnv)
          (kids : String → Tools.ShippingHierState.KidState),
          (∀ t st, t < T → ∃ (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n),
            Tools.ShippingMixedEntrySoundness.Admissible bools bits (seedIn b ins t st)
              (parentUseBinders.zip [i0, i1, i2])
              (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
                (Sparkle.IR.ModuleName.ofDecl ``parentUse)) ∧
            (Tools.ShippingMixedEntrySoundness.prepare bools bits
              (parentUseBinders.zip [i0, i1, i2])
              (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
                (Sparkle.IR.ModuleName.ofDecl ``parentUse))).bits i1 =
              some ⟨8, aS.val (T - 1 - t)⟩ ∧
            (Tools.ShippingMixedEntrySoundness.prepare bools bits
              (parentUseBinders.zip [i0, i1, i2])
              (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
                (Sparkle.IR.ModuleName.ofDecl ``parentUse))).bits i2 =
              some ⟨8, bS.val (T - 1 - t)⟩) →
          Tools.ShippingGateCombSide.DesignSideR design.modules b ins st0 kids →
          (∃ envsO, Tools.ShippingDesignSV.DesignSV
              (Tools.ShippingMachineLinked.childMap design.modules) 0
              (Sparkle.IR.OptCheck.checkedOptimize b) (seedIn b ins) T ⟨st0, mems, kids⟩ envsO ∧
            envsO.length = T ∧
            ∀ (j : Nat) (hj : j < envsO.length),
              (envsO[j]'hj) "out" = ((parentUse aS bS).val j).toNat) ∧
          ∀ envs', Tools.ShippingDesignSV.DesignSV
              (Tools.ShippingMachineLinked.childMap design.modules) 0
              (Sparkle.IR.OptCheck.checkedOptimize b) (seedIn b ins) T ⟨st0, mems, kids⟩ envs' →
            envs'.length = T ∧
            ∀ (j : Nat) (hj : j < envs'.length),
              (envs'[j]'hj) "out" = ((parentUse aS bS).val j).toNat) := by
  obtain ⟨M, envR, mF, y, hpost, hcache, tagR, hy, hobs, hA, hB, i0, i1, i2, cache, H⟩ :=
    Sparkle.Tests.Compiler.GateConeDesignTypedTest.parentUse_gate_designSVN3 hr gdef bnd centry
  have hg : Sparkle.IR.RefineCheck.hierGate b = true := by
    obtain ⟨M', _, _, _, hpost', -, -, -, -, -, hmod'⟩ :=
      Sparkle.Tests.Compiler.GateConeDesignWalkTest.parentUse_gate_designA hr gdef bnd centry
    exact Tools.ShippingGateCombSide.hierGate_of_modOk hmod' hpost'
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := Tools.ShippingGateParentRun.gate_combFacts (c := ``childAdd)
    (n := 2) hr gdef bnd (Sparkle.Tests.Compiler.GateConeDesignNamesTest.childAdd_kidN centry (by decide))
    (fun envR' hacc mF' hleaf L' D' hD' cache' ids nd len =>
      Sparkle.Tests.Compiler.GateConeDesignNamesTest.parentUse_walk2 L' hD' (Sparkle.Tests.Compiler.GateConeUseTest.parentUse_tag hacc) hleaf
        cache' ids nd len)
    (Tools.ShippingGateParentRun.binders_pos_of_all rfl)
  obtain ⟨-, hDB⟩ := Tools.ShippingGateParentRun.gate_typedFacts (c := ``childAdd) (n := 2)
    (fun _ => 8) hr gdef bnd (Sparkle.Tests.Compiler.GateConeDesignTypedTest.childAdd_kidT centry (by decide))
    (fun envR' hacc mF' hleaf L' D' hD' cache' ids nd len =>
      Sparkle.Tests.Compiler.GateConeDesignTypedTest.parentUse_walk3 L' hD' (Sparkle.Tests.Compiler.GateConeUseTest.parentUse_tag hacc) (fun y' hy' => (hleaf y' hy').1)
        (fun y' hy' => Sparkle.Tests.Compiler.GateConeDesignTypedTest.childAdd_w8 (hleaf y' hy').2) cache' ids nd len)
    (Tools.ShippingGateParentRun.binders_pos_of_all rfl)
  refine ⟨M, envR, mF, y, hpost, hcache, tagR, hy, hobs, hA, hB, i0, i1, i2, cache, ?_⟩
  intro Dc aS bS T ins st0 mems kids hadm hR
  obtain ⟨envsO, hD, hlen, hob⟩ := H aS bS T ins st0 mems kids hadm hR
  exact ⟨⟨envsO, hD, hlen, hob⟩,
    Tools.ShippingGateDesignAll.gate_sv_all hg h1 h2 h3 h4 h5 h6 hDB hR hD
      (fun e => e.length = T ∧ ∀ (j : Nat) (hj : j < e.length),
        (e[j]'hj) "out" = ((parentUse aS bS).val j).toNat)
      ⟨hlen, hob⟩⟩

/-- **`wrapAdd` at the design level, EVERY closed run**: `wrapAdd_gate_designSVN3`
(existence) and every closed run from the same seeding and states has length
`T` and shows the source (`Tools.ShippingGateDesignAll.gate_sv_all`). Left:
`DesignSideR`. -/
theorem wrapAdd_gate_designSVall {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinational ``wrapAdd) mctx mref cctx cref w (b, design) w')
    (gdef : GateDefines mctx mref cctx cref ``wrapAdd wrapAddBinders
      Sparkle.Tests.Compiler.GateConeWrapAddTest.wrapAddBody)
    (bnd : ChildBnd mref cref w)
    (centry : EntryDefines mctx mref cctx cref ``childAdd childAddValue) :
    ∃ (M : Sparkle.IR.AST.Module) (envR : Lean.Environment) (mF : Std.HashMap Lean.Name Res)
      (y : Res),
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
        b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)) ∧
      CacheInv mref cref mF ∧
      Sparkle.Compiler.isHardwareModule envR ``childAdd = true ∧
      mF.get? ``childAdd = some y ∧ Sparkle.Tests.Compiler.GateConeWrapAddTest.WrapAddObservesC (ownChild y) M ∧
      DesignHasChild design.modules y ∧ PostKeeps b M ∧
      (∃ (i0 i1 : FVarId) (cache : IO.Ref (Lean.ExprStructMap String)),
        ∀ (aS bS : Signal defaultDomain (BitVec 8)) (T : Nat)
          (ins : Nat → String → Nat) (st0 : String → Nat) (mems : MEnv)
          (kids : String → Tools.ShippingHierState.KidState),
          (∀ t st, t < T → ∃ (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n),
            Tools.ShippingMixedEntrySoundness.Admissible bools bits (seedIn b ins t st)
              (wrapAddBinders.zip [i0, i1])
              (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
                (Sparkle.IR.ModuleName.ofDecl ``wrapAdd)) ∧
            (Tools.ShippingMixedEntrySoundness.prepare bools bits
              (wrapAddBinders.zip [i0, i1])
              (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
                (Sparkle.IR.ModuleName.ofDecl ``wrapAdd))).bits i0 =
              some ⟨8, aS.val (T - 1 - t)⟩ ∧
            (Tools.ShippingMixedEntrySoundness.prepare bools bits
              (wrapAddBinders.zip [i0, i1])
              (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
                (Sparkle.IR.ModuleName.ofDecl ``wrapAdd))).bits i1 =
              some ⟨8, bS.val (T - 1 - t)⟩) →
          Tools.ShippingGateCombSide.DesignSideR design.modules b ins st0 kids →
          (∃ envsO, Tools.ShippingDesignSV.DesignSV
              (Tools.ShippingMachineLinked.childMap design.modules) 0
              (Sparkle.IR.OptCheck.checkedOptimize b) (seedIn b ins) T ⟨st0, mems, kids⟩ envsO ∧
            envsO.length = T ∧
            ∀ (j : Nat) (hj : j < envsO.length),
              (envsO[j]'hj) "out" = ((wrapAdd aS bS).val j).toNat) ∧
          ∀ envs', Tools.ShippingDesignSV.DesignSV
              (Tools.ShippingMachineLinked.childMap design.modules) 0
              (Sparkle.IR.OptCheck.checkedOptimize b) (seedIn b ins) T ⟨st0, mems, kids⟩ envs' →
            envs'.length = T ∧
            ∀ (j : Nat) (hj : j < envs'.length),
              (envs'[j]'hj) "out" = ((wrapAdd aS bS).val j).toNat) := by
  obtain ⟨M, envR, mF, y, hpost, hcache, tagR, hy, hobs, hA, hB, i0, i1, cache, H⟩ :=
    Sparkle.Tests.Compiler.GateConeDesignTypedTest.wrapAdd_gate_designSVN3 hr gdef bnd centry
  have hg : Sparkle.IR.RefineCheck.hierGate b = true := by
    obtain ⟨M', _, _, _, hpost', -, -, -, -, -, hmod'⟩ :=
      Sparkle.Tests.Compiler.GateConeDesignWalkTest.wrapAdd_gate_designA hr gdef bnd centry
    exact Tools.ShippingGateCombSide.hierGate_of_modOk hmod' hpost'
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := Tools.ShippingGateParentRun.gate_combFacts (c := ``childAdd)
    (n := 2) hr gdef bnd (Sparkle.Tests.Compiler.GateConeDesignNamesTest.childAdd_kidN centry (by decide))
    (fun envR' hacc mF' hleaf L' D' hD' cache' ids nd len =>
      Sparkle.Tests.Compiler.GateConeDesignNamesTest.wrapAdd_walk2 L' hD' (Sparkle.Tests.Compiler.GateConeWrapAddTest.wrapAdd_tag hacc) hleaf
        cache' ids nd len)
    (Tools.ShippingGateParentRun.binders_pos_of_all rfl)
  obtain ⟨-, hDB⟩ := Tools.ShippingGateParentRun.gate_typedFacts (c := ``childAdd) (n := 2)
    (fun _ => 8) hr gdef bnd (Sparkle.Tests.Compiler.GateConeDesignTypedTest.childAdd_kidT centry (by decide))
    (fun envR' hacc mF' hleaf L' D' hD' cache' ids nd len =>
      Sparkle.Tests.Compiler.GateConeDesignTypedTest.wrapAdd_walk3 L' hD' (Sparkle.Tests.Compiler.GateConeWrapAddTest.wrapAdd_tag hacc) (fun y' hy' => (hleaf y' hy').1)
        (fun y' hy' => Sparkle.Tests.Compiler.GateConeDesignTypedTest.childAdd_w8 (hleaf y' hy').2) cache' ids nd len)
    (Tools.ShippingGateParentRun.binders_pos_of_all rfl)
  refine ⟨M, envR, mF, y, hpost, hcache, tagR, hy, hobs, hA, hB, i0, i1, cache, ?_⟩
  intro aS bS T ins st0 mems kids hadm hR
  obtain ⟨envsO, hD, hlen, hob⟩ := H aS bS T ins st0 mems kids hadm hR
  exact ⟨⟨envsO, hD, hlen, hob⟩,
    Tools.ShippingGateDesignAll.gate_sv_all hg h1 h2 h3 h4 h5 h6 hDB hR hD
      (fun e => e.length = T ∧ ∀ (j : Nat) (hj : j < e.length),
        (e[j]'hj) "out" = ((wrapAdd aS bS).val j).toNat)
      ⟨hlen, hob⟩⟩

/-- **`parentNested` at the design level, EVERY closed run**: `parentNested_gate_designSVN3`
(existence) and every closed run from the same seeding and states has length
`T` and shows the source (`Tools.ShippingGateDesignAll.gate_sv_all`). Left:
`DesignSideR`. -/
theorem parentNested_gate_designSVall {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinational ``parentNested) mctx mref cctx cref w (b, design) w')
    (gdef : GateDefines mctx mref cctx cref ``parentNested parentNestedBinders
      Sparkle.Tests.Compiler.GateConeNestedTest.parentNestedBody)
    (bnd : ChildBnd mref cref w)
    (centry : EntryDefines mctx mref cctx cref ``childAdd childAddValue) :
    ∃ (M : Sparkle.IR.AST.Module) (envR : Lean.Environment) (mF : Std.HashMap Lean.Name Res)
      (y : Res),
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
        b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)) ∧
      CacheInv mref cref mF ∧
      Sparkle.Compiler.isHardwareModule envR ``childAdd = true ∧
      mF.get? ``childAdd = some y ∧ Sparkle.Tests.Compiler.GateConeNestedTest.ParentNestedObservesC (ownChild y) M ∧
      DesignHasChild design.modules y ∧ PostKeeps b M ∧
      (∃ (i0 i1 i2 : FVarId) (cache : IO.Ref (Lean.ExprStructMap String)),
        ∀ {D : DomainConfig} (aS bS : Signal D (BitVec 8)) (T : Nat)
          (ins : Nat → String → Nat) (st0 : String → Nat) (mems : MEnv)
          (kids : String → Tools.ShippingHierState.KidState),
          (∀ t st, t < T → ∃ (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n),
            Tools.ShippingMixedEntrySoundness.Admissible bools bits (seedIn b ins t st)
              (parentNestedBinders.zip [i0, i1, i2])
              (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
                (Sparkle.IR.ModuleName.ofDecl ``parentNested)) ∧
            (Tools.ShippingMixedEntrySoundness.prepare bools bits
              (parentNestedBinders.zip [i0, i1, i2])
              (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
                (Sparkle.IR.ModuleName.ofDecl ``parentNested))).bits i1 =
              some ⟨8, aS.val (T - 1 - t)⟩ ∧
            (Tools.ShippingMixedEntrySoundness.prepare bools bits
              (parentNestedBinders.zip [i0, i1, i2])
              (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
                (Sparkle.IR.ModuleName.ofDecl ``parentNested))).bits i2 =
              some ⟨8, bS.val (T - 1 - t)⟩) →
          Tools.ShippingGateCombSide.DesignSideR design.modules b ins st0 kids →
          (∃ envsO, Tools.ShippingDesignSV.DesignSV
              (Tools.ShippingMachineLinked.childMap design.modules) 0
              (Sparkle.IR.OptCheck.checkedOptimize b) (seedIn b ins) T ⟨st0, mems, kids⟩ envsO ∧
            envsO.length = T ∧
            ∀ (j : Nat) (hj : j < envsO.length),
              (envsO[j]'hj) "out" = ((parentNested aS bS).val j).toNat) ∧
          ∀ envs', Tools.ShippingDesignSV.DesignSV
              (Tools.ShippingMachineLinked.childMap design.modules) 0
              (Sparkle.IR.OptCheck.checkedOptimize b) (seedIn b ins) T ⟨st0, mems, kids⟩ envs' →
            envs'.length = T ∧
            ∀ (j : Nat) (hj : j < envs'.length),
              (envs'[j]'hj) "out" = ((parentNested aS bS).val j).toNat) := by
  obtain ⟨M, envR, mF, y, hpost, hcache, tagR, hy, hobs, hA, hB, i0, i1, i2, cache, H⟩ :=
    Sparkle.Tests.Compiler.GateConeDesignTypedTest.parentNested_gate_designSVN3 hr gdef bnd centry
  have hg : Sparkle.IR.RefineCheck.hierGate b = true := by
    obtain ⟨M', _, _, _, hpost', -, -, -, -, -, hmod'⟩ :=
      Sparkle.Tests.Compiler.GateConeDesignWalkTest.parentNested_gate_designA hr gdef bnd centry
    exact Tools.ShippingGateCombSide.hierGate_of_modOk hmod' hpost'
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := Tools.ShippingGateParentRun.gate_combFacts (c := ``childAdd)
    (n := 2) hr gdef bnd (Sparkle.Tests.Compiler.GateConeDesignNamesTest.childAdd_kidN centry (by decide))
    (fun envR' hacc mF' hleaf L' D' hD' cache' ids nd len =>
      Sparkle.Tests.Compiler.GateConeDesignNamesTest.parentNested_walk2 L' hD' (Sparkle.Tests.Compiler.GateConeNestedTest.parentNested_tag hacc) hleaf
        cache' ids nd len)
    (Tools.ShippingGateParentRun.binders_pos_of_all rfl)
  obtain ⟨-, hDB⟩ := Tools.ShippingGateParentRun.gate_typedFacts (c := ``childAdd) (n := 2)
    (fun _ => 8) hr gdef bnd (Sparkle.Tests.Compiler.GateConeDesignTypedTest.childAdd_kidT centry (by decide))
    (fun envR' hacc mF' hleaf L' D' hD' cache' ids nd len =>
      Sparkle.Tests.Compiler.GateConeDesignTypedTest.parentNested_walk3 L' hD' (Sparkle.Tests.Compiler.GateConeNestedTest.parentNested_tag hacc) (fun y' hy' => (hleaf y' hy').1)
        (fun y' hy' => Sparkle.Tests.Compiler.GateConeDesignTypedTest.childAdd_w8 (hleaf y' hy').2) cache' ids nd len)
    (Tools.ShippingGateParentRun.binders_pos_of_all rfl)
  refine ⟨M, envR, mF, y, hpost, hcache, tagR, hy, hobs, hA, hB, i0, i1, i2, cache, ?_⟩
  intro Dc aS bS T ins st0 mems kids hadm hR
  obtain ⟨envsO, hD, hlen, hob⟩ := H aS bS T ins st0 mems kids hadm hR
  exact ⟨⟨envsO, hD, hlen, hob⟩,
    Tools.ShippingGateDesignAll.gate_sv_all hg h1 h2 h3 h4 h5 h6 hDB hR hD
      (fun e => e.length = T ∧ ∀ (j : Nat) (hj : j < e.length),
        (e[j]'hj) "out" = ((parentNested aS bS).val j).toNat)
      ⟨hlen, hob⟩⟩

end svn3

end Sparkle.Tests.Compiler.GateConeDesignAllTest

#print axioms Sparkle.Tests.Compiler.GateConeDesignAllTest.parentMix_gate_designSVall
#print axioms Sparkle.Tests.Compiler.GateConeDesignAllTest.parentTwoCalls_gate_designSVall
#print axioms Sparkle.Tests.Compiler.GateConeDesignAllTest.parentRepeat_gate_designSVall
#print axioms Sparkle.Tests.Compiler.GateConeDesignAllTest.parentCmp_gate_designSVall
#print axioms Sparkle.Tests.Compiler.GateConeDesignAllTest.parentUse_gate_designSVall
#print axioms Sparkle.Tests.Compiler.GateConeDesignAllTest.wrapAdd_gate_designSVall
#print axioms Sparkle.Tests.Compiler.GateConeDesignAllTest.parentNested_gate_designSVall
