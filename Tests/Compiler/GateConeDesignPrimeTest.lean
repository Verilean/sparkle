import Tests.Compiler.GateConeDesignTest
import Tests.Compiler.GateConeDesignSixTest
import Tests.Compiler.GateConeDesignWalkTest
import Tools.ShippingGateDesignPost

/-! # The seven gate-route parents at the design level, WITHOUT obstacles (A) and (B) (worker N, round 11)

WRITTEN, NOT BUILT. TARGET-ONLY (`lake build Tests.Compiler.GateConeDesignPrimeTest`;
not in `Tests.AllTests`). GENERATED from the round-10 `…_gate_designSV`
statements (`Tests/Compiler/GateConeDesignTest.lean`,
`Tests/Compiler/GateConeDesignSixTest.lean`; the old theorems are kept):

* the antecedents (A) `DesignHasChild design.modules y` and (B)
  `PostKeeps b M` are REMOVED and CONCLUDED instead: (A) from the walk
  (`…_gate_designA`, `Tests/Compiler/GateConeDesignWalkTest.lean`), (B) from
  the walk's `ModOk` of the core module (`postKeeps_of_modOk`,
  `Tools/ShippingGateDesignPost.lean`);
* remaining antecedents of the design-level part: (C) `OptKeepsOut
  design.modules b "out"` (the optimizer keeps `out`; the no-`rst` refine
  bridge — another worker's scope) and `DesignSide` (the decidable design
  checks and width bounds, as in the machine route's non-closed form).

Premises: exactly those of `…_gate_cone_runK'` (the run, `GateDefines` NOT
ALLOWED, `ChildBnd`, `EntryDefines childAdd`). Uniqueness (every closed run
shows the source) NOT concluded. -/
namespace Sparkle.Tests.Compiler.GateConeDesignPrimeTest
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

/-- **`parentMix` at the design level, (A) and (B) discharged**: the
round-10 statement with `DesignHasChild` and `PostKeeps` concluded; antecedents
left: (C) `OptKeepsOut` and `DesignSide`. -/
theorem parentMix_gate_designSV' {mctx : Lean.Meta.Context}
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
      (OptKeepsOut design.modules b "out" →
        ∃ (i0 i1 i2 : FVarId) (cache : IO.Ref (Lean.ExprStructMap String)),
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
          DesignSide design.modules b ins st0 kids →
          ∃ envsO, Tools.ShippingDesignSV.DesignSV
              (Tools.ShippingMachineLinked.childMap design.modules) 0
              (Sparkle.IR.OptCheck.checkedOptimize b) (seedIn b ins) T ⟨st0, mems, kids⟩ envsO ∧
            envsO.length = T ∧
            ∀ (j : Nat) (hj : j < envsO.length),
              (envsO[j]'hj) "out" = ((parentMix aS bS).val j).toNat) := by
  obtain ⟨M, envR, mF, y, hpost, hcache, tagR, hy, hobs, hA, hmod⟩ :=
    Sparkle.Tests.Compiler.GateConeDesignWalkTest.parentMix_gate_designA hr gdef bnd centry
  have hB : PostKeeps b M := Tools.ShippingGateDesignPost.postKeeps_of_modOk hmod hpost
  refine ⟨M, envR, mF, y, hpost, hcache, tagR, hy, hobs, hA, hB, ?_⟩
  intro hC
  obtain ⟨i0, i1, i2, cache, H⟩ := hobs
  refine ⟨i0, i1, i2, cache, ?_⟩
  intro D aS bS T ins st0 mems kids hin hside
  exact gate_designSV_of_steps hA hB hC
    (G := fun s => ((parentMix aS bS).val s).toNat)
    (fun k st mems' hk => by
      obtain ⟨bools, bits, adm, ha, hb⟩ := hin k st hk
      obtain ⟨⟨result, hev, hout⟩, hlink⟩ :=
        H bools bits (seedIn b ins k st) aS bS (T - 1 - k) mems' adm ha hb
      exact ⟨result, hev, hout, hlink⟩)
    hside

/-- **`parentUse` at the design level, (A) and (B) discharged**: the
round-10 statement with `DesignHasChild` and `PostKeeps` concluded; antecedents
left: (C) `OptKeepsOut` and `DesignSide`. -/
theorem parentUse_gate_designSV' {mctx : Lean.Meta.Context}
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
      (OptKeepsOut design.modules b "out" →
        ∃ (i0 i1 i2 : FVarId) (cache : IO.Ref (Lean.ExprStructMap String)),
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
          DesignSide design.modules b ins st0 kids →
          ∃ envsO, Tools.ShippingDesignSV.DesignSV
              (Tools.ShippingMachineLinked.childMap design.modules) 0
              (Sparkle.IR.OptCheck.checkedOptimize b) (seedIn b ins) T ⟨st0, mems, kids⟩ envsO ∧
            envsO.length = T ∧
            ∀ (j : Nat) (hj : j < envsO.length),
              (envsO[j]'hj) "out" = ((parentUse aS bS).val j).toNat) := by
  obtain ⟨M, envR, mF, y, hpost, hcache, tagR, hy, hobs, hA, hmod⟩ :=
    Sparkle.Tests.Compiler.GateConeDesignWalkTest.parentUse_gate_designA hr gdef bnd centry
  have hB : PostKeeps b M := Tools.ShippingGateDesignPost.postKeeps_of_modOk hmod hpost
  refine ⟨M, envR, mF, y, hpost, hcache, tagR, hy, hobs, hA, hB, ?_⟩
  intro hC
  obtain ⟨i0, i1, i2, cache, H⟩ := hobs
  refine ⟨i0, i1, i2, cache, ?_⟩
  intro D aS bS T ins st0 mems kids hin hside
  exact gate_designSV_of_steps hA hB hC
    (G := fun s => ((parentUse aS bS).val s).toNat)
    (fun k st mems' hk => by
      obtain ⟨bools, bits, adm, ha, hb⟩ := hin k st hk
      obtain ⟨⟨result, hev, hout⟩, hlink⟩ :=
        H bools bits (seedIn b ins k st) aS bS (T - 1 - k) mems' adm ha hb
      exact ⟨result, hev, hout, hlink⟩)
    hside

/-- **`wrapAdd` at the design level, (A) and (B) discharged**: the
round-10 statement with `DesignHasChild` and `PostKeeps` concluded; antecedents
left: (C) `OptKeepsOut` and `DesignSide`. -/
theorem wrapAdd_gate_designSV' {mctx : Lean.Meta.Context}
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
      (OptKeepsOut design.modules b "out" →
        ∃ (i0 i1 : FVarId) (cache : IO.Ref (Lean.ExprStructMap String)),
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
          DesignSide design.modules b ins st0 kids →
          ∃ envsO, Tools.ShippingDesignSV.DesignSV
              (Tools.ShippingMachineLinked.childMap design.modules) 0
              (Sparkle.IR.OptCheck.checkedOptimize b) (seedIn b ins) T ⟨st0, mems, kids⟩ envsO ∧
            envsO.length = T ∧
            ∀ (j : Nat) (hj : j < envsO.length),
              (envsO[j]'hj) "out" = ((wrapAdd aS bS).val j).toNat) := by
  obtain ⟨M, envR, mF, y, hpost, hcache, tagR, hy, hobs, hA, hmod⟩ :=
    Sparkle.Tests.Compiler.GateConeDesignWalkTest.wrapAdd_gate_designA hr gdef bnd centry
  have hB : PostKeeps b M := Tools.ShippingGateDesignPost.postKeeps_of_modOk hmod hpost
  refine ⟨M, envR, mF, y, hpost, hcache, tagR, hy, hobs, hA, hB, ?_⟩
  intro hC
  obtain ⟨i0, i1, cache, H⟩ := hobs
  refine ⟨i0, i1, cache, ?_⟩
  intro aS bS T ins st0 mems kids hin hside
  exact gate_designSV_of_steps hA hB hC
    (G := fun s => ((wrapAdd aS bS).val s).toNat)
    (fun k st mems' hk => by
      obtain ⟨bools, bits, adm, ha, hb⟩ := hin k st hk
      obtain ⟨⟨result, hev, hout⟩, hlink⟩ :=
        H bools bits (seedIn b ins k st) aS bS (T - 1 - k) mems' adm ha hb
      exact ⟨result, hev, hout, hlink⟩)
    hside

/-- **`parentTwoCalls` at the design level, (A) and (B) discharged**: the
round-10 statement with `DesignHasChild` and `PostKeeps` concluded; antecedents
left: (C) `OptKeepsOut` and `DesignSide`. -/
theorem parentTwoCalls_gate_designSV' {mctx : Lean.Meta.Context}
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
      (OptKeepsOut design.modules b "out" →
        ∃ (i0 i1 i2 : FVarId) (cache : IO.Ref (Lean.ExprStructMap String)),
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
          DesignSide design.modules b ins st0 kids →
          ∃ envsO, Tools.ShippingDesignSV.DesignSV
              (Tools.ShippingMachineLinked.childMap design.modules) 0
              (Sparkle.IR.OptCheck.checkedOptimize b) (seedIn b ins) T ⟨st0, mems, kids⟩ envsO ∧
            envsO.length = T ∧
            ∀ (j : Nat) (hj : j < envsO.length),
              (envsO[j]'hj) "out" = ((parentTwoCalls aS bS).val j).toNat) := by
  obtain ⟨M, envR, mF, y, hpost, hcache, tagR, hy, hobs, hA, hmod⟩ :=
    Sparkle.Tests.Compiler.GateConeDesignWalkTest.parentTwoCalls_gate_designA hr gdef bnd centry
  have hB : PostKeeps b M := Tools.ShippingGateDesignPost.postKeeps_of_modOk hmod hpost
  refine ⟨M, envR, mF, y, hpost, hcache, tagR, hy, hobs, hA, hB, ?_⟩
  intro hC
  obtain ⟨i0, i1, i2, cache, H⟩ := hobs
  refine ⟨i0, i1, i2, cache, ?_⟩
  intro D aS bS T ins st0 mems kids hin hside
  exact gate_designSV_of_steps hA hB hC
    (G := fun s => ((parentTwoCalls aS bS).val s).toNat)
    (fun k st mems' hk => by
      obtain ⟨bools, bits, adm, ha, hb⟩ := hin k st hk
      obtain ⟨⟨result, hev, hout⟩, hlink⟩ :=
        H bools bits (seedIn b ins k st) aS bS (T - 1 - k) mems' adm ha hb
      exact ⟨result, hev, hout, hlink⟩)
    hside

/-- **`parentRepeat` at the design level, (A) and (B) discharged**: the
round-10 statement with `DesignHasChild` and `PostKeeps` concluded; antecedents
left: (C) `OptKeepsOut` and `DesignSide`. -/
theorem parentRepeat_gate_designSV' {mctx : Lean.Meta.Context}
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
      (OptKeepsOut design.modules b "out" →
        ∃ (i0 i1 i2 : FVarId) (cache : IO.Ref (Lean.ExprStructMap String)),
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
          DesignSide design.modules b ins st0 kids →
          ∃ envsO, Tools.ShippingDesignSV.DesignSV
              (Tools.ShippingMachineLinked.childMap design.modules) 0
              (Sparkle.IR.OptCheck.checkedOptimize b) (seedIn b ins) T ⟨st0, mems, kids⟩ envsO ∧
            envsO.length = T ∧
            ∀ (j : Nat) (hj : j < envsO.length),
              (envsO[j]'hj) "out" = ((parentRepeat aS bS).val j).toNat) := by
  obtain ⟨M, envR, mF, y, hpost, hcache, tagR, hy, hobs, hA, hmod⟩ :=
    Sparkle.Tests.Compiler.GateConeDesignWalkTest.parentRepeat_gate_designA hr gdef bnd centry
  have hB : PostKeeps b M := Tools.ShippingGateDesignPost.postKeeps_of_modOk hmod hpost
  refine ⟨M, envR, mF, y, hpost, hcache, tagR, hy, hobs, hA, hB, ?_⟩
  intro hC
  obtain ⟨i0, i1, i2, cache, H⟩ := hobs
  refine ⟨i0, i1, i2, cache, ?_⟩
  intro D aS bS T ins st0 mems kids hin hside
  exact gate_designSV_of_steps hA hB hC
    (G := fun s => ((parentRepeat aS bS).val s).toNat)
    (fun k st mems' hk => by
      obtain ⟨bools, bits, adm, ha, hb⟩ := hin k st hk
      obtain ⟨⟨result, hev, hout⟩, hlink⟩ :=
        H bools bits (seedIn b ins k st) aS bS (T - 1 - k) mems' adm ha hb
      exact ⟨result, hev, hout, hlink⟩)
    hside

/-- **`parentCmp` at the design level, (A) and (B) discharged**: the
round-10 statement with `DesignHasChild` and `PostKeeps` concluded; antecedents
left: (C) `OptKeepsOut` and `DesignSide`. -/
theorem parentCmp_gate_designSV' {mctx : Lean.Meta.Context}
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
      (OptKeepsOut design.modules b "out" →
        ∃ (i0 i1 i2 : FVarId) (cache : IO.Ref (Lean.ExprStructMap String)),
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
          DesignSide design.modules b ins st0 kids →
          ∃ envsO, Tools.ShippingDesignSV.DesignSV
              (Tools.ShippingMachineLinked.childMap design.modules) 0
              (Sparkle.IR.OptCheck.checkedOptimize b) (seedIn b ins) T ⟨st0, mems, kids⟩ envsO ∧
            envsO.length = T ∧
            ∀ (j : Nat) (hj : j < envsO.length),
              (envsO[j]'hj) "out" = Tools.ShippingMuxLoweringSoundness.encodeBool ((parentCmp aS bS).val j)) := by
  obtain ⟨M, envR, mF, y, hpost, hcache, tagR, hy, hobs, hA, hmod⟩ :=
    Sparkle.Tests.Compiler.GateConeDesignWalkTest.parentCmp_gate_designA hr gdef bnd centry
  have hB : PostKeeps b M := Tools.ShippingGateDesignPost.postKeeps_of_modOk hmod hpost
  refine ⟨M, envR, mF, y, hpost, hcache, tagR, hy, hobs, hA, hB, ?_⟩
  intro hC
  obtain ⟨i0, i1, i2, cache, H⟩ := hobs
  refine ⟨i0, i1, i2, cache, ?_⟩
  intro D aS bS T ins st0 mems kids hin hside
  exact gate_designSV_of_steps hA hB hC
    (G := fun s => Tools.ShippingMuxLoweringSoundness.encodeBool ((parentCmp aS bS).val s))
    (fun k st mems' hk => by
      obtain ⟨bools, bits, adm, ha, hb⟩ := hin k st hk
      obtain ⟨⟨result, hev, hout⟩, hlink⟩ :=
        H bools bits (seedIn b ins k st) aS bS (T - 1 - k) mems' adm ha hb
      exact ⟨result, hev, hout, hlink⟩)
    hside

/-- **`parentNested` at the design level, (A) and (B) discharged**: the
round-10 statement with `DesignHasChild` and `PostKeeps` concluded; antecedents
left: (C) `OptKeepsOut` and `DesignSide`. -/
theorem parentNested_gate_designSV' {mctx : Lean.Meta.Context}
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
      (OptKeepsOut design.modules b "out" →
        ∃ (i0 i1 i2 : FVarId) (cache : IO.Ref (Lean.ExprStructMap String)),
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
          DesignSide design.modules b ins st0 kids →
          ∃ envsO, Tools.ShippingDesignSV.DesignSV
              (Tools.ShippingMachineLinked.childMap design.modules) 0
              (Sparkle.IR.OptCheck.checkedOptimize b) (seedIn b ins) T ⟨st0, mems, kids⟩ envsO ∧
            envsO.length = T ∧
            ∀ (j : Nat) (hj : j < envsO.length),
              (envsO[j]'hj) "out" = ((parentNested aS bS).val j).toNat) := by
  obtain ⟨M, envR, mF, y, hpost, hcache, tagR, hy, hobs, hA, hmod⟩ :=
    Sparkle.Tests.Compiler.GateConeDesignWalkTest.parentNested_gate_designA hr gdef bnd centry
  have hB : PostKeeps b M := Tools.ShippingGateDesignPost.postKeeps_of_modOk hmod hpost
  refine ⟨M, envR, mF, y, hpost, hcache, tagR, hy, hobs, hA, hB, ?_⟩
  intro hC
  obtain ⟨i0, i1, i2, cache, H⟩ := hobs
  refine ⟨i0, i1, i2, cache, ?_⟩
  intro D aS bS T ins st0 mems kids hin hside
  exact gate_designSV_of_steps hA hB hC
    (G := fun s => ((parentNested aS bS).val s).toNat)
    (fun k st mems' hk => by
      obtain ⟨bools, bits, adm, ha, hb⟩ := hin k st hk
      obtain ⟨⟨result, hev, hout⟩, hlink⟩ :=
        H bools bits (seedIn b ins k st) aS bS (T - 1 - k) mems' adm ha hb
      exact ⟨result, hev, hout, hlink⟩)
    hside

end Sparkle.Tests.Compiler.GateConeDesignPrimeTest

#print axioms Sparkle.Tests.Compiler.GateConeDesignPrimeTest.parentMix_gate_designSV'
#print axioms Sparkle.Tests.Compiler.GateConeDesignPrimeTest.parentUse_gate_designSV'
#print axioms Sparkle.Tests.Compiler.GateConeDesignPrimeTest.wrapAdd_gate_designSV'
#print axioms Sparkle.Tests.Compiler.GateConeDesignPrimeTest.parentTwoCalls_gate_designSV'
#print axioms Sparkle.Tests.Compiler.GateConeDesignPrimeTest.parentRepeat_gate_designSV'
#print axioms Sparkle.Tests.Compiler.GateConeDesignPrimeTest.parentCmp_gate_designSV'
#print axioms Sparkle.Tests.Compiler.GateConeDesignPrimeTest.parentNested_gate_designSV'
