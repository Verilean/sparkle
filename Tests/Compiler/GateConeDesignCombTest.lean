import Tests.Compiler.GateConeDesignPrimeTest
import Tools.ShippingGateOutPort
import Tools.ShippingGateCombSide

/-! # The seven gate-route parents at the design level: (C) wired, checker bundles narrowed (worker N, round 12)

WRITTEN, NOT BUILT. TARGET-ONLY (`lake build Tests.Compiler.GateConeDesignCombTest`;
not in `Tests.AllTests`). GENERATED (a script over the round-11
`…_gate_designSV'` statements of `Tests/Compiler/GateConeDesignPrimeTest.lean`;
the old theorems are kept).

* `…_gate_designSV''`: the antecedent (C) `OptKeepsOut design.modules b "out"`
  is REMOVED: `Tools.ShippingGateOptComb.optKeepsOut_comb_post` from (B)
  `PostKeeps` (concluded) and `combOptSide design.modules b = true`, with
  `"out" ∈ b.outputs.map (·.name)` from the run
  (`Tools.ShippingGateOutPort.gate_out_port`). Antecedents left:
  `combOptSide` and `DesignSide`.
* `…_gate_designSVN`: the same with `combOptSide` narrowed to
  `combSideB design.modules b` (six facts of `b`) and `DesignSide` to
  `designSideB design.modules b` (two emitted-text conjuncts of `b`,
  `portsMatchB` of the shipped module, the children's leaf check) and
  `DesignSideR` (inputs fit, start state bounds, children's start states:
  the run-level width premises). Derived: `hierGate b` (walk: `ModOk` and
  `PostKeeps`), the four shipped-module conjuncts of `combOptSide`,
  `kidsComb` of the shipped body and six of the eight `textCheckI` conjuncts
  of `designCheck` (`Tools/ShippingGateCombSide.lean`).

Premises of both families: exactly those of `…_gate_cone_runK'` (the run,
`GateDefines` NOT ALLOWED, `ChildBnd`, `EntryDefines childAdd`). The
antecedents are checker-style conditions OUTSIDE ALLOWED. Uniqueness (every
closed run shows the source) NOT concluded. -/
namespace Sparkle.Tests.Compiler.GateConeDesignCombTest
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

/-- **`parentMix` at the design level, (C) wired**: `parentMix_gate_designSV'` with
`OptKeepsOut` replaced by `combOptSide` (`optKeepsOut_comb_post`, `out` an output
port by `gate_out_port`); antecedents left: `combOptSide` and `DesignSide`. -/
theorem parentMix_gate_designSV'' {mctx : Lean.Meta.Context}
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
      (Tools.ShippingGateOptComb.combOptSide design.modules b = true →
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
  obtain ⟨M, envR, mF, y, hpost, hcache, tagR, hy, hobs, hA, hB, hD⟩ :=
    Sparkle.Tests.Compiler.GateConeDesignPrimeTest.parentMix_gate_designSV' hr gdef bnd centry
  have hout := Tools.ShippingGateOutPort.gate_out_port hr gdef bnd
  exact ⟨M, envR, mF, y, hpost, hcache, tagR, hy, hobs, hA, hB,
    fun hside => hD (Tools.ShippingGateOptComb.optKeepsOut_comb_post hB hside hout)⟩

/-- **`parentUse` at the design level, (C) wired**: `parentUse_gate_designSV'` with
`OptKeepsOut` replaced by `combOptSide` (`optKeepsOut_comb_post`, `out` an output
port by `gate_out_port`); antecedents left: `combOptSide` and `DesignSide`. -/
theorem parentUse_gate_designSV'' {mctx : Lean.Meta.Context}
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
      (Tools.ShippingGateOptComb.combOptSide design.modules b = true →
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
  obtain ⟨M, envR, mF, y, hpost, hcache, tagR, hy, hobs, hA, hB, hD⟩ :=
    Sparkle.Tests.Compiler.GateConeDesignPrimeTest.parentUse_gate_designSV' hr gdef bnd centry
  have hout := Tools.ShippingGateOutPort.gate_out_port hr gdef bnd
  exact ⟨M, envR, mF, y, hpost, hcache, tagR, hy, hobs, hA, hB,
    fun hside => hD (Tools.ShippingGateOptComb.optKeepsOut_comb_post hB hside hout)⟩

/-- **`wrapAdd` at the design level, (C) wired**: `wrapAdd_gate_designSV'` with
`OptKeepsOut` replaced by `combOptSide` (`optKeepsOut_comb_post`, `out` an output
port by `gate_out_port`); antecedents left: `combOptSide` and `DesignSide`. -/
theorem wrapAdd_gate_designSV'' {mctx : Lean.Meta.Context}
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
      (Tools.ShippingGateOptComb.combOptSide design.modules b = true →
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
  obtain ⟨M, envR, mF, y, hpost, hcache, tagR, hy, hobs, hA, hB, hD⟩ :=
    Sparkle.Tests.Compiler.GateConeDesignPrimeTest.wrapAdd_gate_designSV' hr gdef bnd centry
  have hout := Tools.ShippingGateOutPort.gate_out_port hr gdef bnd
  exact ⟨M, envR, mF, y, hpost, hcache, tagR, hy, hobs, hA, hB,
    fun hside => hD (Tools.ShippingGateOptComb.optKeepsOut_comb_post hB hside hout)⟩

/-- **`parentTwoCalls` at the design level, (C) wired**: `parentTwoCalls_gate_designSV'` with
`OptKeepsOut` replaced by `combOptSide` (`optKeepsOut_comb_post`, `out` an output
port by `gate_out_port`); antecedents left: `combOptSide` and `DesignSide`. -/
theorem parentTwoCalls_gate_designSV'' {mctx : Lean.Meta.Context}
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
      (Tools.ShippingGateOptComb.combOptSide design.modules b = true →
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
  obtain ⟨M, envR, mF, y, hpost, hcache, tagR, hy, hobs, hA, hB, hD⟩ :=
    Sparkle.Tests.Compiler.GateConeDesignPrimeTest.parentTwoCalls_gate_designSV' hr gdef bnd centry
  have hout := Tools.ShippingGateOutPort.gate_out_port hr gdef bnd
  exact ⟨M, envR, mF, y, hpost, hcache, tagR, hy, hobs, hA, hB,
    fun hside => hD (Tools.ShippingGateOptComb.optKeepsOut_comb_post hB hside hout)⟩

/-- **`parentRepeat` at the design level, (C) wired**: `parentRepeat_gate_designSV'` with
`OptKeepsOut` replaced by `combOptSide` (`optKeepsOut_comb_post`, `out` an output
port by `gate_out_port`); antecedents left: `combOptSide` and `DesignSide`. -/
theorem parentRepeat_gate_designSV'' {mctx : Lean.Meta.Context}
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
      (Tools.ShippingGateOptComb.combOptSide design.modules b = true →
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
  obtain ⟨M, envR, mF, y, hpost, hcache, tagR, hy, hobs, hA, hB, hD⟩ :=
    Sparkle.Tests.Compiler.GateConeDesignPrimeTest.parentRepeat_gate_designSV' hr gdef bnd centry
  have hout := Tools.ShippingGateOutPort.gate_out_port hr gdef bnd
  exact ⟨M, envR, mF, y, hpost, hcache, tagR, hy, hobs, hA, hB,
    fun hside => hD (Tools.ShippingGateOptComb.optKeepsOut_comb_post hB hside hout)⟩

/-- **`parentCmp` at the design level, (C) wired**: `parentCmp_gate_designSV'` with
`OptKeepsOut` replaced by `combOptSide` (`optKeepsOut_comb_post`, `out` an output
port by `gate_out_port`); antecedents left: `combOptSide` and `DesignSide`. -/
theorem parentCmp_gate_designSV'' {mctx : Lean.Meta.Context}
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
      (Tools.ShippingGateOptComb.combOptSide design.modules b = true →
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
  obtain ⟨M, envR, mF, y, hpost, hcache, tagR, hy, hobs, hA, hB, hD⟩ :=
    Sparkle.Tests.Compiler.GateConeDesignPrimeTest.parentCmp_gate_designSV' hr gdef bnd centry
  have hout := Tools.ShippingGateOutPort.gate_out_port hr gdef bnd
  exact ⟨M, envR, mF, y, hpost, hcache, tagR, hy, hobs, hA, hB,
    fun hside => hD (Tools.ShippingGateOptComb.optKeepsOut_comb_post hB hside hout)⟩

/-- **`parentNested` at the design level, (C) wired**: `parentNested_gate_designSV'` with
`OptKeepsOut` replaced by `combOptSide` (`optKeepsOut_comb_post`, `out` an output
port by `gate_out_port`); antecedents left: `combOptSide` and `DesignSide`. -/
theorem parentNested_gate_designSV'' {mctx : Lean.Meta.Context}
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
      (Tools.ShippingGateOptComb.combOptSide design.modules b = true →
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
  obtain ⟨M, envR, mF, y, hpost, hcache, tagR, hy, hobs, hA, hB, hD⟩ :=
    Sparkle.Tests.Compiler.GateConeDesignPrimeTest.parentNested_gate_designSV' hr gdef bnd centry
  have hout := Tools.ShippingGateOutPort.gate_out_port hr gdef bnd
  exact ⟨M, envR, mF, y, hpost, hcache, tagR, hy, hobs, hA, hB,
    fun hside => hD (Tools.ShippingGateOptComb.optKeepsOut_comb_post hB hside hout)⟩

/-- **`parentMix` at the design level, checker bundles narrowed**: `parentMix_gate_designSV''`
with `combOptSide` narrowed to `combSideB` (six facts of `b`) and `DesignSide` to
`designSideB` (four checks) and `DesignSideR` (the width premises); `hierGate b` and
the shipped module's facts derived (`Tools.ShippingGateCombSide`). -/
theorem parentMix_gate_designSVN {mctx : Lean.Meta.Context}
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
      (Tools.ShippingGateCombSide.combSideB design.modules b = true →
        Tools.ShippingGateCombSide.designSideB design.modules b = true →
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
          Tools.ShippingGateCombSide.DesignSideR design.modules b ins st0 kids →
          ∃ envsO, Tools.ShippingDesignSV.DesignSV
              (Tools.ShippingMachineLinked.childMap design.modules) 0
              (Sparkle.IR.OptCheck.checkedOptimize b) (seedIn b ins) T ⟨st0, mems, kids⟩ envsO ∧
            envsO.length = T ∧
            ∀ (j : Nat) (hj : j < envsO.length),
              (envsO[j]'hj) "out" = ((parentMix aS bS).val j).toNat) := by
  obtain ⟨M, envR, mF, y, hpost, hcache, tagR, hy, hobs, hA, hB, hD⟩ :=
    parentMix_gate_designSV'' hr gdef bnd centry
  have hg : Sparkle.IR.RefineCheck.hierGate b = true := by
    obtain ⟨M', _, _, _, hpost', -, -, -, -, -, hmod'⟩ :=
      Sparkle.Tests.Compiler.GateConeDesignWalkTest.parentMix_gate_designA hr gdef bnd centry
    exact Tools.ShippingGateCombSide.hierGate_of_modOk hmod' hpost'
  refine ⟨M, envR, mF, y, hpost, hcache, tagR, hy, hobs, hA, hB, ?_⟩
  intro hSB hDB
  obtain ⟨i0, i1, i2, cache, H⟩ := hD (Tools.ShippingGateCombSide.combOptSide_of_B hg hSB)
  refine ⟨i0, i1, i2, cache, ?_⟩
  intro D aS bS T ins st0 mems kids hin hR
  exact H aS bS T ins st0 mems kids hin
    (Tools.ShippingGateCombSide.designSide_of_R hg hSB hDB hR)

/-- **`parentUse` at the design level, checker bundles narrowed**: `parentUse_gate_designSV''`
with `combOptSide` narrowed to `combSideB` (six facts of `b`) and `DesignSide` to
`designSideB` (four checks) and `DesignSideR` (the width premises); `hierGate b` and
the shipped module's facts derived (`Tools.ShippingGateCombSide`). -/
theorem parentUse_gate_designSVN {mctx : Lean.Meta.Context}
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
      (Tools.ShippingGateCombSide.combSideB design.modules b = true →
        Tools.ShippingGateCombSide.designSideB design.modules b = true →
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
          Tools.ShippingGateCombSide.DesignSideR design.modules b ins st0 kids →
          ∃ envsO, Tools.ShippingDesignSV.DesignSV
              (Tools.ShippingMachineLinked.childMap design.modules) 0
              (Sparkle.IR.OptCheck.checkedOptimize b) (seedIn b ins) T ⟨st0, mems, kids⟩ envsO ∧
            envsO.length = T ∧
            ∀ (j : Nat) (hj : j < envsO.length),
              (envsO[j]'hj) "out" = ((parentUse aS bS).val j).toNat) := by
  obtain ⟨M, envR, mF, y, hpost, hcache, tagR, hy, hobs, hA, hB, hD⟩ :=
    parentUse_gate_designSV'' hr gdef bnd centry
  have hg : Sparkle.IR.RefineCheck.hierGate b = true := by
    obtain ⟨M', _, _, _, hpost', -, -, -, -, -, hmod'⟩ :=
      Sparkle.Tests.Compiler.GateConeDesignWalkTest.parentUse_gate_designA hr gdef bnd centry
    exact Tools.ShippingGateCombSide.hierGate_of_modOk hmod' hpost'
  refine ⟨M, envR, mF, y, hpost, hcache, tagR, hy, hobs, hA, hB, ?_⟩
  intro hSB hDB
  obtain ⟨i0, i1, i2, cache, H⟩ := hD (Tools.ShippingGateCombSide.combOptSide_of_B hg hSB)
  refine ⟨i0, i1, i2, cache, ?_⟩
  intro D aS bS T ins st0 mems kids hin hR
  exact H aS bS T ins st0 mems kids hin
    (Tools.ShippingGateCombSide.designSide_of_R hg hSB hDB hR)

/-- **`wrapAdd` at the design level, checker bundles narrowed**: `wrapAdd_gate_designSV''`
with `combOptSide` narrowed to `combSideB` (six facts of `b`) and `DesignSide` to
`designSideB` (four checks) and `DesignSideR` (the width premises); `hierGate b` and
the shipped module's facts derived (`Tools.ShippingGateCombSide`). -/
theorem wrapAdd_gate_designSVN {mctx : Lean.Meta.Context}
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
      (Tools.ShippingGateCombSide.combSideB design.modules b = true →
        Tools.ShippingGateCombSide.designSideB design.modules b = true →
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
          Tools.ShippingGateCombSide.DesignSideR design.modules b ins st0 kids →
          ∃ envsO, Tools.ShippingDesignSV.DesignSV
              (Tools.ShippingMachineLinked.childMap design.modules) 0
              (Sparkle.IR.OptCheck.checkedOptimize b) (seedIn b ins) T ⟨st0, mems, kids⟩ envsO ∧
            envsO.length = T ∧
            ∀ (j : Nat) (hj : j < envsO.length),
              (envsO[j]'hj) "out" = ((wrapAdd aS bS).val j).toNat) := by
  obtain ⟨M, envR, mF, y, hpost, hcache, tagR, hy, hobs, hA, hB, hD⟩ :=
    wrapAdd_gate_designSV'' hr gdef bnd centry
  have hg : Sparkle.IR.RefineCheck.hierGate b = true := by
    obtain ⟨M', _, _, _, hpost', -, -, -, -, -, hmod'⟩ :=
      Sparkle.Tests.Compiler.GateConeDesignWalkTest.wrapAdd_gate_designA hr gdef bnd centry
    exact Tools.ShippingGateCombSide.hierGate_of_modOk hmod' hpost'
  refine ⟨M, envR, mF, y, hpost, hcache, tagR, hy, hobs, hA, hB, ?_⟩
  intro hSB hDB
  obtain ⟨i0, i1, cache, H⟩ := hD (Tools.ShippingGateCombSide.combOptSide_of_B hg hSB)
  refine ⟨i0, i1, cache, ?_⟩
  intro aS bS T ins st0 mems kids hin hR
  exact H aS bS T ins st0 mems kids hin
    (Tools.ShippingGateCombSide.designSide_of_R hg hSB hDB hR)

/-- **`parentTwoCalls` at the design level, checker bundles narrowed**: `parentTwoCalls_gate_designSV''`
with `combOptSide` narrowed to `combSideB` (six facts of `b`) and `DesignSide` to
`designSideB` (four checks) and `DesignSideR` (the width premises); `hierGate b` and
the shipped module's facts derived (`Tools.ShippingGateCombSide`). -/
theorem parentTwoCalls_gate_designSVN {mctx : Lean.Meta.Context}
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
      (Tools.ShippingGateCombSide.combSideB design.modules b = true →
        Tools.ShippingGateCombSide.designSideB design.modules b = true →
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
          Tools.ShippingGateCombSide.DesignSideR design.modules b ins st0 kids →
          ∃ envsO, Tools.ShippingDesignSV.DesignSV
              (Tools.ShippingMachineLinked.childMap design.modules) 0
              (Sparkle.IR.OptCheck.checkedOptimize b) (seedIn b ins) T ⟨st0, mems, kids⟩ envsO ∧
            envsO.length = T ∧
            ∀ (j : Nat) (hj : j < envsO.length),
              (envsO[j]'hj) "out" = ((parentTwoCalls aS bS).val j).toNat) := by
  obtain ⟨M, envR, mF, y, hpost, hcache, tagR, hy, hobs, hA, hB, hD⟩ :=
    parentTwoCalls_gate_designSV'' hr gdef bnd centry
  have hg : Sparkle.IR.RefineCheck.hierGate b = true := by
    obtain ⟨M', _, _, _, hpost', -, -, -, -, -, hmod'⟩ :=
      Sparkle.Tests.Compiler.GateConeDesignWalkTest.parentTwoCalls_gate_designA hr gdef bnd centry
    exact Tools.ShippingGateCombSide.hierGate_of_modOk hmod' hpost'
  refine ⟨M, envR, mF, y, hpost, hcache, tagR, hy, hobs, hA, hB, ?_⟩
  intro hSB hDB
  obtain ⟨i0, i1, i2, cache, H⟩ := hD (Tools.ShippingGateCombSide.combOptSide_of_B hg hSB)
  refine ⟨i0, i1, i2, cache, ?_⟩
  intro D aS bS T ins st0 mems kids hin hR
  exact H aS bS T ins st0 mems kids hin
    (Tools.ShippingGateCombSide.designSide_of_R hg hSB hDB hR)

/-- **`parentRepeat` at the design level, checker bundles narrowed**: `parentRepeat_gate_designSV''`
with `combOptSide` narrowed to `combSideB` (six facts of `b`) and `DesignSide` to
`designSideB` (four checks) and `DesignSideR` (the width premises); `hierGate b` and
the shipped module's facts derived (`Tools.ShippingGateCombSide`). -/
theorem parentRepeat_gate_designSVN {mctx : Lean.Meta.Context}
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
      (Tools.ShippingGateCombSide.combSideB design.modules b = true →
        Tools.ShippingGateCombSide.designSideB design.modules b = true →
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
          Tools.ShippingGateCombSide.DesignSideR design.modules b ins st0 kids →
          ∃ envsO, Tools.ShippingDesignSV.DesignSV
              (Tools.ShippingMachineLinked.childMap design.modules) 0
              (Sparkle.IR.OptCheck.checkedOptimize b) (seedIn b ins) T ⟨st0, mems, kids⟩ envsO ∧
            envsO.length = T ∧
            ∀ (j : Nat) (hj : j < envsO.length),
              (envsO[j]'hj) "out" = ((parentRepeat aS bS).val j).toNat) := by
  obtain ⟨M, envR, mF, y, hpost, hcache, tagR, hy, hobs, hA, hB, hD⟩ :=
    parentRepeat_gate_designSV'' hr gdef bnd centry
  have hg : Sparkle.IR.RefineCheck.hierGate b = true := by
    obtain ⟨M', _, _, _, hpost', -, -, -, -, -, hmod'⟩ :=
      Sparkle.Tests.Compiler.GateConeDesignWalkTest.parentRepeat_gate_designA hr gdef bnd centry
    exact Tools.ShippingGateCombSide.hierGate_of_modOk hmod' hpost'
  refine ⟨M, envR, mF, y, hpost, hcache, tagR, hy, hobs, hA, hB, ?_⟩
  intro hSB hDB
  obtain ⟨i0, i1, i2, cache, H⟩ := hD (Tools.ShippingGateCombSide.combOptSide_of_B hg hSB)
  refine ⟨i0, i1, i2, cache, ?_⟩
  intro D aS bS T ins st0 mems kids hin hR
  exact H aS bS T ins st0 mems kids hin
    (Tools.ShippingGateCombSide.designSide_of_R hg hSB hDB hR)

/-- **`parentCmp` at the design level, checker bundles narrowed**: `parentCmp_gate_designSV''`
with `combOptSide` narrowed to `combSideB` (six facts of `b`) and `DesignSide` to
`designSideB` (four checks) and `DesignSideR` (the width premises); `hierGate b` and
the shipped module's facts derived (`Tools.ShippingGateCombSide`). -/
theorem parentCmp_gate_designSVN {mctx : Lean.Meta.Context}
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
      (Tools.ShippingGateCombSide.combSideB design.modules b = true →
        Tools.ShippingGateCombSide.designSideB design.modules b = true →
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
          Tools.ShippingGateCombSide.DesignSideR design.modules b ins st0 kids →
          ∃ envsO, Tools.ShippingDesignSV.DesignSV
              (Tools.ShippingMachineLinked.childMap design.modules) 0
              (Sparkle.IR.OptCheck.checkedOptimize b) (seedIn b ins) T ⟨st0, mems, kids⟩ envsO ∧
            envsO.length = T ∧
            ∀ (j : Nat) (hj : j < envsO.length),
              (envsO[j]'hj) "out" = Tools.ShippingMuxLoweringSoundness.encodeBool ((parentCmp aS bS).val j)) := by
  obtain ⟨M, envR, mF, y, hpost, hcache, tagR, hy, hobs, hA, hB, hD⟩ :=
    parentCmp_gate_designSV'' hr gdef bnd centry
  have hg : Sparkle.IR.RefineCheck.hierGate b = true := by
    obtain ⟨M', _, _, _, hpost', -, -, -, -, -, hmod'⟩ :=
      Sparkle.Tests.Compiler.GateConeDesignWalkTest.parentCmp_gate_designA hr gdef bnd centry
    exact Tools.ShippingGateCombSide.hierGate_of_modOk hmod' hpost'
  refine ⟨M, envR, mF, y, hpost, hcache, tagR, hy, hobs, hA, hB, ?_⟩
  intro hSB hDB
  obtain ⟨i0, i1, i2, cache, H⟩ := hD (Tools.ShippingGateCombSide.combOptSide_of_B hg hSB)
  refine ⟨i0, i1, i2, cache, ?_⟩
  intro D aS bS T ins st0 mems kids hin hR
  exact H aS bS T ins st0 mems kids hin
    (Tools.ShippingGateCombSide.designSide_of_R hg hSB hDB hR)

/-- **`parentNested` at the design level, checker bundles narrowed**: `parentNested_gate_designSV''`
with `combOptSide` narrowed to `combSideB` (six facts of `b`) and `DesignSide` to
`designSideB` (four checks) and `DesignSideR` (the width premises); `hierGate b` and
the shipped module's facts derived (`Tools.ShippingGateCombSide`). -/
theorem parentNested_gate_designSVN {mctx : Lean.Meta.Context}
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
      (Tools.ShippingGateCombSide.combSideB design.modules b = true →
        Tools.ShippingGateCombSide.designSideB design.modules b = true →
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
          Tools.ShippingGateCombSide.DesignSideR design.modules b ins st0 kids →
          ∃ envsO, Tools.ShippingDesignSV.DesignSV
              (Tools.ShippingMachineLinked.childMap design.modules) 0
              (Sparkle.IR.OptCheck.checkedOptimize b) (seedIn b ins) T ⟨st0, mems, kids⟩ envsO ∧
            envsO.length = T ∧
            ∀ (j : Nat) (hj : j < envsO.length),
              (envsO[j]'hj) "out" = ((parentNested aS bS).val j).toNat) := by
  obtain ⟨M, envR, mF, y, hpost, hcache, tagR, hy, hobs, hA, hB, hD⟩ :=
    parentNested_gate_designSV'' hr gdef bnd centry
  have hg : Sparkle.IR.RefineCheck.hierGate b = true := by
    obtain ⟨M', _, _, _, hpost', -, -, -, -, -, hmod'⟩ :=
      Sparkle.Tests.Compiler.GateConeDesignWalkTest.parentNested_gate_designA hr gdef bnd centry
    exact Tools.ShippingGateCombSide.hierGate_of_modOk hmod' hpost'
  refine ⟨M, envR, mF, y, hpost, hcache, tagR, hy, hobs, hA, hB, ?_⟩
  intro hSB hDB
  obtain ⟨i0, i1, i2, cache, H⟩ := hD (Tools.ShippingGateCombSide.combOptSide_of_B hg hSB)
  refine ⟨i0, i1, i2, cache, ?_⟩
  intro D aS bS T ins st0 mems kids hin hR
  exact H aS bS T ins st0 mems kids hin
    (Tools.ShippingGateCombSide.designSide_of_R hg hSB hDB hR)

end Sparkle.Tests.Compiler.GateConeDesignCombTest

#print axioms Sparkle.Tests.Compiler.GateConeDesignCombTest.parentMix_gate_designSV''
#print axioms Sparkle.Tests.Compiler.GateConeDesignCombTest.parentUse_gate_designSV''
#print axioms Sparkle.Tests.Compiler.GateConeDesignCombTest.wrapAdd_gate_designSV''
#print axioms Sparkle.Tests.Compiler.GateConeDesignCombTest.parentTwoCalls_gate_designSV''
#print axioms Sparkle.Tests.Compiler.GateConeDesignCombTest.parentRepeat_gate_designSV''
#print axioms Sparkle.Tests.Compiler.GateConeDesignCombTest.parentCmp_gate_designSV''
#print axioms Sparkle.Tests.Compiler.GateConeDesignCombTest.parentNested_gate_designSV''
#print axioms Sparkle.Tests.Compiler.GateConeDesignCombTest.parentMix_gate_designSVN
#print axioms Sparkle.Tests.Compiler.GateConeDesignCombTest.parentUse_gate_designSVN
#print axioms Sparkle.Tests.Compiler.GateConeDesignCombTest.wrapAdd_gate_designSVN
#print axioms Sparkle.Tests.Compiler.GateConeDesignCombTest.parentTwoCalls_gate_designSVN
#print axioms Sparkle.Tests.Compiler.GateConeDesignCombTest.parentRepeat_gate_designSVN
#print axioms Sparkle.Tests.Compiler.GateConeDesignCombTest.parentCmp_gate_designSVN
#print axioms Sparkle.Tests.Compiler.GateConeDesignCombTest.parentNested_gate_designSVN
