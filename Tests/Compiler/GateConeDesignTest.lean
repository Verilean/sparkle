import Tests.Compiler.GateConeEntryTest
import Tools.ShippingGateDesignLift

/-! # `parentMix` at the design level, modulo three named obstacles (worker N, round 10)

WRITTEN, NOT BUILT. TARGET-ONLY (`lake build Tests.Compiler.GateConeDesignTest`;
not in `Tests.AllTests`).

`parentMix_gate_cone_runK'` (round 6) concludes, from the run, `GateDefines`
(NOT ALLOWED, ruling pending), `ChildBnd`, `EntryDefines childAdd`: an entry
`y` of `childAdd` in the final child cache and `ParentMixObservesC (ownChild y)
M` — ONE cycle of the linked evaluation of the CORE module `M` over the run's
own child.

`parentMix_gate_designSV` lifts it to the census's form, `DesignSV
(childMap design.modules) 0 (checkedOptimize b) (seedIn b ins) T …` of the
RETURNED design, through `Tools.ShippingGateDesignLift.gate_designSV_of_steps`
— under the three facts the gate side does not have, kept as ANTECEDENTS of
the conclusion (each a statement about the run's values; none is derived):

* (A) `DesignHasChild design.modules y` — `moduleByName design.modules
  y.1.name = some y.1`;
* (B) `PostKeeps b M` — `M.body.all combStmtI`, `b.body = M.body`,
  `declWidth b = moduleWidths M`;
* (C) `OptKeepsOut design.modules b "out"` — `checkedOptimize b` keeps the
  linked run's `out` (the machine route's `hierRefineCheck_linkedH` needs
  `"rst" ∈ b.inputs`, false for this combinational parent).

and the design's decidable checks and width bounds (`DesignSide`:
`kidsComb`, `designCheck … 0`, input / state / instance-state bounds) as in
the machine route's non-closed `ships_design_svH`. The per-cycle inputs are
stated in the observation's own vocabulary (`Admissible` of the cycle's
seeding, the two bit-vector inputs at signal time `T - 1 - t`).

NOT concluded: uniqueness (every closed run shows it). Premises: exactly
those of `parentMix_gate_cone_runK'`. -/
namespace Sparkle.Tests.Compiler.GateConeDesignTest
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

/-- **`parentMix` at the design level**, the obstacles (A) (B) (C) and the
design's checks as antecedents. -/
theorem parentMix_gate_designSV {mctx : Lean.Meta.Context}
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
      (DesignHasChild design.modules y → PostKeeps b M → OptKeepsOut design.modules b "out" →
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
  obtain ⟨M, envR, mF, hpost, hcache, tagR, y, hy, hobs⟩ :=
    parentMix_gate_cone_runK' hr gdef bnd centry
  refine ⟨M, envR, mF, y, hpost, hcache, tagR, hy, hobs, ?_⟩
  intro hA hB hC
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

end Sparkle.Tests.Compiler.GateConeDesignTest

#print axioms Sparkle.Tests.Compiler.GateConeDesignTest.parentMix_gate_designSV
