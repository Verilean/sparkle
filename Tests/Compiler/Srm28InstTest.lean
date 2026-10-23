import Tests.Compiler.Srm24WidthTest
import Tools.ShippingSrm28Regs
set_option autoImplicit false
-- BUILT (unit SRM28): dev runs r3 (exit 1), r4 (exit 0); the final-SHA rebuild in REPORT-SRM28.md is the only final evidence.
-- SCOPE: for the ACTUAL topshareM / topshareQ (hypotheses as SRM24: hcore, hpost, entry, hBnd), G5 `ShippedRegsAreSlots b regs slots` for the `regs` witness of the SINGLE `ComposedNW 2`
--   witness (`topshare{M,Q}_composedNW`), PROVED from `MachineWired`'s new call-case clause (Tools/ShippingMachineEntry.lean), `hierGate b` (SRM23) and `b.body = raw.body` (hpost via core_kids_facts_ranAM),
--   through SRM25's `shippedRegsAreSlots_of_source`; and the SRM22 `regsAtInit_of_hinit` with ONLY the G5 binder removed.  K1, G1, G3, hsk, FitTree, hRK, hst facts, hW and the ComposedNW tail
--   (hinit, seeds, kids, reset) are untouched and explicit; no reset-start assumption; no endpoint / production / general-design claim.
namespace Tests.Compiler.Srm28InstTest
open Lean Meta
open Tools.ShippingSrm7Rank Tools.ShippingSrm12Corr Sparkle.Compiler.MachInstOrigin
open Tests.Compiler.SharedLeafMemKidTest Tests.Compiler.Srm7RankTest Tests.Compiler.Srm12CorrTest
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry Tools.ShippingChildInvA Tools.ShippingChildFresh
open Tools.ShippingChildCacheA Tools.ShippingChildRunAKids Tools.ShippingChildInv Sparkle.IR.AST Sparkle.IR.Machine
open Sparkle.Compiler.Elab Tools.ShippingChildBndCore Tools.ShippingChildVCA
open Tools.ShippingSrm3Callee Tools.ShippingMemCloses Tools.ShippingMachineAuto
open Sparkle.IR.OptCheck (checkedOptimize)
open Sparkle.IR.RefineCheck (mergeChecked)
open Tests.Compiler.SharedLeafMemKidIfaceTest Tests.Compiler.SharedLeafMemKidRunTest Tests.Compiler.SharedLeafMemKidEntryTest
open Tools.ShippingSrm21Lift
open Tools.ShippingMachineLinked (childMap)
open Sparkle.IR.ModuleName (ofDecl)
open Sparkle.IR.RegDedup (declWidth)
open Tools.ShippingHierStateG (KT KSn KState runModuleTG instFree)
open Tools.ShippingMachineShipsDepth (ResetNk kidsMaskedN)
open Tools.ShippingSrm5Height Tools.ShippingSrm6Sem Tools.ShippingSrm11Bounds
open Tools.ShippingHierOpen Tools.ShippingHierState Tools.ShippingMachineShipsDepth Sparkle.IR.HierCheck Sparkle.IR.OptCheck
open Tools.ShippingSeqOptSoundness (seedIn)
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.IR.Semantics (MEnv Env)
open Tools.ShippingSrm13Supply Tools.ShippingSrm4Core6 Tools.ShippingSrm4Parent
open Tests.Compiler.Srm9ComposedTest (TmBnd TqBnd tmExt tmExtB tqExt tqExtB)
open Tools.ShippingSrm22Width Sparkle.IR.HierCheck Sparkle.IR.OptCheck
open Tests.Compiler.SharedLeafMemKidIfaceTest
open Tests.Compiler.Srm23RegsTest


/-- **PROVED** for the actual `topshareM`: `ComposedNW 2` (the one witness of `topshareM_composedNW`) with `ShippedRegsAreSlots b regs slots` for ITS `regs`; `b` is tied to `raw` by `hpost` only. -/
theorem topshareM_composedNW_g5
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {b raw : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore ``topshareM [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : MachineDefines mctx mref cctx cref ``topshareM topshareM.machineData.shape)
    (hBnd : TmBnd mctx mref cctx cref w raw D) :
    Tools.ShippingSrm28.ComposedNWRegs 2 ``topshareM topshareM.machineData 4 raw D (fun _ : Unit => defaultDomain) topshareM.machineSource tmExt tmExtB
      (fun regs => Tools.ShippingSrm22Width.ShippedRegsAreSlots b regs topshareM.machineData.shape.layout.slots) := by
  have hgate := topshareM_hierGate hcore hpost entry hBnd
  obtain ⟨O, T0, hA, entryL, entry₁, entry₂, hc1, hc2, hgrp, hw⟩ := hBnd
  have ran := topshareM_ranA O T0 hA entryL entry₁ entry₂ entry hcore hw
  have hb : b.body = raw.body := (Tools.ShippingSrm3Iface.core_kids_facts_ranAM O topshareM.machineData topshareM_parentData.ok topshareM_parentData.body
    (nDecl := 4) topshareM_parentData.callsOk topshareM_parentData.slots topshareM_parentData.domB topshareM_insts_ne topshareM_fne
    topshareM_outTy hpost ran).2.1
  exact Tools.ShippingSrm28.composedNWRegs_of_composedNW _ (topshareM_composedNW O T0 hA entryL entry₁ entry₂ entry hc1 hc2 hgrp hw hcore)
    (fun _ _ _ _ _ _ hW => Tools.ShippingSrm28.shippedRegsAreSlots_of_wired_all hgate hb hW)

/-- The SRM22 `regsAtInit_of_hinit` CALLED UNCHANGED with ONLY its binder `hG : ShippedRegsAreSlots b regs slots` removed (derived from `topshareM_composedNW_g5`, same witness); `hinit` stays an explicit hypothesis. -/
theorem topshareM_composedNW_regsAtInit_noG5
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {b raw : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore ``topshareM [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : MachineDefines mctx mref cctx cref ``topshareM topshareM.machineData.shape)
    (hBnd : TmBnd mctx mref cctx cref w raw D) :
    Tools.ShippingSrm28.ComposedNWRegs 2 ``topshareM topshareM.machineData 4 raw D (fun _ : Unit => defaultDomain) topshareM.machineSource tmExt tmExtB
      (fun regs => ∀ st0 : String → Nat,
        (∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r →
          topshareM.machineData.shape.layout.slots[k]? = some f → st0 r = f.init) →
        RegsAtInit (checkedOptimize b) st0) := by
  obtain ⟨ids, nd, len, cache, regs, rnd, rlen, hG, rest⟩ := topshareM_composedNW_g5 hcore hpost entry hBnd
  exact ⟨ids, nd, len, cache, regs, rnd, rlen,
    fun st0 hinit => Tools.ShippingSrm22Width.regsAtInit_of_hinit regs topshareM.machineData.shape.layout.slots st0 hG hinit, rest⟩


/-- **PROVED** for the actual `topshareQ`: `ComposedNW 2` (the one witness of `topshareQ_composedNW`) with `ShippedRegsAreSlots b regs slots` for ITS `regs`; `b` is tied to `raw` by `hpost` only. -/
theorem topshareQ_composedNW_g5
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {b raw : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore ``topshareQ [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : MachineDefines mctx mref cctx cref ``topshareQ topshareQ.machineData.shape)
    (hBnd : TqBnd mctx mref cctx cref w raw D) :
    Tools.ShippingSrm28.ComposedNWRegs 2 ``topshareQ topshareQ.machineData 4 raw D (fun _ : Unit => defaultDomain) topshareQ.machineSource tqExt tqExtB
      (fun regs => Tools.ShippingSrm22Width.ShippedRegsAreSlots b regs topshareQ.machineData.shape.layout.slots) := by
  have hgate := topshareQ_hierGate hcore hpost entry hBnd
  obtain ⟨O, T0, hA, hR0, hcl, entry₁, entry₂, hc1, hF, hgrp, hw⟩ := hBnd
  have ran := topshareQ_ranA O T0 hA hR0 hcl entry₁ entry₂ entry hcore hw
  have hb : b.body = raw.body := (Tools.ShippingSrm3Iface.core_kids_facts_ranAM O topshareQ.machineData topshareQ_parentData.ok topshareQ_parentData.body
    (nDecl := 4) topshareQ_parentData.callsOk topshareQ_parentData.slots topshareQ_parentData.domB topshareQ_insts_ne topshareQ_fne
    topshareQ_outTy hpost ran).2.1
  exact Tools.ShippingSrm28.composedNWRegs_of_composedNW _ (topshareQ_composedNW O T0 hA hR0 hcl entry₁ entry₂ entry hc1 hF hgrp hw hcore)
    (fun _ _ _ _ _ _ hW => Tools.ShippingSrm28.shippedRegsAreSlots_of_wired_all hgate hb hW)

/-- The SRM22 `regsAtInit_of_hinit` CALLED UNCHANGED with ONLY its binder `hG : ShippedRegsAreSlots b regs slots` removed (derived from `topshareQ_composedNW_g5`, same witness); `hinit` stays an explicit hypothesis. -/
theorem topshareQ_composedNW_regsAtInit_noG5
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {b raw : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore ``topshareQ [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : MachineDefines mctx mref cctx cref ``topshareQ topshareQ.machineData.shape)
    (hBnd : TqBnd mctx mref cctx cref w raw D) :
    Tools.ShippingSrm28.ComposedNWRegs 2 ``topshareQ topshareQ.machineData 4 raw D (fun _ : Unit => defaultDomain) topshareQ.machineSource tqExt tqExtB
      (fun regs => ∀ st0 : String → Nat,
        (∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r →
          topshareQ.machineData.shape.layout.slots[k]? = some f → st0 r = f.init) →
        RegsAtInit (checkedOptimize b) st0) := by
  obtain ⟨ids, nd, len, cache, regs, rnd, rlen, hG, rest⟩ := topshareQ_composedNW_g5 hcore hpost entry hBnd
  exact ⟨ids, nd, len, cache, regs, rnd, rlen,
    fun st0 hinit => Tools.ShippingSrm22Width.regsAtInit_of_hinit regs topshareQ.machineData.shape.layout.slots st0 hG hinit, rest⟩

end Tests.Compiler.Srm28InstTest

#print axioms Tests.Compiler.Srm28InstTest.topshareM_composedNW_g5
#print axioms Tests.Compiler.Srm28InstTest.topshareM_composedNW_regsAtInit_noG5
#print axioms Tests.Compiler.Srm28InstTest.topshareQ_composedNW_g5
#print axioms Tests.Compiler.Srm28InstTest.topshareQ_composedNW_regsAtInit_noG5
