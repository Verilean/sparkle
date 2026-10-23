import Tests.Compiler.Srm23RegsTest
import Tools.ShippingSrm24Width
set_option autoImplicit false
-- BUILT (unit SRM24): dev run h3 (exit 0); the final-SHA rebuild in REPORT-SRM24.md is the only final evidence.
-- SCOPE: the SRM22 gap Prop `ShippedRegWidthLe b` (G4) for the ACTUAL topshareM / topshareQ modules, PROVED from `hierGate b` and the sanitize-stable wire table `hT.wn`
--   (core_closed_typedIn_ranAM, as in SRM23 topshare{M,Q}_hstX_of_hst3), via `Tools.ShippingSrm24Width.shippedRegWidthLe_of_hierGate`.
--   Corollaries: SRM23 `topshare{M,Q}_regsFit_of_hstR_hst1` CALLED UNCHANGED with ONLY the binder `hW : ShippedRegWidthLe b` removed.
--   InputsAreWires (G1), SourceRegsKept (G3), ShippedRegsAreSlots (G5), hst1/hst2/hst3 are NOT touched.
namespace Tests.Compiler.Srm24WidthTest
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

/-- **PROVED** for the actual `topshareM` module: `ShippedRegWidthLe b`, from `hierGate b` and `hT.wn` (both derived from `hBnd` / `hcore` / `hpost` / `entry`). -/
theorem topshareM_shippedRegWidthLe
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {b raw : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore ``topshareM [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : MachineDefines mctx mref cctx cref ``topshareM topshareM.machineData.shape)
    (hBnd : TmBnd mctx mref cctx cref w raw D) :
    Tools.ShippingSrm22Width.ShippedRegWidthLe b := by
  have hgate := topshareM_hierGate hcore hpost entry hBnd
  obtain ⟨O, T0, hA, entryL, entry₁, entry₂, -, -, -, hw⟩ := hBnd
  have ran := topshareM_ranA O T0 hA entryL entry₁ entry₂ entry hcore hw
  have hT := Tools.ShippingSrm4Core1.core_closed_typedIn_ranAM O topshareM.machineData topshareM_parentData.ok topshareM_parentData.body
    (nDecl := 4) topshareM_parentData.callsOk topshareM_parentData.slots topshareM_parentData.domB topshareM_insts_ne topshareM_fne
    topshareM_outTy hpost ran (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (topshareM_outsClean o ho)) topshareM_scalar
  exact Tools.ShippingSrm24Width.shippedRegWidthLe_of_hierGate hgate hT.wn

/-- SRM23 `topshareM_regsFit_of_hstR_hst1` called unchanged, binder `hW : ShippedRegWidthLe b` removed (derived above); `st0` and the rest stay. -/
theorem topshareM_regsFit_of_hstR_hst1_noW
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {b raw : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore ``topshareM [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : MachineDefines mctx mref cctx cref ``topshareM topshareM.machineData.shape)
    (hBnd : TmBnd mctx mref cctx cref w raw D)
    (st0 : String → Nat) :
    RegsAtInit (checkedOptimize b) st0 →
      (∀ r ∈ seqRegs (openFlat b (openIns b) (openOuts b)), st0 r.1 < 2 ^ declWidth b r.1) →
      RegsFit (checkedOptimize b) :=
  topshareM_regsFit_of_hstR_hst1 hcore hpost entry hBnd st0 (topshareM_shippedRegWidthLe hcore hpost entry hBnd)


/-- **PROVED** for the actual `topshareQ` module: `ShippedRegWidthLe b`, from `hierGate b` and `hT.wn` (both derived from `hBnd` / `hcore` / `hpost` / `entry`). -/
theorem topshareQ_shippedRegWidthLe
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {b raw : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore ``topshareQ [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : MachineDefines mctx mref cctx cref ``topshareQ topshareQ.machineData.shape)
    (hBnd : TqBnd mctx mref cctx cref w raw D) :
    Tools.ShippingSrm22Width.ShippedRegWidthLe b := by
  have hgate := topshareQ_hierGate hcore hpost entry hBnd
  obtain ⟨O, T0, hA, hR0, hcl, entry₁, entry₂, -, -, -, hw⟩ := hBnd
  have ran := topshareQ_ranA O T0 hA hR0 hcl entry₁ entry₂ entry hcore hw
  have hT := Tools.ShippingSrm4Core1.core_closed_typedIn_ranAM O topshareQ.machineData topshareQ_parentData.ok topshareQ_parentData.body
    (nDecl := 4) topshareQ_parentData.callsOk topshareQ_parentData.slots topshareQ_parentData.domB topshareQ_insts_ne topshareQ_fne
    topshareQ_outTy hpost ran (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (topshareQ_outsClean o ho)) topshareQ_scalar
  exact Tools.ShippingSrm24Width.shippedRegWidthLe_of_hierGate hgate hT.wn

/-- SRM23 `topshareQ_regsFit_of_hstR_hst1` called unchanged, binder `hW : ShippedRegWidthLe b` removed (derived above); `st0` and the rest stay. -/
theorem topshareQ_regsFit_of_hstR_hst1_noW
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {b raw : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore ``topshareQ [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : MachineDefines mctx mref cctx cref ``topshareQ topshareQ.machineData.shape)
    (hBnd : TqBnd mctx mref cctx cref w raw D)
    (st0 : String → Nat) :
    RegsAtInit (checkedOptimize b) st0 →
      (∀ r ∈ seqRegs (openFlat b (openIns b) (openOuts b)), st0 r.1 < 2 ^ declWidth b r.1) →
      RegsFit (checkedOptimize b) :=
  topshareQ_regsFit_of_hstR_hst1 hcore hpost entry hBnd st0 (topshareQ_shippedRegWidthLe hcore hpost entry hBnd)

end Tests.Compiler.Srm24WidthTest

#print axioms Tests.Compiler.Srm24WidthTest.topshareM_shippedRegWidthLe
#print axioms Tests.Compiler.Srm24WidthTest.topshareM_regsFit_of_hstR_hst1_noW
#print axioms Tests.Compiler.Srm24WidthTest.topshareQ_shippedRegWidthLe
#print axioms Tests.Compiler.Srm24WidthTest.topshareQ_regsFit_of_hstR_hst1_noW
