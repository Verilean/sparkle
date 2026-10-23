import Tests.Compiler.Srm22PairsTest
import Tools.ShippingSrm23Regs
set_option autoImplicit false
-- BUILT (unit SRM23): dev run g2 (exit 0); final-SHA rebuild only in REPORT; see STATUS-SRM23.md / REPORT-SRM23.md for the runs.
-- SCOPE: the SRM22 gap Prop `ShippedRegsFromSource b` for the ACTUAL topshareM / topshareQ modules (`b` from hcore / hpost), PROVED from `hierGate b = true`
--   (`core_hierGate_anyAM`, derived from hBnd / hcore / hpost / entry) via `Tools.ShippingSrm23Regs.shippedRegsFromSource_of_hierGate`.
--   Corollaries: SRM22 `hstX_of_hst3` and `regsFit_of_hstR_hst1` CALLED UNCHANGED with ONLY the `ShippedRegsFromSource b` binder removed.
--   The other gaps (InputsAreWires, SourceRegsKept, ShippedRegWidthLe, ShippedRegsAreSlots) are NOT proved here: `hW : ShippedRegWidthLe b` stays an explicit PREMISE.
namespace Tests.Compiler.Srm23RegsTest
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

theorem topshareM_hierGate
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {b raw : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore ``topshareM [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : MachineDefines mctx mref cctx cref ``topshareM topshareM.machineData.shape)
    (hBnd : TmBnd mctx mref cctx cref w raw D) :
    Sparkle.IR.RefineCheck.hierGate b = true := by
  obtain ⟨O, T0, hA, entryL, entry₁, entry₂, -, -, -, hw⟩ := hBnd
  have ran := topshareM_ranA O T0 hA entryL entry₁ entry₂ entry hcore hw
  exact Tools.ShippingSrm4Core2.core_hierGate_anyAM O topshareM.machineData topshareM_parentData.ok topshareM_parentData.body
    (nDecl := 4) topshareM_parentData.callsOk topshareM_parentData.slots topshareM_parentData.domB topshareM_insts_ne topshareM_fne
    topshareM_outTy hpost ran

/-- **PROVED** for the actual `topshareM` module: `ShippedRegsFromSource b`, from `hierGate b` (derived). -/
theorem topshareM_shippedRegsFromSource
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {b raw : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore ``topshareM [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : MachineDefines mctx mref cctx cref ``topshareM topshareM.machineData.shape)
    (hBnd : TmBnd mctx mref cctx cref w raw D) :
    ShippedRegsFromSource b :=
  Tools.ShippingSrm23Regs.shippedRegsFromSource_of_hierGate (topshareM_hierGate hcore hpost entry hBnd)

/-- SRM22 `hstX_of_hst3` for `topshareM`, binder `hreg : ShippedRegsFromSource b` removed (the rest of that lemma's premises: `hnd`, `hsI` explicit; `hgate`, `how`, wire/output sanitize derived from `hBnd`). -/
theorem topshareM_hstX_of_hst3
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {b raw : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore ``topshareM [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : MachineDefines mctx mref cctx cref ``topshareM topshareM.machineData.shape)
    (hBnd : TmBnd mctx mref cctx cref w raw D)
    (hnd : (b.wires.map (·.name)).Nodup)
    (hsI : ∀ p ∈ b.inputs, Sparkle.Backend.Verilog.sanitizeName p.name = p.name)
    (C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)) (st0 : String → Nat) :
    NonRegBounded (checkedOptimize b) st0 →
      ∀ x ∈ (openIns b).map (·.name), x ∉ bodyInstOuts C b.body → st0 x < 2 ^ declWidth b x := by
  have hgate := topshareM_hierGate hcore hpost entry hBnd
  obtain ⟨O, T0, hA, entryL, entry₁, entry₂, -, -, -, hw⟩ := hBnd
  have ran := topshareM_ranA O T0 hA entryL entry₁ entry₂ entry hcore hw
  have hT := Tools.ShippingSrm4Core1.core_closed_typedIn_ranAM O topshareM.machineData topshareM_parentData.ok topshareM_parentData.body
    (nDecl := 4) topshareM_parentData.callsOk topshareM_parentData.slots topshareM_parentData.domB topshareM_insts_ne topshareM_fne
    topshareM_outTy hpost ran (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (topshareM_outsClean o ho)) topshareM_scalar
  have hs : ∀ p ∈ b.wires ++ b.inputs ++ b.outputs, Sparkle.Backend.Verilog.sanitizeName p.name = p.name := by
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · rcases List.mem_append.mp hp with hp | hp
      · exact hT.wn p hp
      · exact hsI p hp
    · exact hT.ostable p hp
  exact hstX_of_hst3 hgate hnd hs hT.ow (Tools.ShippingSrm23Regs.shippedRegsFromSource_of_hierGate hgate) C st0

/-- SRM22 `regsFit_of_hstR_hst1` for `topshareM`, binder `hreg : ShippedRegsFromSource b` removed; `hW : ShippedRegWidthLe b` stays an explicit PREMISE. -/
theorem topshareM_regsFit_of_hstR_hst1
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {b raw : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore ``topshareM [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : MachineDefines mctx mref cctx cref ``topshareM topshareM.machineData.shape)
    (hBnd : TmBnd mctx mref cctx cref w raw D)
    (st0 : String → Nat) (hW : ShippedRegWidthLe b) :
    RegsAtInit (checkedOptimize b) st0 →
      (∀ r ∈ seqRegs (openFlat b (openIns b) (openOuts b)), st0 r.1 < 2 ^ declWidth b r.1) →
      RegsFit (checkedOptimize b) :=
  regsFit_of_hstR_hst1 st0 (topshareM_shippedRegsFromSource hcore hpost entry hBnd) hW

theorem topshareQ_hierGate
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {b raw : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore ``topshareQ [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : MachineDefines mctx mref cctx cref ``topshareQ topshareQ.machineData.shape)
    (hBnd : TqBnd mctx mref cctx cref w raw D) :
    Sparkle.IR.RefineCheck.hierGate b = true := by
  obtain ⟨O, T0, hA, hR0, hcl, entry₁, entry₂, -, -, -, hw⟩ := hBnd
  have ran := topshareQ_ranA O T0 hA hR0 hcl entry₁ entry₂ entry hcore hw
  exact Tools.ShippingSrm4Core2.core_hierGate_anyAM O topshareQ.machineData topshareQ_parentData.ok topshareQ_parentData.body
    (nDecl := 4) topshareQ_parentData.callsOk topshareQ_parentData.slots topshareQ_parentData.domB topshareQ_insts_ne topshareQ_fne
    topshareQ_outTy hpost ran

/-- **PROVED** for the actual `topshareQ` module: `ShippedRegsFromSource b`, from `hierGate b` (derived). -/
theorem topshareQ_shippedRegsFromSource
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {b raw : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore ``topshareQ [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : MachineDefines mctx mref cctx cref ``topshareQ topshareQ.machineData.shape)
    (hBnd : TqBnd mctx mref cctx cref w raw D) :
    ShippedRegsFromSource b :=
  Tools.ShippingSrm23Regs.shippedRegsFromSource_of_hierGate (topshareQ_hierGate hcore hpost entry hBnd)

/-- SRM22 `hstX_of_hst3` for `topshareQ`, binder `hreg : ShippedRegsFromSource b` removed (the rest of that lemma's premises: `hnd`, `hsI` explicit; `hgate`, `how`, wire/output sanitize derived from `hBnd`). -/
theorem topshareQ_hstX_of_hst3
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {b raw : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore ``topshareQ [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : MachineDefines mctx mref cctx cref ``topshareQ topshareQ.machineData.shape)
    (hBnd : TqBnd mctx mref cctx cref w raw D)
    (hnd : (b.wires.map (·.name)).Nodup)
    (hsI : ∀ p ∈ b.inputs, Sparkle.Backend.Verilog.sanitizeName p.name = p.name)
    (C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)) (st0 : String → Nat) :
    NonRegBounded (checkedOptimize b) st0 →
      ∀ x ∈ (openIns b).map (·.name), x ∉ bodyInstOuts C b.body → st0 x < 2 ^ declWidth b x := by
  have hgate := topshareQ_hierGate hcore hpost entry hBnd
  obtain ⟨O, T0, hA, hR0, hcl, entry₁, entry₂, -, -, -, hw⟩ := hBnd
  have ran := topshareQ_ranA O T0 hA hR0 hcl entry₁ entry₂ entry hcore hw
  have hT := Tools.ShippingSrm4Core1.core_closed_typedIn_ranAM O topshareQ.machineData topshareQ_parentData.ok topshareQ_parentData.body
    (nDecl := 4) topshareQ_parentData.callsOk topshareQ_parentData.slots topshareQ_parentData.domB topshareQ_insts_ne topshareQ_fne
    topshareQ_outTy hpost ran (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (topshareQ_outsClean o ho)) topshareQ_scalar
  have hs : ∀ p ∈ b.wires ++ b.inputs ++ b.outputs, Sparkle.Backend.Verilog.sanitizeName p.name = p.name := by
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · rcases List.mem_append.mp hp with hp | hp
      · exact hT.wn p hp
      · exact hsI p hp
    · exact hT.ostable p hp
  exact hstX_of_hst3 hgate hnd hs hT.ow (Tools.ShippingSrm23Regs.shippedRegsFromSource_of_hierGate hgate) C st0

/-- SRM22 `regsFit_of_hstR_hst1` for `topshareQ`, binder `hreg : ShippedRegsFromSource b` removed; `hW : ShippedRegWidthLe b` stays an explicit PREMISE. -/
theorem topshareQ_regsFit_of_hstR_hst1
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {b raw : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore ``topshareQ [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : MachineDefines mctx mref cctx cref ``topshareQ topshareQ.machineData.shape)
    (hBnd : TqBnd mctx mref cctx cref w raw D)
    (st0 : String → Nat) (hW : ShippedRegWidthLe b) :
    RegsAtInit (checkedOptimize b) st0 →
      (∀ r ∈ seqRegs (openFlat b (openIns b) (openOuts b)), st0 r.1 < 2 ^ declWidth b r.1) →
      RegsFit (checkedOptimize b) :=
  regsFit_of_hstR_hst1 st0 (topshareQ_shippedRegsFromSource hcore hpost entry hBnd) hW

end Tests.Compiler.Srm23RegsTest

#print axioms Tests.Compiler.Srm23RegsTest.topshareM_hierGate
#print axioms Tests.Compiler.Srm23RegsTest.topshareM_shippedRegsFromSource
#print axioms Tests.Compiler.Srm23RegsTest.topshareM_hstX_of_hst3
#print axioms Tests.Compiler.Srm23RegsTest.topshareM_regsFit_of_hstR_hst1
#print axioms Tests.Compiler.Srm23RegsTest.topshareQ_hierGate
#print axioms Tests.Compiler.Srm23RegsTest.topshareQ_shippedRegsFromSource
#print axioms Tests.Compiler.Srm23RegsTest.topshareQ_hstX_of_hst3
#print axioms Tests.Compiler.Srm23RegsTest.topshareQ_regsFit_of_hstR_hst1
