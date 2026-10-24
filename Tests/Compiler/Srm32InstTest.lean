import Tests.Compiler.Srm24WidthTest
import Tools.ShippingSrm28Regs
import Tools.ShippingSrm32Width
set_option autoImplicit false
-- BUILT (unit SRM32): dev runs e1 (Entry, exit 0), e2 (exit 1, syntax), e3 (exit 0), a1 (exit 1, stale Srm28AuditTest count), a2 (exit 0); the final-SHA rebuild in REPORT-SRM32.md is the only final evidence.
-- SCOPE: for the ACTUAL topshareM / topshareQ (hypotheses as SRM28: hcore, hpost, entry, hBnd), the width link hWd (the text frozen in SRM31's EXPECTED) for the `regs` witness of the SINGLE
--   `ComposedNW 2` witness (`topshare{M,Q}_composedNW`), PROVED from `MachineWired`'s 20th conjunct (Tools/ShippingMachineEntry.lean), `hierGate b` (SRM23) and `hpost` (declWidth b = weOf raw).
--   All other binders (G1, G3, K1, hsk, FitTree, hRK, hst, hW, hinit, ComposedNW tail) are untouched and explicit; no reset-start assumption; no endpoint / production / general-design claim.
namespace Tests.Compiler.Srm32InstTest
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


/-- **PROVED** for the actual `topshareM`: `ComposedNW 2` (the one witness of `topshareM_composedNW`) with the width link `hWd` for ITS `regs`; `b` is tied to `raw` by `hpost` only. -/
theorem topshareM_composedNW_hWd
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {b raw : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore ``topshareM [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : MachineDefines mctx mref cctx cref ``topshareM topshareM.machineData.shape)
    (hBnd : TmBnd mctx mref cctx cref w raw D) :
    Tools.ShippingSrm28.ComposedNWRegs 2 ``topshareM topshareM.machineData 4 raw D (fun _ : Unit => defaultDomain) topshareM.machineSource tmExt tmExtB
      (fun regs => ∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r →
        topshareM.machineData.shape.layout.slots[k]? = some f → f.width ≤ declWidth b r) := by
  have hgate := topshareM_hierGate hcore hpost entry hBnd
  obtain ⟨O, T0, hA, entryL, entry₁, entry₂, hc1, hc2, hgrp, hw⟩ := hBnd
  exact Tools.ShippingSrm28.composedNWRegs_of_composedNW _ (topshareM_composedNW O T0 hA entryL entry₁ entry₂ entry hc1 hc2 hgrp hw hcore)
    (fun _ _ _ _ _ _ hW => Tools.ShippingSrm32.hWd_of_wired hpost hgate topshareM_outTy hW)

/-- **PROVED** for the actual `topshareQ`: `ComposedNW 2` (the one witness of `topshareQ_composedNW`) with the width link `hWd` for ITS `regs`; `b` is tied to `raw` by `hpost` only. -/
theorem topshareQ_composedNW_hWd
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {b raw : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore ``topshareQ [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : MachineDefines mctx mref cctx cref ``topshareQ topshareQ.machineData.shape)
    (hBnd : TqBnd mctx mref cctx cref w raw D) :
    Tools.ShippingSrm28.ComposedNWRegs 2 ``topshareQ topshareQ.machineData 4 raw D (fun _ : Unit => defaultDomain) topshareQ.machineSource tqExt tqExtB
      (fun regs => ∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r →
        topshareQ.machineData.shape.layout.slots[k]? = some f → f.width ≤ declWidth b r) := by
  have hgate := topshareQ_hierGate hcore hpost entry hBnd
  obtain ⟨O, T0, hA, hR0, hcl, entry₁, entry₂, hc1, hF, hgrp, hw⟩ := hBnd
  exact Tools.ShippingSrm28.composedNWRegs_of_composedNW _ (topshareQ_composedNW O T0 hA hR0 hcl entry₁ entry₂ entry hc1 hF hgrp hw hcore)
    (fun _ _ _ _ _ _ hW => Tools.ShippingSrm32.hWd_of_wired hpost hgate topshareQ_outTy hW)

end Tests.Compiler.Srm32InstTest

#print axioms Tests.Compiler.Srm32InstTest.topshareM_composedNW_hWd
#print axioms Tests.Compiler.Srm32InstTest.topshareQ_composedNW_hWd
