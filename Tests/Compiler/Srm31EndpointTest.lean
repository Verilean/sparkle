import Tests.Compiler.Srm9ComposedTest
import Tools.ShippingSrm31Core
set_option autoImplicit false
-- BUILT (unit SRM31): dev runs c2, a4 (exit 0); further dev runs are recorded in REPORT-SRM31.md; the final-SHA rebuild there is the only final evidence.
-- SCOPE (instance-specific, topshareM / topshareQ ONLY).  `topshare{M,Q}_hierC_at_nw` = `Tests.Compiler.Srm9ComposedTest.topshare{M,Q}_hierC_at_free` with EVERY binder and the conclusion unchanged EXCEPT the last antecedent `hstR`,
-- which is REPLACED by the per-slot width link `slot.width ≤ declWidth b r` (for the same `regs` witness).  The `composed` binder is supplied by SRM4's `topshare*_composedNW` DIRECTLY (not through `composedG_of_NW`), so the wiring is used.
-- INTERMEDIATE endpoint theorems, CONDITIONAL on the width link (a new machine-derived PREMISE).  NOT a discharge of `hstR` (the endpoint hstR gap stays OPEN): the width link is a PREMISE (MachineWired exports it only for shape.insts = []); the slot-init fit `f.init < 2^f.width` is decided on the concrete layout.  TmBnd/TqBnd, Bd, SourceInputs, hinit, ResetNk 2, hinsFit, hstX stay explicit.
namespace Tests.Compiler.Srm31EndpointTest
open Lean Meta
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry Tools.ShippingChildInvA Tools.ShippingChildFresh
open Tools.ShippingChildCacheA Tools.ShippingChildRunAKids Tools.ShippingChildInv Sparkle.IR.AST Sparkle.IR.Machine
open Sparkle.Compiler.Elab Tools.ShippingChildBndCore Tools.ShippingChildVCA
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.IR.OptCheck Sparkle.IR.HierCheck Sparkle.IR.Semantics
open Sparkle.IR.RefineCheck (mergeChecked)
open Sparkle.IR.RegDedup (declWidth)
open Tools.ShippingMachineLinked (childMap)
open Tools.ShippingMachineAuto Tools.ShippingMachineLinked Tools.ShippingMachineDepth
open Tools.ShippingHierOpen Tools.ShippingHierState Tools.ShippingHierStateG Tools.ShippingHierOptRun
open Tools.ShippingMachineShipsHier Tools.ShippingMachineShipsDepth
open Tools.ShippingMixedSourceBridge
open Tools.ShippingSeqOptSoundness (seedIn)
open Tools.ShippingMachineSource Tools.ShippingMachineDenote Tools.ShippingMachineDepthRunRA
open Tools.ShippingDesignSV Tools.ShippingDesignSVBounds
open Tools.ShippingSeqParentLemmas (HCallsOf)
open Tools.ShippingMachineCausal (letObsB)
open Tools.ShippingSrm3Callee Tools.ShippingSrm4Callee
open Tools.ShippingQuadComposed (QuadGroupFacts)
open Tests.Compiler.SharedLeafMemKidTest Tests.Compiler.SharedLeafMemKidRunTest Tests.Compiler.SharedLeafMemKidIfaceTest
open Tests.Compiler.Srm9ComposedTest (TmBnd TqBnd tmExt tmExtB tqExt tqExtB)

/-- **`machine_ships_hierC_at_free` at `topshareM`, KSn 2**: every binder but the run ones (`hcore`, `hpost`, `entry`, `closes`) supplied. -/
theorem topshareM_hierC_at_nw
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {b raw : Sparkle.IR.AST.Module} {D : Design}
    (hcore : RunsTo (synthesizeCombinationalCore ``topshareM [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : MachineDefines mctx mref cctx cref ``topshareM topshareM.machineData.shape)
    (closes : (fun _ _ _ _ => True) mctx mref cctx cref) :
        TmBnd mctx mref cctx cref w raw D → (fun (b : Sparkle.IR.AST.Module) (D : Design) => kidsMaskedN D.modules b.body = true) b D →
        ∃ ids : List FVarId, ids.Nodup ∧ ids.length = topshareM.machineData.shape.binders.length ∧
        ∃ (cache : IO.Ref (ExprStructMap String)) (regs : List String),
          regs.Nodup ∧ regs.length = topshareM.machineData.ss.length ∧
          ∀ (i : Unit) (bools : Nat → Signal (defaultDomain) Bool)
            (bits : (j : Nat) → (n : Nat) → Signal (defaultDomain) (BitVec n))
            (T : Nat) (ins : Nat → String → Nat) (st0 : String → Nat) (mems : MEnv)
            (kids : String → KT 2),
            (∀ t st, t < T → SourceInputs ``topshareM (topshareM.machineData.bsIn.take 4) ids cache
              (fun j => (tmExtB i bools bits j).val (T - 1 - t))
              (fun j n => (tmExt i bools bits j n).val (T - 1 - t)) (seedIn b ins t st)) →
            (∀ t st r, r ∈ regs → seedIn b ins t st r = st r) →
            (∀ t, ins t "rst" = 0) → (∀ t st, seedIn b ins t st "clk" = 0) →
            (∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r →
              topshareM.machineData.shape.layout.slots[k]? = some f → st0 r = f.init) →
            ResetNk 2 raw D kids →
            (∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ declWidth b x) →
            (∀ x ∈ (openIns b).map (·.name), x ∉ bodyInstOuts (childMap D.modules) b.body →
              st0 x < 2 ^ declWidth b x) →
            (∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r →
              topshareM.machineData.shape.layout.slots[k]? = some f → f.width ≤ declWidth b r) →
            ∃ envsO, runModuleTG (KSn (childMap D.modules) 2) (declWidth (checkedOptimize b))
                (childMap D.modules) (checkedOptimize b).body (seedIn b ins) T
                ⟨st0, mems, kids⟩ = some envsO ∧
              envsO.length = T ∧
              ∀ j (hj : j < envsO.length) (k : Nat) (o : OutField) (f : Nat → Nat),
                topshareM.machineData.shape.layout.outs[k]? = some o → (topshareM.machineSource i bools bits)[k]? = some f →
                (envsO[j]'hj) o.name = f j :=
  Tools.ShippingSrm31.machine_ships_hierC_at_nw (n := 2) (fun D => KSn_local (childMap D.modules) 2)
    TmBnd (fun _ _ _ _ => True) (fun (b : Sparkle.IR.AST.Module) (D : Design) => kidsMaskedN D.modules b.body = true)
    (fun _ _ => True)
    (fun b D hok => KSn_boundedIn D.modules b.body hok 2)
    (true_inv _) topshareM.machineData
    (lsrc := letObsB topshareM.machineData (fun _ : Unit => defaultDomain) topshareM.machineInits topshareM.machineBody topshareM.machineExt topshareM.machineExtB) (srcL := topshareM.machineSource) (extL := tmExt) (extBL := tmExtB)
    (fun hrun hentry _ hB => by
      obtain ⟨O, T, hA, entryL, entry₁, entry₂, hc1, hc2, hgrp, hw⟩ := hB
      exact topshareM_soundLA O T hA entryL entry₁ entry₂ hentry hw hrun)
    (fun hrun hentry _ hB _ => by
      obtain ⟨O, T, hA, entryL, entry₁, entry₂, hc1, hc2, hgrp, hw⟩ := hB
      exact topshareM_composedNW O T hA entryL entry₁ entry₂ hentry hc1 hc2 hgrp hw hrun)
    topshareM_outTy (by decide) hcore hpost entry closes
    (fun hB => by
      obtain ⟨O, T, hA, entryL, entry₁, entry₂, hc1, hc2, hgrp, hw⟩ := hB
      exact topshareM_runFacts O T hA entryL entry₁ entry₂ entry hcore hpost hw)

/-- **`machine_ships_hierC_at_free` at `topshareQ`, KSn 2**: every binder but the run ones (`hcore`, `hpost`, `entry`, `closes`) supplied. -/
theorem topshareQ_hierC_at_nw
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {b raw : Sparkle.IR.AST.Module} {D : Design}
    (hcore : RunsTo (synthesizeCombinationalCore ``topshareQ [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : MachineDefines mctx mref cctx cref ``topshareQ topshareQ.machineData.shape)
    (closes : (fun _ _ _ _ => True) mctx mref cctx cref) :
        TqBnd mctx mref cctx cref w raw D → (fun (b : Sparkle.IR.AST.Module) (D : Design) => kidsMaskedN D.modules b.body = true) b D →
        ∃ ids : List FVarId, ids.Nodup ∧ ids.length = topshareQ.machineData.shape.binders.length ∧
        ∃ (cache : IO.Ref (ExprStructMap String)) (regs : List String),
          regs.Nodup ∧ regs.length = topshareQ.machineData.ss.length ∧
          ∀ (i : Unit) (bools : Nat → Signal (defaultDomain) Bool)
            (bits : (j : Nat) → (n : Nat) → Signal (defaultDomain) (BitVec n))
            (T : Nat) (ins : Nat → String → Nat) (st0 : String → Nat) (mems : MEnv)
            (kids : String → KT 2),
            (∀ t st, t < T → SourceInputs ``topshareQ (topshareQ.machineData.bsIn.take 4) ids cache
              (fun j => (tqExtB i bools bits j).val (T - 1 - t))
              (fun j n => (tqExt i bools bits j n).val (T - 1 - t)) (seedIn b ins t st)) →
            (∀ t st r, r ∈ regs → seedIn b ins t st r = st r) →
            (∀ t, ins t "rst" = 0) → (∀ t st, seedIn b ins t st "clk" = 0) →
            (∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r →
              topshareQ.machineData.shape.layout.slots[k]? = some f → st0 r = f.init) →
            ResetNk 2 raw D kids →
            (∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ declWidth b x) →
            (∀ x ∈ (openIns b).map (·.name), x ∉ bodyInstOuts (childMap D.modules) b.body →
              st0 x < 2 ^ declWidth b x) →
            (∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r →
              topshareQ.machineData.shape.layout.slots[k]? = some f → f.width ≤ declWidth b r) →
            ∃ envsO, runModuleTG (KSn (childMap D.modules) 2) (declWidth (checkedOptimize b))
                (childMap D.modules) (checkedOptimize b).body (seedIn b ins) T
                ⟨st0, mems, kids⟩ = some envsO ∧
              envsO.length = T ∧
              ∀ j (hj : j < envsO.length) (k : Nat) (o : OutField) (f : Nat → Nat),
                topshareQ.machineData.shape.layout.outs[k]? = some o → (topshareQ.machineSource i bools bits)[k]? = some f →
                (envsO[j]'hj) o.name = f j :=
  Tools.ShippingSrm31.machine_ships_hierC_at_nw (n := 2) (fun D => KSn_local (childMap D.modules) 2)
    TqBnd (fun _ _ _ _ => True) (fun (b : Sparkle.IR.AST.Module) (D : Design) => kidsMaskedN D.modules b.body = true)
    (fun _ _ => True)
    (fun b D hok => KSn_boundedIn D.modules b.body hok 2)
    (true_inv _) topshareQ.machineData
    (lsrc := letObsB topshareQ.machineData (fun _ : Unit => defaultDomain) topshareQ.machineInits topshareQ.machineBody topshareQ.machineExt topshareQ.machineExtB) (srcL := topshareQ.machineSource) (extL := tqExt) (extBL := tqExtB)
    (fun hrun hentry _ hB => by
      obtain ⟨O, T, hA, hR0, hcl, entry₁, entry₂, hc1, hF, hgrp, hw⟩ := hB
      exact topshareQ_soundLA O T hA hR0 hcl entry₁ entry₂ hentry hw hrun)
    (fun hrun hentry _ hB _ => by
      obtain ⟨O, T, hA, hR0, hcl, entry₁, entry₂, hc1, hF, hgrp, hw⟩ := hB
      exact topshareQ_composedNW O T hA hR0 hcl entry₁ entry₂ hentry hc1 hF hgrp hw hrun)
    topshareQ_outTy (by decide) hcore hpost entry closes
    (fun hB => by
      obtain ⟨O, T, hA, hR0, hcl, entry₁, entry₂, hc1, hF, hgrp, hw⟩ := hB
      exact topshareQ_runFacts O T hA hR0 hcl entry₁ entry₂ entry hcore hpost hw)

end Tests.Compiler.Srm31EndpointTest

#print axioms Tests.Compiler.Srm31EndpointTest.topshareM_hierC_at_nw
#print axioms Tests.Compiler.Srm31EndpointTest.topshareQ_hierC_at_nw
