import Tests.Compiler.Srm4ComposedTest
import Tests.Compiler.Srm4ComposedQTest
import Tests.Compiler.Srm4ParentTest
import Tests.Compiler.Srm4ParentQTest
import Tools.ShippingShipsFree
-- BUILT (unit SRM9): r5 exit 0 (dev run, default heartbeats); the final-SHA rebuild is in REPORT-SRM9.md.
-- SCOPE (binding).  The `composed` binder of `Tools.ShippingShipsFree.machine_ships_hierC_at_free` (with `KS = KSn (childMap D.modules) 2`, `Reset = ResetNk 2`) for `topshareM` and `topshareQ` ONLY (instance-specific).
-- PROVED here: `topshareM_composed_binder`, `topshareQ_composed_binder` (= the binder, from SRM4's `topshare*_composedNW` through the GENERIC, pre-existing `Tools.ShippingMachineShipsDepth.composedG_of_NW`: it drops `lets`/`MachineWired`
--   and turns the per-instance `ResetN` hypothesis into `ResetNk n`; the binder's extra `memFree m.body` hypothesis is unused), and `topshareM_hierC_at_free` / `topshareQ_hierC_at_free` (`machine_ships_hierC_at_free` at KSn 2 with EVERY
--   binder but the run ones supplied: `hloc`, `hBd`, `hRI`, `soundL`, `composed`, `houtTy`, `facts`).
-- PREMISE: the instance data bundle `TmBnd` / `TqBnd` (the run boundary `Bnd`): `O`, `T`, `AdmCtx`, the `MachineDefines` of the leaves/callees, SRM4's text-supplied `hcalls`/`hF`/`hgrp` and the start-world fact `JQC O 0 w` (a history of past synthesis results).
--   The bundle is a premise of the conclusion (`Bnd mctx mref cctx cref w raw D →`); it is NOT discharged.  `C` is `True`.  `entry` (the parent's `MachineDefines`), `hcore`, `hpost` stay run premises of the conclusion.
-- No `sorry`, no `axiom`, no `native_decide`, no heartbeat option.
namespace Tests.Compiler.Srm9ComposedTest
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

/-! ## topshareM -/

abbrev TmH1 {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ (m : Sparkle.IR.AST.Module) (design : Sparkle.IR.AST.Design),
    HCallsOf 1 wrapM.machineData design m (dom := fun i : DomainConfig => i)
      (letObsB wrapM.machineData (fun i : DomainConfig => i) wrapM.machineInits wrapM.machineBody wrapM.machineExt wrapM.machineExtB)
      (fun i bools bits => wrapM.machineExt i bools bits (stateLoop wrapM.machineInits (wrapM.machineBody i bools bits)))
      (fun i bools bits => wrapM.machineExtB i bools bits (stateLoop wrapM.machineInits (wrapM.machineBody i bools bits)))
      4 (memLeafBsC ``leafM leafM.machineData 4) (memLeafOutsC ``leafM leafM.machineData) (memLeafSrcC ``leafM leafM.machineData 4 leafM.machineSource)
      (memLeafPC O ``leafM leafM.machineData design)
abbrev TmH2 {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ (m : Sparkle.IR.AST.Module) (design : Sparkle.IR.AST.Design),
    HCallsOf 1 wrapM3.machineData design m (dom := fun i : DomainConfig => i)
      (letObsB wrapM3.machineData (fun i : DomainConfig => i) wrapM3.machineInits wrapM3.machineBody wrapM3.machineExt wrapM3.machineExtB)
      (fun i bools bits => wrapM3.machineExt i bools bits (stateLoop wrapM3.machineInits (wrapM3.machineBody i bools bits)))
      (fun i bools bits => wrapM3.machineExtB i bools bits (stateLoop wrapM3.machineInits (wrapM3.machineBody i bools bits)))
      4 (memLeafBsC ``leafM leafM.machineData 4) (memLeafOutsC ``leafM leafM.machineData) (memLeafSrcC ``leafM leafM.machineData 4 leafM.machineSource)
      (memLeafPC O ``leafM leafM.machineData design)
abbrev TmGrp : Prop := QuadGroupFacts topshareM.machineData 4
      (letObsB topshareM.machineData (fun _ : Unit => defaultDomain) topshareM.machineInits topshareM.machineBody topshareM.machineExt topshareM.machineExtB)
      (fun i bools bits => topshareM.machineExt i bools bits (stateLoop topshareM.machineInits (topshareM.machineBody i bools bits)))
      (fun i bools bits => topshareM.machineExtB i bools bits (stateLoop topshareM.machineInits (topshareM.machineBody i bools bits)))
      tmBsC tmOutsC tmSrcC

/-- PREMISE (boundary): the instance data `topshareM_composedNW` / `topshareM_soundLA` / `topshareM_runFacts` / `topshareM_kidsMasked` take, besides the run. -/
def TmBnd : CtxBnd := fun mctx mref cctx cref w _ _ =>
  ∃ (O : RefLawsAOps MkRefd mref cref) (_ : RefLawsATele O.quiet mref cref),
    AdmCtx O.quiet mctx cctx ∧
    MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape ∧
    MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape ∧
    MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape ∧
    TmH1 O ∧ TmH2 O ∧ TmGrp ∧ JQC O 0 w

noncomputable abbrev tmExt := fun i bools bits => topshareM.machineExt i bools bits (stateLoop topshareM.machineInits (topshareM.machineBody i bools bits))
noncomputable abbrev tmExtB := fun i bools bits => topshareM.machineExtB i bools bits (stateLoop topshareM.machineInits (topshareM.machineBody i bools bits))

/-- **The `composed` binder of `machine_ships_hierC_at_free` for `topshareM`** (KS = KSn 2, Reset = ResetNk 2, C = True, Bnd = TmBnd). -/
theorem topshareM_composed_binder :
    ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
      {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w' : Void IO.RealWorld}
      {m : Sparkle.IR.AST.Module} {design : Design},
      RunsTo (synthesizeCombinationalCore ``topshareM [] false) mctx mref cctx cref w (m, design) w' →
      MachineDefines mctx mref cctx cref ``topshareM topshareM.machineData.shape →
      (fun _ _ _ _ => True) mctx mref cctx cref →
      TmBnd mctx mref cctx cref w m design → Tools.ConeFold.memFree m.body →
      ComposedG (fun D => KSn (childMap D.modules) 2) (ResetNk 2) ``topshareM topshareM.machineData 4 m design
        (fun _ : Unit => defaultDomain) topshareM.machineSource tmExt tmExtB := by
  intro mctx mref cctx cref w w' m design hcore entryP _ hB _
  obtain ⟨O, T, hA, entryL, entry₁, entry₂, hc1, hc2, hgrp, hw⟩ := hB
  exact composedG_of_NW (topshareM_composedNW O T hA entryL entry₁ entry₂ entryP hc1 hc2 hgrp hw hcore)

/-- **`machine_ships_hierC_at_free` at `topshareM`, KSn 2**: every binder but the run ones (`hcore`, `hpost`, `entry`, `closes`) supplied. -/
theorem topshareM_hierC_at_free
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
            (∀ r ∈ seqRegs (openFlat b (openIns b) (openOuts b)), st0 r.1 < 2 ^ declWidth b r.1) →
            ∃ envsO, runModuleTG (KSn (childMap D.modules) 2) (declWidth (checkedOptimize b))
                (childMap D.modules) (checkedOptimize b).body (seedIn b ins) T
                ⟨st0, mems, kids⟩ = some envsO ∧
              envsO.length = T ∧
              ∀ j (hj : j < envsO.length) (k : Nat) (o : OutField) (f : Nat → Nat),
                topshareM.machineData.shape.layout.outs[k]? = some o → (topshareM.machineSource i bools bits)[k]? = some f →
                (envsO[j]'hj) o.name = f j :=
  Tools.ShippingShipsFree.machine_ships_hierC_at_free (fun D => KSn (childMap D.modules) 2) (fun D => KSn_local (childMap D.modules) 2)
    (ResetNk 2) TmBnd (fun _ _ _ _ => True) (fun (b : Sparkle.IR.AST.Module) (D : Design) => kidsMaskedN D.modules b.body = true)
    (fun _ _ => True)
    (fun b D hok => KSn_boundedIn D.modules b.body hok 2)
    (true_inv _) topshareM.machineData
    (lsrc := letObsB topshareM.machineData (fun _ : Unit => defaultDomain) topshareM.machineInits topshareM.machineBody topshareM.machineExt topshareM.machineExtB) (srcL := topshareM.machineSource) (extL := tmExt) (extBL := tmExtB)
    (fun hrun hentry _ hB => by
      obtain ⟨O, T, hA, entryL, entry₁, entry₂, hc1, hc2, hgrp, hw⟩ := hB
      exact topshareM_soundLA O T hA entryL entry₁ entry₂ hentry hw hrun)
    topshareM_composed_binder topshareM_outTy hcore hpost entry closes
    (fun hB => by
      obtain ⟨O, T, hA, entryL, entry₁, entry₂, hc1, hc2, hgrp, hw⟩ := hB
      exact topshareM_runFacts O T hA entryL entry₁ entry₂ entry hcore hpost hw)


/-! ## topshareQ -/

/-- PREMISE (boundary): the instance data `topshareQ_composedNW` / `topshareQ_soundLA` / `topshareQ_runFacts` / `topshareQ_kidsMasked` take, besides the run. -/
def TqBnd : CtxBnd := fun mctx mref cctx cref w _ _ =>
  ∃ (O : RefLawsAOps MkRefd mref cref) (_ : RefLawsATele O.quiet mref cref),
    AdmCtx O.quiet mctx cctx ∧
    MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape ∧
    (∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape) ∧
    MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape ∧
    MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape ∧
    TqHcallsP O ∧ TqFQ ∧ TqGrp ∧ JQC O 0 w

noncomputable abbrev tqExt := fun i bools bits => topshareQ.machineExt i bools bits (stateLoop topshareQ.machineInits (topshareQ.machineBody i bools bits))
noncomputable abbrev tqExtB := fun i bools bits => topshareQ.machineExtB i bools bits (stateLoop topshareQ.machineInits (topshareQ.machineBody i bools bits))

/-- **The `composed` binder of `machine_ships_hierC_at_free` for `topshareQ`** (KS = KSn 2, Reset = ResetNk 2, C = True, Bnd = TqBnd). -/
theorem topshareQ_composed_binder :
    ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
      {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w' : Void IO.RealWorld}
      {m : Sparkle.IR.AST.Module} {design : Design},
      RunsTo (synthesizeCombinationalCore ``topshareQ [] false) mctx mref cctx cref w (m, design) w' →
      MachineDefines mctx mref cctx cref ``topshareQ topshareQ.machineData.shape →
      (fun _ _ _ _ => True) mctx mref cctx cref →
      TqBnd mctx mref cctx cref w m design → Tools.ConeFold.memFree m.body →
      ComposedG (fun D => KSn (childMap D.modules) 2) (ResetNk 2) ``topshareQ topshareQ.machineData 4 m design
        (fun _ : Unit => defaultDomain) topshareQ.machineSource tqExt tqExtB := by
  intro mctx mref cctx cref w w' m design hcore entryP _ hB _
  obtain ⟨O, T, hA, hR0, hcl, entry₁, entry₂, hc1, hF, hgrp, hw⟩ := hB
  exact composedG_of_NW (topshareQ_composedNW O T hA hR0 hcl entry₁ entry₂ entryP hc1 hF hgrp hw hcore)

/-- **`machine_ships_hierC_at_free` at `topshareQ`, KSn 2**: every binder but the run ones (`hcore`, `hpost`, `entry`, `closes`) supplied. -/
theorem topshareQ_hierC_at_free
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
            (∀ r ∈ seqRegs (openFlat b (openIns b) (openOuts b)), st0 r.1 < 2 ^ declWidth b r.1) →
            ∃ envsO, runModuleTG (KSn (childMap D.modules) 2) (declWidth (checkedOptimize b))
                (childMap D.modules) (checkedOptimize b).body (seedIn b ins) T
                ⟨st0, mems, kids⟩ = some envsO ∧
              envsO.length = T ∧
              ∀ j (hj : j < envsO.length) (k : Nat) (o : OutField) (f : Nat → Nat),
                topshareQ.machineData.shape.layout.outs[k]? = some o → (topshareQ.machineSource i bools bits)[k]? = some f →
                (envsO[j]'hj) o.name = f j :=
  Tools.ShippingShipsFree.machine_ships_hierC_at_free (fun D => KSn (childMap D.modules) 2) (fun D => KSn_local (childMap D.modules) 2)
    (ResetNk 2) TqBnd (fun _ _ _ _ => True) (fun (b : Sparkle.IR.AST.Module) (D : Design) => kidsMaskedN D.modules b.body = true)
    (fun _ _ => True)
    (fun b D hok => KSn_boundedIn D.modules b.body hok 2)
    (true_inv _) topshareQ.machineData
    (lsrc := letObsB topshareQ.machineData (fun _ : Unit => defaultDomain) topshareQ.machineInits topshareQ.machineBody topshareQ.machineExt topshareQ.machineExtB) (srcL := topshareQ.machineSource) (extL := tqExt) (extBL := tqExtB)
    (fun hrun hentry _ hB => by
      obtain ⟨O, T, hA, hR0, hcl, entry₁, entry₂, hc1, hF, hgrp, hw⟩ := hB
      exact topshareQ_soundLA O T hA hR0 hcl entry₁ entry₂ hentry hw hrun)
    topshareQ_composed_binder topshareQ_outTy hcore hpost entry closes
    (fun hB => by
      obtain ⟨O, T, hA, hR0, hcl, entry₁, entry₂, hc1, hF, hgrp, hw⟩ := hB
      exact topshareQ_runFacts O T hA hR0 hcl entry₁ entry₂ entry hcore hpost hw)

end Tests.Compiler.Srm9ComposedTest

#print axioms Tests.Compiler.Srm9ComposedTest.topshareM_composed_binder
#print axioms Tests.Compiler.Srm9ComposedTest.topshareM_hierC_at_free
#print axioms Tests.Compiler.Srm9ComposedTest.topshareQ_composed_binder
#print axioms Tests.Compiler.Srm9ComposedTest.topshareQ_hierC_at_free
