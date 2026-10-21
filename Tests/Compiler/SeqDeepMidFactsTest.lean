import Tests.Compiler.SeqDeepMidTest
import Tests.Compiler.ParentDesignCheckFATest
import Tools.ShippingSeqChildDeepFactsA
-- BUILT (unit SR3o): o9 exit 0 (o8 exit 1: kindTy namespace). In-test audit THROWS on failure.
-- SCOPE (binding): the CHILD `mid` of the depth-2 chain `grand -> mid -> cnt` (callee `cnt`, a leaf register machine).  PROVED
-- relative to `O`, `T : RefLawsATele` (ADDED boundary), `MachineDefines` of `mid` / `cnt` and a `RealChildA O mid y` (a history
-- of past synthesis results, not freshness): `RunFacts (childMap y.2.modules) y.1`, `outsCheck` (PREMISE `hierGate y.1`),
-- `designCheck` of `checkedOptimize y.1` at every depth.  NOT the `KidFacts.check` field (OPEN, ledger L8x).
namespace Tests.Compiler.SeqDeepMidFactsTest
open Sparkle.Tests.Compiler.ShippingMachineSeqTest
open Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildCacheA Tools.ShippingChildVCA Tools.ShippingChildBndCore
open Tools.ShippingMachineLinked (childMap)
open Sparkle.IR.OptCheck (checkedOptimize)
open Tests.Compiler.SeqDeepMidTest

theorem mid_insts_cnt : ∀ (k : Nat) (hk : k < mid.machineData.shape.insts.length),
    (mid.machineData.shape.insts[k]).1 = ``cnt := by
  first | decide | decide +kernel

theorem mid_callArgs :
    Tools.ShippingPortsMatchRaw.callArgsOk mid.machineData 2 (fun _ => [1]) = true := by
  first | decide | decide +kernel

section
variable {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}

theorem mid_hkidP (O : RefLawsAOps MkRefd mref cref)
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``cnt cnt.machineData.shape) :
    ∀ (k : Nat) (hk : k < mid.machineData.shape.insts.length) (y : Tools.ShippingChildInv.Res),
      RealChildA O (mid.machineData.shape.insts[k]).1 y →
      ∀ p ∈ y.1.outputs, (∀ q ∈ Tools.ShippingInstStmtG.inPortsOf y.1, q.name ≠ p.name) ∧
        p.name ≠ "clk" ∧ p.name ≠ "rst" := by
  intro k hk y hy
  rw [mid_insts_cnt k hk] at hy
  exact (Tools.ShippingSeqChildIfaceA.seqChild_of_realA O cnt.machineData cnt.machine_ok cnt.machine_body
    (by decide) (by decide) hR0 (fun mc cc => cnt.machine_closes mc _ cc _) hy).outsIn

theorem mid_hkidT (O : RefLawsAOps MkRefd mref cref)
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``cnt cnt.machineData.shape) :
    ∀ (k : Nat) (hk : k < mid.machineData.shape.insts.length) (y : Tools.ShippingChildInv.Res),
      RealChildA O (mid.machineData.shape.insts[k]).1 y →
      Tools.ShippingChildIfaceTy.ChildOutTys cnt.machineData.shape.layout.outs y.1 := by
  intro k hk y hy
  rw [mid_insts_cnt k hk] at hy
  exact Tools.ShippingCallWidthsChildRealA.leaf_real_outTysA (O := O) cnt.machineData cnt.machine_ok cnt.machine_body
    (by decide) (by decide) (by decide) (by decide) hR0
    (fun mctx' cctx' {tenv} b _ w r w' _ _ hr => cnt.machine_closes mctx' _ cctx' _ (Tools.ShippingChildInv.profLogIO b) w r w' hr) hy

theorem mid_hkidW (O : RefLawsAOps MkRefd mref cref)
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``cnt cnt.machineData.shape) :
    ∀ (k : Nat) (hk : k < mid.machineData.shape.insts.length) (y : Tools.ShippingChildInv.Res),
      RealChildA O (mid.machineData.shape.insts[k]).1 y →
      ∀ p ∈ y.1.outputs, p.name = mid.machineData.shape.instFields.getD k "" →
        (mid.machineData.shape.binders[2 + k]?).map (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth) =
          some p.ty.bitWidth :=
  Tools.ShippingParentRunFactsA.hkidW_of_dataA O
    (kidOuts := fun _ => cnt.machineData.shape.layout.outs)
    (by first | decide | decide +kernel) (mid_hkidT O hR0)

set_option maxHeartbeats 4000000 in
/-- **`RunFacts` of the SERVED `mid`** against its served design (`deepChild_runFactsA`; `cnt`'s facts from `RealChildA`). -/
theorem mid_runFactsA (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``mid mid.machineData.shape)
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``cnt cnt.machineData.shape)
    {y : Tools.ShippingChildInv.Res} (h : RealChildA O ``mid y) :
    Tools.ShippingGuardsSound.RunFacts (childMap y.2.modules) y.1 :=
  Tools.ShippingSeqChildDeepFactsA.deepChild_runFactsA O T mid.machineData mid.machine_ok
    mid.machine_body (nDecl := 2) (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel) (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (mid_hkidP O hR0) (mid_hkidW O hR0) (mid_hsep O hR0) entry
    (fun _ _ hA' => mid_closesA O T hA' (Tools.ShippingReflectCtx.MachineDefines.ctx hR0)) h

set_option maxHeartbeats 4000000 in
/-- **`outsCheck` of the SERVED `mid`, every depth**; PREMISE `hierGate y.1 = true` (not derived). -/
theorem mid_outsCheckA (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (n : Nat)
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``mid mid.machineData.shape)
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``cnt cnt.machineData.shape)
    {y : Tools.ShippingChildInv.Res} (h : RealChildA O ``mid y)
    (hg : Sparkle.IR.RefineCheck.hierGate y.1 = true) :
    Tools.ShippingDesignSVBack.outsCheck (childMap y.2.modules) n (checkedOptimize y.1) = true := by
  have hcl : ∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context),
      Tools.ShippingMachineEntry.MachineCloses mc mref cc cref ``cnt cnt.machineData.shape :=
    fun mc cc => cnt.machine_closes mc _ cc _
  exact Tools.ShippingSeqChildDeepFactsA.deepChild_outsCheckA O T mid.machineData mid.machine_ok
    mid.machine_body (nDecl := 2) (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel) (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (fun k hk y' hy' => by
      rw [mid_insts_cnt k hk] at hy'
      exact Tools.ShippingParentRunFactsA.leaf_real_kidAA O cnt.machineData cnt.machine_ok cnt.machine_body
        (by decide) (by decide) (by decide) (by decide) hR0 hcl hy')
    (fun k hk y' hy' => by
      rw [mid_insts_cnt k hk] at hy'
      exact Tools.ShippingParentRunFactsA.leaf_real_kidRA O cnt.machineData cnt.machine_ok cnt.machine_body
        (by decide) (by decide) hR0 hcl hy')
    n (mid_hsep O hR0) entry
    (fun _ _ hA' => mid_closesA O T hA' (Tools.ShippingReflectCtx.MachineDefines.ctx hR0)) h hg

set_option maxHeartbeats 4000000 in
/-- **`designCheck` of the SERVED `mid`, every depth** (no check premise). -/
theorem mid_designCheckA (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (n : Nat)
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``mid mid.machineData.shape)
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``cnt cnt.machineData.shape)
    {y : Tools.ShippingChildInv.Res} (h : RealChildA O ``mid y) :
    Tools.ShippingDesignSV.designCheck (childMap y.2.modules) n (checkedOptimize y.1) = true := by
  have hcl : ∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context),
      Tools.ShippingMachineEntry.MachineCloses mc mref cc cref ``cnt cnt.machineData.shape :=
    fun mc cc => cnt.machine_closes mc _ cc _
  have hon : ∀ o ∈ cnt.machineData.shape.layout.outs, Sparkle.Backend.Verilog.sanitizeName o.name = o.name :=
    fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (Tests.Compiler.KidsPassLeafTest.cnt_outs_clean o ho)
  have hdw : Tools.ShippingPortWidthsPure.declWidths cnt.machineData = [1] := by first | decide | decide +kernel
  exact Tools.ShippingSeqChildDeepFactsA.deepChild_designCheckA O T mid.machineData mid.machine_ok
    mid.machine_body (nDecl := 2) (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel) (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (mid_hkidP O hR0) (mid_hkidW O hR0)
    (fun k hk y' hy' => by
      rw [mid_insts_cnt k hk] at hy'
      exact Tools.ShippingParentDesignFA.leaf_real_portsInA O cnt.machineData cnt.machine_ok cnt.machine_body
        (nDecl := cnt.machineData.nIn) (by decide) (by decide) rfl (by decide) (by decide) hR0 hcl hon (by decide) hy')
    (kidIns := fun _ => [1]) mid_callArgs
    (fun k hk y' hy' j q hq => by
      rw [mid_insts_cnt k hk] at hy'
      obtain ⟨wd, h1, h2⟩ := Tools.ShippingParentDesignFA.leaf_real_inWidthsA O cnt.machineData cnt.machine_ok
        cnt.machine_body (nDecl := cnt.machineData.nIn) (by decide) (by decide) rfl (by decide) (by decide) hR0 hcl hy' j q hq
      rw [hdw] at h1
      exact ⟨wd, h1, h2⟩)
    (fun k hk y' hy' => by
      rw [mid_insts_cnt k hk] at hy'
      exact Tools.ShippingParentDesignFA.leaf_real_clkA O cnt.machineData cnt.machine_ok cnt.machine_body
        (nDecl := cnt.machineData.nIn) (by decide) (by decide) rfl (by decide) (by decide) hR0 hcl hy')
    (fun k hk y' hy' => by
      rw [mid_insts_cnt k hk] at hy'
      exact Tools.ShippingParentDesignFA.leaf_real_kidK_regA O cnt.machineData cnt.machine_ok cnt.machine_body
        (nDecl := cnt.machineData.nIn) (by decide) (by decide) rfl (by decide) (by decide) (by decide) hR0 hcl hon (by decide) hy')
    (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (mid_outChars o ho)) mid_outScalar n
    (mid_hsep O hR0) entry
    (fun _ _ hA' => mid_closesA O T hA' (Tools.ShippingReflectCtx.MachineDefines.ctx hR0)) h

end

open Lean Elab Command Meta Term in
open Tests.Compiler.ChildVertAuditTest in
run_cmd Lean.Elab.Command.liftTermElabM do
  for nm in [``mid_runFactsA, ``mid_outsCheckA, ``mid_designCheckA] do
    stdAxioms nm
  let cl ← depClosure ``mid_designCheckA
  for must in [``Tools.ShippingSeqChildDeepFactsA.deepChild_designCheckA, ``Tools.ShippingSeqChildDeepConsumerA.hsep_of_leaf_kids,
      ``Tools.ShippingParentDesignFA.core_designCheck_ranFA, ``mid_closesA] do
    unless cl.contains must do throwError "SR3o AUDIT FAILED: {must} not in the closure of mid_designCheckA"
  let bad := cl.toList.filter fun c =>
    [`Tools.ShippingChildInv.ChildBnd, `Tools.ShippingChildInv.StartV].any (·.isPrefixOf c)
  unless bad.isEmpty do throwError "SR3o AUDIT FAILED: old boundary in closure: {bad}"
  logInfo m!"SR3o: mid_runFactsA / mid_outsCheckA / mid_designCheckA axioms standard, no old boundary"

#print axioms mid_runFactsA
#print axioms mid_outsCheckA
#print axioms mid_designCheckA

end Tests.Compiler.SeqDeepMidFactsTest
