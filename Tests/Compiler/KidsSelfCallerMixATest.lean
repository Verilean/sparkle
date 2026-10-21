import Tests.Compiler.ParentDesignCheckATest
import Tools.ShippingKidsSelfA
-- BUILT (unit SR3b, par/u-sr3b): sb3 exit 0 (sb1 exit 1: missing opens; sb2 exit 1: audit premise count). In-test audit THROWS on failure. See REPORT-SR3b.md.
-- SCOPE (binding): facts about the checks of the shipped module of `callerMix` (two distinct one-output gate
-- children) on the NEW boundary; NOT a parent semantic-equivalence head and NOT the endpoint
-- `machine_design_svH_full` (OPEN: its semantic part still takes `ChildBnd`). Not runtime fit.

/-! # Unit SR3b: regression example — `core_kids_selfA` / `core_kidsPass_deepA` on `callerMix`

Supplies BOTH the closing (`callerMix_closesA`, from `machineClosesAtA_of_gateKids`, restricted to distinct callees)
and the child checks `hkidK` (from `pick_kidKA` / `pickD_kidKA` = `gate_real_kidKA`, one per `RealChildA` child), so the
concrete statements have no per-child premise.  PREMISES that remain: `O`, `hA`, `T : RefLawsATele`, `hw : JQ O.quiet 0 w`,
the run, `MachineDefines`, one `EntryDefines` per callee, the post-processing disjunction.
`hkidM` (`core_kidsMaskedN_topA`): NOT supplied — `callerMix` has `instFields = []` (no `hfne`) so that theorem does not
apply to it, and no gate-child `outsMaskedN` theorem exists in the tree (OPEN).
`RealChildA` is a history of past synthesis results. -/

namespace Tests.Compiler.KidsSelfCallerMixATest
open Sparkle.Tests.Compiler.ShippingPremiseEvalTest
open Sparkle.Tests.Compiler.ShippingMachineInstTest
open Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildCacheA Tools.ShippingChildVCA
open Tools.ShippingInlineSoundness (EntryDefines)
open Tests.Compiler.ParentDesignCheckATest

set_option maxHeartbeats 0 in
/-- `hkidK` of `core_kidsPass_deepA` for `callerMix`: supplied from `pick_kidKA` / `pickD_kidKA`. -/
theorem callerMix_hkidK
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref)
    (hR0 : EntryDefines mctx mref cctx cref ``pick pick.gateValue)
    (hR1 : EntryDefines mctx mref cctx cref ``pickD pickD.gateValue) (n : Nat) :
    ∀ (k : Nat) (hk : k < callerMix.machineData.shape.insts.length) (y : Tools.ShippingChildInv.Res),
      RealChildA O (callerMix.machineData.shape.insts[k]).1 y →
      ∀ ms : List Sparkle.IR.AST.Module,
        Sparkle.IR.Machine.moduleByName ms y.1.name = some y.1 →
        (∀ g ∈ y.2.modules, Sparkle.IR.Machine.moduleByName ms g.name = some g) →
        Tools.ShippingChecksDesign.kidCheck (Tools.ShippingMachineLinked.childMap ms) n y.1 = true ∧
          ∀ g ∈ y.2.modules, Tools.ShippingChecksDesign.kidCheck (Tools.ShippingMachineLinked.childMap ms) n g = true := by
  intro k hk y hy ms _ _
  have key : (∀ (C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)) (n : Nat),
        Tools.ShippingChecksDesign.kidCheck C n y.1 = true) ∧
      ∀ g ∈ y.2.modules,
        ∀ (C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)) (n : Nat),
          Tools.ShippingChecksDesign.kidCheck C n g = true := by
    rcases callerMix.oneout_entries k hk with ⟨hc, hki, hres⟩ | ⟨hc, hki, hres⟩
    · (rw [hc] at hy; exact pick_kidKA O hR0 hy)
    · (rw [hc] at hy; exact pickD_kidKA O hR1 hy)
  exact ⟨key.1 _ n, fun g hg => key.2 g hg _ n⟩

set_option maxHeartbeats 0 in
/-- The conclusion of `core_kids_selfA` at `callerMix` (a `def`, so that the outer-premise audit does not enter it). -/
def KidsSelfConcl {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (D : Sparkle.IR.AST.Design) : Prop :=
    ∀ g ∈ D.modules, ∃ (k : Nat) (hk : k < callerMix.machineData.shape.insts.length) (y : Tools.ShippingChildInv.Res),
      RealChildA O (callerMix.machineData.shape.insts[k]).1 y ∧ (g = y.1 ∨ g ∈ y.2.modules) ∧
      Sparkle.IR.Machine.moduleByName D.modules y.1.name = some y.1 ∧
      ∀ g2 ∈ y.2.modules, Sparkle.IR.Machine.moduleByName D.modules g2.name = some g2

set_option maxHeartbeats 0 in
/-- `core_kids_selfA` for `callerMix`: closing from `callerMix_closesA`, no per-child premise. -/
theorem callerMix_kids_selfA
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w w1 : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx) (hw : JQ O.quiet 0 w)
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``callerMix [] false)
      mctx mref cctx cref w (raw, D) w1)
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``callerMix
      callerMix.machineData.shape)
    (hR0 : EntryDefines mctx mref cctx cref ``pick pick.gateValue)
    (hR1 : EntryDefines mctx mref cctx cref ``pickD pickD.gateValue) :
    KidsSelfConcl O D :=
  Tools.ShippingKidsSelfA.core_kids_selfA O hA T callerMix.machineData callerMix.machine_ok
    callerMix.machine_body callerMix.oneout_callsOk callerMix.oneout_slotLen callerMix.oneout_domB
    callerMix.oneout_insts callerMix.oneout_nomem hcore entry (callerMix_closesA O T hA hR0 hR1) hw (Or.inl rfl)

set_option maxHeartbeats 0 in
/-- `core_kidsPass_deepA` for `callerMix`: closing from `callerMix_closesA`, `hkidK` from `callerMix_hkidK`. -/
theorem callerMix_kidsPass_deepA
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx) (hw : JQ O.quiet 0 w)
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``callerMix [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``callerMix
      callerMix.machineData.shape)
    (hR0 : EntryDefines mctx mref cctx cref ``pick pick.gateValue)
    (hR1 : EntryDefines mctx mref cctx cref ``pickD pickD.gateValue) :
    Tools.ShippingDesignSV.kidsPass (Tools.ShippingMachineLinked.childMap D.modules)
      (Tools.ShippingChecksDesign.kidCheck (Tools.ShippingMachineLinked.childMap D.modules) 0)
      (Sparkle.IR.OptCheck.checkedOptimize b).body = true :=
  Tools.ShippingKidsSelfA.core_kidsPass_deepA O hA T callerMix.machineData callerMix.machine_ok
    callerMix.machine_body callerMix.oneout_callsOk callerMix.oneout_slotLen callerMix.oneout_domB
    callerMix.oneout_insts (Tools.ShippingReaderOutsInv.outTy_of_core hcore entry) callerMix.oneout_nomem 0
    (callerMix_hkidK O hR0 hR1 0) hcore entry (callerMix_closesA O T hA hR0 hR1) hw (Or.inl rfl) hpost

open Lean Elab Command Meta Term in
open Tests.Compiler.ChildVertAuditTest in
run_cmd Lean.Elab.Command.liftTermElabM do
  for (n, k) in [(``callerMix_kids_selfA, 7), (``callerMix_kidsPass_deepA, 8)] do
    auditParentA n k
  -- no per-child binder left: the only premises are the named ones (auditParentA checks the Prop heads)

#print axioms callerMix_kids_selfA
#print axioms callerMix_kidsPass_deepA

end Tests.Compiler.KidsSelfCallerMixATest
