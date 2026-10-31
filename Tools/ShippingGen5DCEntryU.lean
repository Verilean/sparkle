import Tools.ShippingGen5DCEntryT
import Tools.ShippingGen5DCEntryN
import Tools.ShippingGen5DCEntryW
import Tools.ShippingParentDesignA
import Tools.ShippingRanABridge
import Tools.ShippingServedRealA
set_option autoImplicit false
-- U-CORENR, scripts/gen5/DC_CONNECT_CORENR_FREEZE.md §3 (freeze 28f2627c approved). NOT BUILT (agent incremental build only; clean build is the coder's).

/-! # DC-CONNECT U-CORENR: `NoRawBelow` and `hlk` for a REAL core run

CONDITIONAL on `MachineDefines`, `MachineClosesAtA`, `Start`, `insts ≠ []`, `instFields = []`. Does not supply those, the leaf case,
(a3), `TopShips` on `D'`, `EntryWitness`/`ReflectsAll`, `Post`; is not FG. -/

namespace Tools.ShippingGen5DCEntryU

theorem noRawBelow_of_coreRun
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {L : Tools.ShippingGen2.Laws mref cref} {mctx : Lean.Meta.Context} {cctx : Lean.Core.Context}
    {w w1 : Void IO.RealWorld} {declName : Lean.Name}
    {raw : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (d : Tools.ShippingMachineAuto.MachineData)
    (hS : Tools.ShippingGen2.Start L mctx cctx w)
    (hr : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1)
    (hdef : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref declName d.shape)
    (hcl : Tools.ShippingChildRunAKids.MachineClosesAtA (mref := mref) (cref := cref) L.O mctx cctx declName d.shape)
    (hins : d.shape.insts ≠ []) (hf : d.shape.instFields = []) :
    ∀ k : Nat, Tools.ShippingGen5DCEntryR.NoRawBelow D raw.name k raw := by
  obtain ⟨hA, hj0⟩ := hS
  have taken := Tools.ShippingServedRealA.machineRunJQC_of_closesA L.O hA hr hdef hcl hj0.1 (Or.inl rfl)
  have ranA := Tools.ShippingRanABridge.machineRanA_of_runJQC L.O hA L.T taken
  obtain ⟨_, _, _, _, _, _, _, _, hcl', _⟩ :=
    Tools.ShippingParentDesignA.core_closeInstsA L.O d hins hf ranA
  exact Tools.ShippingGen5DCEntryS.noRawBelow_of_closeInsts hcl'

theorem hlk_of_postEntry {b raw : Sparkle.IR.AST.Module} {D D' : Sparkle.IR.AST.Design}
    (h : Tools.ShippingGen5DCEntryD.PostEntry b raw D D') :
    ∀ mn : String, mn ≠ raw.name →
      Sparkle.IR.Machine.moduleByName D'.modules mn = Sparkle.IR.Machine.moduleByName D.modules mn :=
  fun _ hne => (Tools.ShippingGen5DCEntryN.postEntry_lookup_ne h hne).1

theorem coreRun_transport
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {L : Tools.ShippingGen2.Laws mref cref} {mctx : Lean.Meta.Context} {cctx : Lean.Core.Context}
    {w w1 : Void IO.RealWorld} {declName : Lean.Name}
    {b raw : Sparkle.IR.AST.Module} {D D' : Sparkle.IR.AST.Design}
    (d : Tools.ShippingMachineAuto.MachineData)
    (hS : Tools.ShippingGen2.Start L mctx cctx w)
    (hr : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : Tools.ShippingGen5DCEntryD.PostEntry b raw D D')
    (hdef : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref declName d.shape)
    (hcl : Tools.ShippingChildRunAKids.MachineClosesAtA (mref := mref) (cref := cref) L.O mctx cctx declName d.shape)
    (hins : d.shape.insts ≠ []) (hf : d.shape.instFields = [])
    (n : Nat) (we : Sparkle.IR.Semantics.WEnv)
    (seed : Nat → (String → Nat) → Sparkle.IR.Semantics.Env) (T : Nat)
    (s : Tools.ShippingHierStateG.KState (Tools.ShippingHierStateG.KT n)) :
    Tools.ShippingHierStateG.runModuleTG
        (Tools.ShippingHierStateG.KSn (Tools.ShippingMachineLinked.childMap D'.modules) n) we
        (Tools.ShippingMachineLinked.childMap D'.modules) raw.body seed T s =
      Tools.ShippingHierStateG.runModuleTG
        (Tools.ShippingHierStateG.KSn (Tools.ShippingMachineLinked.childMap D.modules) n) we
        (Tools.ShippingMachineLinked.childMap D.modules) raw.body seed T s :=
  Tools.ShippingGen5DCEntryT.runModuleTG_transport (hlk_of_postEntry hpost) n raw we seed T s
    (noRawBelow_of_coreRun d hS hr hdef hcl hins hf (n + 1))

end Tools.ShippingGen5DCEntryU
