import Tools.ShippingTopShareRun
import Tools.ShippingParentRanA
-- BUILT (unit SR11): b1 exit 0 (qbuild build Tools.ShippingTopShareRan); see REPORT-SR11.md for the final-SHA rebuild.
-- No `sorry`, no `axiom`, no `native_decide`, no new RefLawsAOps/RefLawsATele field, no existing statement changed.
-- `machineRanA_start0`: `Tools.ShippingParentRanA.machineRanA_main` with the closing premise `MachineClosesAtA` (all worlds)
-- replaced by the START-world form `MachineClosesAtStart0` (SR10 derives it for `topshare`, `topshare_closes0`), at the outermost
-- start world `JQC O 0 w`.  The proof is `core_run_tracked0'` followed by the same `synthesizeMachineCertified_runsA` step.
-- WORDING: `MachineRanA` is the run information of the machine synthesis (a history of that run); the children of the closing
-- are `ChildrenRealA O` (a history of past synthesis results), not semantic correctness in the current environment.

namespace Tools.ShippingTopShareRan
open Lean Meta
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry Tools.ShippingTopShareRun
open Sparkle.Compiler.Elab
open Tools.ShippingChildBndCore Tools.ShippingChildInvA Tools.ShippingChildVCA Tools.ShippingChildCacheA
open Tools.ShippingChildDepthC Tools.ShippingChildRunA Tools.ShippingChildRunAKids Tools.ShippingChildRunAMain
open Tools.ShippingChildComposeC Tools.ShippingChildFresh Tools.ShippingParentRanA

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- **`MachineRanA` from a returning core run at the outermost start world `JQC O 0 w`**, from the START-world closing
`MachineClosesAtStart0` (premises: `O`, `hA`, `T` through `BodyStepC`/`htr`, `MachineDefines`, `MachineClosesAtStart0`). -/
theorem machineRanA_start0 (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (T : RefLawsATele O.quiet mref cref) {c : Name} {shape : MachineShape}
    {w w' : Void IO.RealWorld} {M : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w')
    (entry : MachineDefines mctx mref cctx cref c shape)
    (closes : MachineClosesAtStart0 (mref := mref) (cref := cref) O mctx cctx c shape)
    (hw : JQC O 0 w) :
    MachineRanA O mctx cctx c shape M D := by
  obtain ⟨tenv, b, w9, w10, hrun, hw9, -, -⟩ := core_run_tracked0' O hA entry closes hw hr
  obtain ⟨t, t', d₀, run, hcl, hmt⟩ :=
    synthesizeMachineCertified_runsA O (bodyStepC_of_tele O T) hA (htr_of_tele O hA T 0 tenv) hw9 hrun
  exact ⟨tenv, b, w9, w10, hrun, t, t', d₀, run, hcl, hmt⟩

end Tools.ShippingTopShareRan

#print axioms Tools.ShippingTopShareRan.machineRanA_start0
