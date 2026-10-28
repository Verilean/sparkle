import Tools.ShippingServedRealA
import Tools.ShippingParentRanA
-- BUILT (integrator, par/int-r15): int-r15b0 exit 0 (365 jobs; WIP over 17ec8f5d). No `sorry`, no `axiom`, no `native_decide`, no new law / field.

/-! # Bridge: unit SR's `MachineRunJQC` → unit PH's `MachineRanA`

The two definitions are NOT definitionally equal: `MachineRunJQC O mctx cctx n c shape M D`
(Tools/ShippingServedRealA.lean) is "the machine synthesis returned `some (M, D)` from a world in
`JQC O n`"; `MachineRanA O mctx cctx c shape M D` (Tools/ShippingParentRanA.lean) is the same run
together with its decomposition (harness, `closeLets`, closing, `ChildrenRealA` children), and no `JQC`.
`machineRanA_of_runJQC` proves the direction SR → PH at depth `n ≥ 1`, from `O`, `hA`, `T`
(`BodyStepC`/`htr` from `T`, G2), by G's `synthesizeMachineCertified_runsA` — the same step
PH's `machineRanA_main` uses. No closing premise (`MachineClosesAtA`) is needed: the run already
returned `some`. The converse is not claimed (`MachineRanA` carries no `JQC`).
Not runtime fit; `ChildrenRealA` is a history. -/

namespace Tools.ShippingRanABridge
open Lean Meta
open Tools.ShippingEntrySoundness
open Tools.ShippingMachineEntry
open Sparkle.Compiler.Elab
open Tools.ShippingChildBndCore
open Tools.ShippingChildInvA
open Tools.ShippingChildVCA
open Tools.ShippingChildCacheA
open Tools.ShippingChildDepthC
open Tools.ShippingChildRunA
open Tools.ShippingChildRunAKids
open Tools.ShippingChildRunAMain
open Tools.ShippingChildComposeC
open Tools.ShippingChildFresh
open Tools.ShippingChildInv (profLogIO)

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- **SR's run fact gives PH's `MachineRanA`** (depth `D + 1`; premises `O`, `hA`, `T`). -/
theorem machineRanA_of_runJQC (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (T : RefLawsATele O.quiet mref cref) {D : Nat} {c : Name} {shape : MachineShape}
    {M : Sparkle.IR.AST.Module} {Ds : Sparkle.IR.AST.Design}
    (h : Tools.ShippingServedRealA.MachineRunJQC O mctx cctx (D + 1) c shape M Ds) :
    Tools.ShippingParentRanA.MachineRanA O mctx cctx c shape M Ds := by
  obtain ⟨tenv, b, w9, w10, hrun, hw9⟩ := h
  obtain ⟨t, t', d₀, run, hcl, hmt⟩ :=
    synthesizeMachineCertified_runsA O (bodyStepC_of_tele O T) hA
      (htr_of_tele O hA T D tenv) hw9 hrun
  exact ⟨tenv, b, w9, w10, hrun, t, t', d₀, run, hcl, hmt⟩

end Tools.ShippingRanABridge
