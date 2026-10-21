import Tools.ShippingChildRunAMain
-- BUILT (unit PH, par/u-ph): ph2 exit 0. See REPORT-PH.md.
-- SCOPE (binding): this file proves facts about the checks of the shipped module up to `designCheck = true`
-- (resp. the check statement named below), NOT a parent semantic-equivalence head and NOT the endpoint
-- `machine_design_svH_full` (its semantic part still takes `ChildBnd`: OPEN). Not runtime fit.
-- No `sorry`, no `axiom`, no `native_decide`, no new law / field.

/-! # Unit PH: `MachineRanA` — what the parent-level design chain takes of a returning core run (new boundary)

The old design-level chain of a parent with calls (`ShippingChecksCore.core_kids_facts_ran`,
`ShippingLinkedFresh`, `ShippingClosedTyped`, `ShippingHierGateAny`, `ShippingOneOutFacts`) works from
`Tools.ShippingMachineRan.MachineRan`, which holds an old `InvW`/`DepthPos` witness and then calls
`synthesizeMachineCertified_runs` to obtain `ChildrenReal`.  Here `MachineRanA O` is the SAME run
information with the output of `synthesizeMachineCertified_runsA` already in it: the machine synthesis
returned `some (M, D)`, its harness result / `closeLets` / closing are exposed, and the children of the
closing are `ChildrenRealA O` (a history of past synthesis results, not freshness or semantic
correctness).

* `machineRanA_main`: `MachineRanA` from a returning core run.  Premises: `O`, `hA`, `T : RefLawsATele`
  (only through `BodyStepC`/`htr`, G2), the start world `JQ O.quiet D₀ w` (+ `CacheInvA` if `D₀ ≠ 0`),
  `MachineDefines`, and `MachineClosesAtA` (UNRESOLVED PREMISE: the machine synthesis does not fall back).

Not a runtime-fit proof; `O`, `hA`, `T` are hypotheses. -/

namespace Tools.ShippingParentRanA
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

/-- **The machine synthesis a core run performs returned the run's result, with its children
`ChildrenRealA`** (new boundary analogue of `MachineRan`, with `synthesizeMachineCertified_runsA` applied). -/
def MachineRanA (O : RefLawsAOps MkRefd mref cref) (mctx : Meta.Context) (cctx : Core.Context)
    (c : Name) (shape : MachineShape) (M : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design) : Prop :=
  ∃ (tenv : Lean.Environment) (b : Bool) (w9 w10 : Void IO.RealWorld),
    RunsTo (synthesizeMachineCertified
      (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b) c shape)
      mctx mref cctx cref w9 (some (M, D)) w10 ∧
    ∃ t t' d₀, MReturns (synthesizeMixedCertified
        (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b) c
        shape.binders shape.body) (t, d₀) ∧
      Sparkle.IR.Machine.closeLets shape.layout.lets t = some t' ∧
      ((shape.insts = [] ∧ M = Sparkle.IR.Machine.closeMachine shape.layout t' ∧ D = d₀) ∨
       (shape.insts ≠ [] ∧ ∃ children,
          CloseCalls shape t (Sparkle.IR.Machine.closeMachine shape.layout t') d₀ children M D ∧
          ChildrenRealA O shape children))

/-- **`MachineRanA` from a returning core run** (premises `O`, `hA`, `T`, start world, `MachineDefines`,
`MachineClosesAtA`). -/
theorem machineRanA_main (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (T : RefLawsATele O.quiet mref cref) {c : Name} {shape : MachineShape} {D₀ : Nat}
    {w w' : Void IO.RealWorld} {M : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w')
    (entry : MachineDefines mctx mref cctx cref c shape)
    (closes : MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx c shape)
    (hw : JQ O.quiet D₀ w) (hc : D₀ = 0 ∨ CacheInvA O (cv w)) :
    MachineRanA O mctx cctx c shape M D := by
  obtain ⟨tenv, b, r, w9, w10, hrun, hw9, hres⟩ := machine_run_of_coreA O hA hr entry hw hc
  have hne := closes b (D₀ + 1) w9 r w10 hw9 (by omega) hrun
  cases r with
  | none => exact absurd rfl hne
  | some res =>
    have := hres res rfl
    subst this
    obtain ⟨t, t', d₀, run, hcl, hmt⟩ :=
      synthesizeMachineCertified_runsA O (bodyStepC_of_tele O T) hA
        (htr_of_tele O hA T D₀ tenv) hw9 hrun
    exact ⟨tenv, b, w9, w10, hrun, t, t', d₀, run, hcl, hmt⟩

end Tools.ShippingParentRanA
