import Tools.ShippingParentRanA
import Tools.ShippingFGCircuitS2sAdmLawsX
import Tools.ShippingFGCircuitS2sAdmS2hHist
import Tools.ShippingFGCircuitS2sAdmS2hHist2
import Tools.ShippingFGCircuitS2sAdmChildCacheA
import Tools.ShippingFGCircuitS2sAdmChildCanonKeyA
import Tools.ShippingFGCircuitS2sAdmChildComposeA
import Tools.ShippingFGCircuitS2sAdmChildComposeC
import Tools.ShippingFGCircuitS2sAdmChildCoreC
import Tools.ShippingFGCircuitS2sAdmChildDepthA
import Tools.ShippingFGCircuitS2sAdmChildDepthC
import Tools.ShippingFGCircuitS2sAdmChildFallbackA
import Tools.ShippingFGCircuitS2sAdmChildFrontA
import Tools.ShippingFGCircuitS2sAdmChildFrontCP
import Tools.ShippingFGCircuitS2sAdmChildInvA
import Tools.ShippingFGCircuitS2sAdmChildLegacyCachedA
import Tools.ShippingFGCircuitS2sAdmChildLegacyHandlersA
import Tools.ShippingFGCircuitS2sAdmChildLegacyHelpersA
import Tools.ShippingFGCircuitS2sAdmChildLegacyImplA
import Tools.ShippingFGCircuitS2sAdmChildLegacyTailA
import Tools.ShippingFGCircuitS2sAdmChildMainA
import Tools.ShippingFGCircuitS2sAdmChildPathA
import Tools.ShippingFGCircuitS2sAdmChildPinC
import Tools.ShippingFGCircuitS2sAdmChildProjFieldA
import Tools.ShippingFGCircuitS2sAdmChildRunA
import Tools.ShippingFGCircuitS2sAdmChildRunAKids
import Tools.ShippingFGCircuitS2sAdmChildRunAMain
import Tools.ShippingFGCircuitS2sAdmChildTeleCP
import Tools.ShippingFGCircuitS2sAdmChildTeleLocalA
import Tools.ShippingFGCircuitS2sAdmChildTeleMainA
import Tools.ShippingFGCircuitS2sAdmChildTranslateA
import Tools.ShippingFGCircuitS2sAdmChildTranslatePathA
import Tools.ShippingFGCircuitS2sAdmChildVCA
import Tools.ShippingFGCircuitS2sAdmChildVertA
import Tools.ShippingFGCircuitS2sAdmChildWalkA
import Tools.ShippingFGCircuitS2sAdmKWalk
import Tools.ShippingChildRunAKids
import Tools.ShippingChildComposeC
import Tools.ShippingFGCircuitS2sAdmChildPinC
import Tools.ShippingFGCircuitS2sAdmCallsGatePinned
import Tools.ShippingFGCircuitS2sAdmRunLocal
import Tools.ShippingFGCircuitS2sAdmLinked
import Tools.ShippingFGCircuitS2sAdmRunReads
import Tools.ShippingFGCircuitS2sAdmServedRealA
-- FG circuit pilot S2s4: SELECTIVE port of ShippingParentRanA.lean onto the context-predicate bundles (only the declarations that mention RefLawsAOps/AdmCtx/Laws/... or an already-ported name; the rest is taken from the imported original); rename-only script scripts/s2s_port2.py (suffix X, `AdmCtx O.quiet` -> `O.adm`). No sorry/axiom/native_decide/TRUSTED/law.
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
`ChildrenRealAX`** (new boundary analogue of `MachineRan`, with `synthesizeMachineCertified_runsAX` applied). -/
def MachineRanAX (O : RefLawsAOpsX MkRefd mref cref) (mctx : Meta.Context) (cctx : Core.Context)
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
          ChildrenRealAX O shape children))


/-- **`MachineRanAX` from a returning core run** (premises `O`, `hA`, `T`, start world, `MachineDefines`,
`MachineClosesAtAX`). -/
theorem machineRanA_mainX (O : RefLawsAOpsX MkRefd mref cref) (hA : O.adm mctx cctx)
    (T : RefLawsATeleX O.quiet O.adm mref cref) {c : Name} {shape : MachineShape} {D₀ : Nat}
    {w w' : Void IO.RealWorld} {M : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w')
    (entry : MachineDefines mctx mref cctx cref c shape)
    (closes : MachineClosesAtAX (mref := mref) (cref := cref) O mctx cctx c shape)
    (hw : JQ O.quiet D₀ w) (hc : D₀ = 0 ∨ CacheInvAX O (cv w)) :
    MachineRanAX O mctx cctx c shape M D := by
  obtain ⟨tenv, b, r, w9, w10, hrun, hw9, hres⟩ := machine_run_of_coreAX O hA hr entry hw hc
  have hne := closes b (D₀ + 1) w9 r w10 hw9 (by omega) hrun
  cases r with
  | none => exact absurd rfl hne
  | some res =>
    have := hres res rfl
    subst this
    obtain ⟨t, t', d₀, run, hcl, hmt⟩ :=
      synthesizeMachineCertified_runsAX O (bodyStepC_of_teleX O T) hA
        (htr_of_teleX O hA T D₀ tenv) hw9 hrun
    exact ⟨tenv, b, w9, w10, hrun, t, t', d₀, run, hcl, hmt⟩

end Tools.ShippingParentRanA

