import Tools.Prototype.DGenProv
import Tools.ShippingGen5ReadKindsU5
import Tools.ShippingGen5ReadKindsU6
import Tools.ShippingGen5ReadKindsU7
import Tools.ShippingGen5Env
import Tools.ShippingStRefCorrespondence
set_option autoImplicit false
-- NOT BUILT: (header to be synced by a comment-only commit after a successful build). Freeze: scripts/gen5/DG_READKINDS_U8_FREEZE.md. No sorry / axiom / native_decide.

/-! # DG-READKINDS U8 (freeze scripts/gen5/DG_READKINDS_U8_FREEZE.md)

U8a-0 `runsTo_det` (thin alias of the existing `Tools.ShippingStRefCorrespondence.runsTo_det`; not re-proved),
U8a `readMachine_rootFields` (`ReadRoot ∧ ReadFields` for ONE `ci`/`env`/`w1`/`w2`, witnesses identified by `runsTo_det`),
U8d `readMachine_gates` (the two gate-miss conjuncts of `MachineDefines` from a successful `allowGate = false` run),
U8e `machineDefines_of_readMachine` (CONDITIONAL on `hall`, the DG-ENV premise: intermediate, not a supply).
Not claimed: `hall` supplied, real-run tie, `hstore`, `GateDefines`, `srcDom`, `ls`/`outs`/`nexts`, hq, `Expr.equal_sound`, coverage, FG.
`hX` is absent from U8e only because `MachineDefines` quantifies over the same `declName`; this is not a real-run tie. -/
namespace Tools.ShippingGen5ReadKindsU8
open Lean Meta
open Sparkle.Compiler.Elab
open Tools.ShippingEntrySoundness
open Tools.ShippingMachineCommand Tools.ShippingMachineEntry
open Tools.Prototype.DGenProv
open Tools.ShippingGen5ReadKinds Tools.ShippingGen5ReadKindsU5
open Tools.ShippingGen5ReadKindsU6 Tools.ShippingGen5ReadKindsU7
open Tools.ShippingChildInv

theorem runsTo_det {α : Type} {m : MetaM α} {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld}
    {a b : α} {w' w'' : Void IO.RealWorld}
    (h1 : RunsTo m mctx mref cctx cref w a w') (h2 : RunsTo m mctx mref cctx cref w b w'') :
    a = b ∧ w' = w'' :=
  Tools.ShippingStRefCorrespondence.runsTo_det h1 h2

theorem readMachine_rootFields {declName : Lean.Name} {allowGate : Bool}
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (h : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w') :
    ∃ ci env w1 w2, RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w env w1 ∧
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 ∧
      ReadRoot ci env r ∧ ReadFields ci env r := by
  obtain ⟨ci, env, w1, w2, he, hc, hroot⟩ := readMachine_root h
  obtain ⟨ci', env', v1, v2, he', hc', _, hfields⟩ := readMachine_fields h
  obtain ⟨hev, hw1⟩ := runsTo_det he he'
  subst hev
  subst hw1
  obtain ⟨hcv, hw2⟩ := runsTo_det hc hc'
  subst hcv
  subst hw2
  exact ⟨ci, env, w1, w2, he, hc, hroot, hfields⟩

theorem readMachine_gates {declName : Lean.Name}
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (h : RunsTo (readMachine declName false) mctx mref cctx cref w r w') :
    ∃ ci env w1 w2, RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w env w1 ∧
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 ∧
      certifiedShape? false [] (GenEntry ci env) = none ∧
      mixedCertifiedShape? false [] (GenEntry ci env) (instancePredicate env) = none := by
  unfold readMachine at h
  obtain ⟨env, w1, he, h⟩ := RunsTo.bind h
  obtain ⟨ci, w2, hc, h⟩ := RunsTo.bind h
  refine ⟨ci, env, w1, w2, he, hc, ?_⟩
  have_open h as jp0 hj0
  have H0 : ∀ a w r w', RunsTo (jp0 a) mctx mref cctx cref w r w' →
      (certifiedShape? false [] (GenEntry ci env) = none ∧
        mixedCertifiedShape? false [] (GenEntry ci env) (instancePredicate env) = none) := by
    intro a w r w' h
    subst hj0
    have_open h as senv hse
    subst hse
    have_open h as entry hen
    subst hen
    rcases runs_dcases h with ⟨hn, h⟩ | ⟨_, h⟩
    case inr =>
      obtain ⟨_, _, h1, _⟩ := RunsTo.bind h
      exact (throwError_not_runs _ h1).elim
    refine ⟨?_, ?_⟩
    · cases hcs : certifiedShape? false [] (GenEntry ci env) with
      | none => rfl
      | some v => exact (hn (by simp [GenEntry, hcs] at *)).elim
    · cases hms : mixedCertifiedShape? false [] (GenEntry ci env) (instancePredicate env) with
      | none => rfl
      | some v => exact (hn (by simp [GenEntry, hms] at *)).elim
  rcases runs_dcases h with ⟨_, h⟩ | ⟨_, h⟩
  · obtain ⟨_, _, h1, _⟩ := RunsTo.bind h
    exact (throwError_not_runs _ h1).elim
  · exact H0 _ _ _ _ h

theorem machineDefines_of_readMachine {declName : Lean.Name}
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (hrun : RunsTo (readMachine declName false) mctx mref cctx cref w r w')
    {env₀ : Lean.Environment} (hall : ∀ u, Tools.ShippingGen5Env.ReadsAt env₀ cref u) :
    Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref declName r.shape := by
  obtain ⟨ci, env, w1, w2, he, hc, hg1, hg2⟩ := readMachine_gates hrun
  obtain ⟨ci', env', v1, v2, he', hc', _, hsh⟩ := readMachine_run hrun
  obtain ⟨hev, hw1⟩ := runsTo_det he he'
  subst hev
  subst hw1
  obtain ⟨hcv, hw2⟩ := runsTo_det hc hc'
  subst hcv
  subst hw2
  have hci : env₀.find? declName = some ci := Tools.ShippingGen5Env.ci_of_readsAt hc (hall w1)
  obtain ⟨_, p1, p2, p3⟩ := Tools.ShippingGen5Env.envR_of_readsAt he (hall w)
  unfold GenEntry at hg1 hg2 hsh
  rw [p1, p2, p3] at hg1 hg2 hsh
  exact Tools.ShippingGen5Env.machineDefines_of_readsAll hall hci hg1 hg2 hsh

end Tools.ShippingGen5ReadKindsU8
