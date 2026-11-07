import Tools.ShippingFGCircuitRunLocal
import Tools.ShippingFGCircuitS2sAdmLawsX
import Tools.ShippingFGCircuitS2sAdmS2hHist
import Tools.ShippingFGCircuitS2sAdmS2hHist2
import Tools.ShippingChildRunAKids
import Tools.ShippingChildComposeC
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
import Tools.ShippingFGCircuitS2sAdmChildProjFieldA
import Tools.ShippingFGCircuitS2sAdmChildRunA
import Tools.ShippingFGCircuitS2sAdmChildRunAKids
import Tools.ShippingFGCircuitS2sAdmChildTeleCP
import Tools.ShippingFGCircuitS2sAdmChildTeleLocalA
import Tools.ShippingFGCircuitS2sAdmChildTranslateA
import Tools.ShippingFGCircuitS2sAdmChildTranslatePathA
import Tools.ShippingFGCircuitS2sAdmChildVCA
import Tools.ShippingFGCircuitS2sAdmChildVertA
import Tools.ShippingFGCircuitS2sAdmChildWalkA
import Tools.ShippingFGCircuitS2sAdmKWalk
import Tools.ShippingFGCircuitS2sAdmServedRealA
-- FG circuit pilot S2s4: SELECTIVE port of ShippingFGCircuitRunLocal.lean onto the context-predicate bundles (only the declarations that mention RefLawsAOps/AdmCtx/Laws/... or an already-ported name; the rest is taken from the imported original); rename-only script scripts/s2s_port2.py (suffix X, `AdmCtx O.quiet` -> `O.adm`). No sorry/axiom/native_decide/TRUSTED/law.
set_option autoImplicit false
-- FG circuit pilot S1f, unit 1: `MachineDefinesRun`, the run-local successor of `MachineDefines`. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED.

/-! # `MachineDefinesRun`: the machine boundary of ONE core run

`MachineDefines mctx mref cctx cref X shape` (Tools/ShippingMachineEntry.lean) is read at three worlds `w1 w5 w7` that are not connected to any run: it is `∀` over every `getConstInfo` / `getEnv` result of every world.
`MachineDefinesRun` asks the same three facts only of the `ci` / `envR` / `envR'` that the given core run `hr` actually reads:

* `ci` and `envR` are the values the run's `synthesizeFromConst` was called with (`RunsTo (synthesizeFromConst … ci envR) w3 (M, D) w4`, inside `RunsTo (synthesizeCombinationalCore X …) w (M, D) w'`);
* `envR'` is the result of the `getEnv` that `synthesizeFromConst` performs FIRST, at its own start world `w3` (`synthesizeFromConst_machine_invR`: the world is tied, unlike `synthesizeFromConst_machine_invA`).

`MachineDefines` implies `MachineDefinesRun` (`machineDefinesRun_of_defines`); the converse is not claimed. -/
namespace Tools.ShippingFGCircuitRunLocal
open Lean Meta
open Tools.ShippingEntrySoundness
open Tools.ShippingMachineEntry
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv Tools.ShippingChildBndInit Tools.ShippingChildBndCore Tools.ShippingChildInvA Tools.ShippingChildFresh
open Tools.ShippingChildVCA Tools.ShippingChildCacheA Tools.ShippingChildVertA Tools.ShippingChildCoreC Tools.ShippingChildRunA
open Tools.ShippingServedRealA Tools.ShippingChildRunAKids Tools.ShippingMachineClose Tools.ShippingMixedEntrySoundness Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingMachineClose (Zip₂)

/-- the global form implies the run-local one -/
theorem machineDefinesRun_of_definesX {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {declName : Name} {shape : MachineShape} {w w' : Void IO.RealWorld}
    {M : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design} (h : MachineDefines mctx mref cctx cref declName shape) :
    MachineDefinesRun mctx mref cctx cref declName shape w M D w' := by
  intro _ logProf envR ci w1 w2 w3 w4 w5 w6 hgetX henv _
  obtain ⟨a, b, _⟩ := h _ _ _ _ _ _ _ _ _ hgetX henv henv
  exact ⟨a, b, fun envR' w8 henv' => (h _ _ _ _ _ _ _ _ _ hgetX henv henv').2.2⟩

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}


/-- `synthesizeFromConst_machine_invAX` with the `getEnv` tied to the start world `w` of the body (copy of the proof; only the statement is strengthened) -/
theorem synthesizeFromConst_machine_invRX (O : RefLawsAOpsX MkRefd mref cref)
    (hA : O.adm mctx cctx) {tenv : Lean.Environment}
    {logProf : String → IO Unit} {declName : Name} {n : Nat}
    {ci : ConstantInfo} {isInst : Lean.Expr → Bool} {m : Sparkle.IR.AST.Module}
    {d : Sparkle.IR.AST.Design} {w w' : Void IO.RealWorld}
    (old : certifiedShape? false [] ci = none)
    (miss : mixedCertifiedShape? false [] ci isInst = none) (hw : JQCX O n w)
    (hr : RunsTo (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) logProf
      declName [] false true ci isInst) mctx mref cctx cref w (m, d) w') :
    ∃ (envR : Environment) (w6 : Void IO.RealWorld),
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w envR w6 ∧
      ∀ shape, machineShape? false [] ci (structEnv envR) = some shape →
        ∃ r w7 w8, RunsTo (synthesizeMachineCertified
            (fun e hint top named => translateExprToWire tenv e hint top named) logProf declName
            shape) mctx mref cctx cref w7 r w8 ∧ JQCX O n w7 ∧
          ∀ res, r = some res → res = (m, d) := by
  unfold synthesizeFromConst at hr
  simp only [↓reduceIte, old, miss, Bool.not_false, Bool.and_self, List.isEmpty_nil] at hr
  obtain ⟨envR, w1, henv, hr⟩ := RunsTo.bind hr
  have hw1 := triple_runsX (keeps_iff.mp (keepsA_framedX O hA (stableA_JQCX O n) FramedA.env)) hw henv
  obtain ⟨mach, w2, hp, hr⟩ := RunsTo.bind hr
  obtain ⟨hm, rfl⟩ := RunsTo.pure_world hp
  subst hm
  refine ⟨envR, _, henv, ?_⟩
  intro shape hs
  rw [hs] at hr
  dsimp only at hr
  obtain ⟨r, w3, hmach, hr⟩ := RunsTo.bind hr
  refine ⟨r, _, _, hmach, hw1, ?_⟩
  intro res hres
  subst hres
  dsimp only at hr
  have hr := hr.mreturns
  peel_bind hr
  peel_bind hr
  exact (MReturns.pure hr).symm


/-- `machine_run_of_coreAX` from the run-local boundary -/
theorem machine_run_of_coreRX (O : RefLawsAOpsX MkRefd mref cref) (hA : O.adm mctx cctx)
    {declName : Name} {shape : MachineShape} {D : Nat}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, d) w')
    (entry : MachineDefinesRun mctx mref cctx cref declName shape w m d w')
    (hw : JQ O.quiet D w) (hc : D = 0 ∨ CacheInvAX O (cv w)) :
    ∃ (tenv : Lean.Environment) (b : Bool) (r : Option Res) (w9 w10 : Void IO.RealWorld),
      RunsTo (synthesizeMachineCertified
        (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b) declName shape)
        mctx mref cctx cref w9 r w10 ∧ JQCX O (D + 1) w9 ∧
      ∀ res, r = some res → res = (m, d) := by
  obtain ⟨b, envR, ci, w1, w2, w3, w4, w5, w6, get, henv, run, hw3⟩ :=
    core_reads_invAX O hA hw hc hr
  obtain ⟨old, miss, _⟩ := entry hr _ _ _ _ _ _ _ _ _ get henv run
  obtain ⟨envR', w8, henv', hmach⟩ := synthesizeFromConst_machine_invRX O hA old miss hw3 run
  obtain ⟨_, _, hshape⟩ := entry hr _ _ _ _ _ _ _ _ _ get henv run
  obtain ⟨r, w9, w10, hrun, hw9, hres⟩ := hmach shape (hshape _ _ henv')
  exact ⟨_, b, r, w9, w10, hrun, hw9, hres⟩


theorem machineRunJQC_of_closesRX (O : RefLawsAOpsX MkRefd mref cref) (hA : O.adm mctx cctx)
    {declName : Name} {shape : MachineShape} {D : Nat}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, d) w')
    (entry : MachineDefinesRun mctx mref cctx cref declName shape w m d w')
    (closes : MachineClosesAtAX (mref := mref) (cref := cref) O mctx cctx declName shape)
    (hw : JQ O.quiet D w) (hc : D = 0 ∨ CacheInvAX O (cv w)) :
    MachineRunJQC O mctx cctx (D + 1) declName shape m d := by
  obtain ⟨tenv, b, r, w9, w10, hrun, hw9, hres⟩ := machine_run_of_coreRX O hA hr entry hw hc
  have hne := closes b (D + 1) w9 r w10 hw9 (by omega) hrun
  cases r with
  | none => exact absurd rfl hne
  | some res =>
    have := hres res rfl
    subst this
    exact ⟨tenv, b, w9, w10, hrun, hw9⟩


/-- `synthesizeCombinationalCore_machine_sound` from the run-local boundary (copy of the proof) -/
theorem synthesizeCombinationalCore_machine_soundRX {declName : Name}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    {shape : MachineShape} {bsIn slotBs letBs : List (Name × MixedGateBinder)}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, d) w')
    (entry : MachineDefinesRun mctx mref cctx cref declName shape w m d w')
    (closes : MachineCloses mctx mref cctx cref declName shape)
    (hbs : shape.binders = bsIn ++ slotBs ++ letBs)
    (hlets : shape.layout.lets = letBs.length)
    (positive : PositiveBinders shape.binders)
    (slotKinds : ∀ b ∈ slotBs, b.2 ≠ .domain)
    (letKinds : ∀ b ∈ letBs, b.2 ≠ .domain)
    (layW : Zip₂ (fun (f : SlotField) (b : Name × MixedGateBinder) => f.width = machWidth b.2)
      shape.layout.slots slotBs)
    (outsOk : ∀ o ∈ shape.layout.outs, 0 < o.width ∧ outNameOk o.name = true)
    (outsNodup : (shape.layout.outs.map (·.name)).Nodup) :
    MachinePreserves declName shape bsIn slotBs letBs m d := by
  obtain ⟨logProf, envR, ci, w1, w2, w3, w4, w5, w6, get, henv, run⟩ :=
    synthesizeCombinationalCore_reads hr
  obtain ⟨old, miss, hshape⟩ := entry hr _ _ _ _ _ _ _ _ _ get henv run
  obtain ⟨envR', w8, henv', hmach⟩ := synthesizeFromConst_machineR old miss run
  obtain ⟨r, w9, w10, hrun, hres⟩ := hmach shape (hshape _ _ henv')
  have hne := closes logProf _ _ _ hrun
  cases r with
  | none => exact absurd rfl hne
  | some res =>
    have := hres res rfl
    subst this
    exact synthesizeMachineCertified_sound hrun.mreturns hbs hlets positive slotKinds letKinds
      layW outsOk outsNodup

end Tools.ShippingFGCircuitRunLocal

#print axioms Tools.ShippingFGCircuitRunLocal.machineRunJQC_of_closesRX
#print axioms Tools.ShippingFGCircuitRunLocal.synthesizeCombinationalCore_machine_soundRX

