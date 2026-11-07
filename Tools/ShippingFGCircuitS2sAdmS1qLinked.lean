import Tools.ShippingFGCircuitS1qLinked
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
import Tools.ShippingFGCircuitS2sAdmParentRanA
import Tools.ShippingFGCircuitS2sAdmParentTailsA
import Tools.ShippingFGCircuitS2sAdmParentDesignA
-- FG circuit pilot S2s4: SELECTIVE port of ShippingFGCircuitS1qLinked.lean onto the context-predicate bundles (only the declarations that mention RefLawsAOps/AdmCtx/Laws/... or an already-ported name; the rest is taken from the imported original); rename-only script scripts/s2s_port2.py (suffix X, `AdmCtx O.quiet` -> `O.adm`). No sorry/axiom/native_decide/TRUSTED/law.
set_option autoImplicit false
-- FG circuit pilot S1q, unit 1: the profile-free entry `synthesizeCombinationalCoreOff` split as `coreHeadOff` / `coreRestOff`, its linked chain, and the machine boundary on it.  No `sorry`, no `axiom`, no `native_decide`, no TRUSTED, no new law.

/-! # S1q-1: the chain of the profile-free entry

`synthesizeCombinationalCoreOff` (Sparkle/Compiler/Elab.lean) is `synthesizeCombinationalCoreWith … declName [] false true` with `profile := false` fixed by the definition: no `IO.getEnv "SPARKLE_PROFILE"`, no profile log.
`coreHeadOff` / `coreRestOff` are the mirror of `coreHead` / `coreRest` without those two (`CoreSaved.profile := false`).  The existing `coreHead`, `coreRest`, `core_*`, `MachineDefinesLinked`, … are NOT changed; the `…Off` theorems below are copies of the existing proofs under the renaming
`synthesizeCombinationalCore → synthesizeCombinationalCoreOff`, `coreHead → coreHeadOff`, `core_chain → core_chainOff`, `profLogIO s.profile → (fun _ => pure ())`. -/
namespace Tools.ShippingFGCircuitS1qLinked
open Lean Meta Sparkle.Compiler.Elab Sparkle.IR.AST
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingEntryReadsLinked (CoreSaved envAt bind_assoc_fn ite_bind_fn)
open Tools.ShippingMachineOutcomeA3 (coreFinally RunsTo.try_finally')

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- the chain of the profile-free entry: `w —head→ w1 —getConstInfo→ w2 —getEnv→ w3 —body→ w4 —finally→ w'` -/
theorem core_chainOffX {declName : Name} {w w' : Void IO.RealWorld} {M : Sparkle.IR.AST.Module} {D : Design}
    (hr : RunsTo (synthesizeCombinationalCoreOff declName) mctx mref cctx cref w (M, D) w') :
    ∃ (s : CoreSaved) (w1 : Void IO.RealWorld) (envR : Environment) (ci : ConstantInfo)
      (w2 w3 w4 : Void IO.RealWorld),
      RunsTo (coreHeadOff declName) mctx mref cctx cref w s w1 ∧
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 ∧
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w2 envR w3 ∧
      RunsTo (synthesizeFromConst (fun e h t n => translateExprToWire envR e h t n) (fun _ => pure ())
        declName [] false true
        (entryConst true false [] ci (Sparkle.Compiler.Elab.instancePredicate envR)
          (userInliner envR) (structEnv envR))
        (Sparkle.Compiler.Elab.instancePredicate envR))
        mctx mref cctx cref w3 (M, D) w4 ∧
      RunsTo (coreFinally s.depth s.sf s.sw s.sl s.sp s.sc s.ss s.sg) mctx mref cctx cref w4 () w' := by
  obtain ⟨s, w1, hh, hk⟩ := core_splitOff hr
  unfold coreRestOff at hk
  obtain ⟨w4, u, hx, hfin⟩ := RunsTo.try_finally' hk
  cases u
  obtain ⟨ci, w2, hgetX, hx⟩ := RunsTo.bind hx
  obtain ⟨envR, w3, henv, hx⟩ := RunsTo.bind hx
  rcases RunsTo.ite hx with hx | hx
  · exact (Tools.ShippingEntrySoundness.RunsTo.throwError_false hx).elim
  exact ⟨s, w1, envR, ci, w2, w3, w4, hh, hgetX, henv, hx, hfin⟩

section Consumers
open Tools.ShippingMachineEntry Tools.ShippingChildInv Tools.ShippingChildBndInit Tools.ShippingChildBndCore Tools.ShippingChildInvA Tools.ShippingChildFresh
open Tools.ShippingChildVCA Tools.ShippingChildCacheA Tools.ShippingChildVertA Tools.ShippingChildCoreC Tools.ShippingChildRunA
open Tools.ShippingServedRealA Tools.ShippingChildRunAKids Tools.ShippingMachineClose Tools.ShippingMixedEntrySoundness Sparkle.IR.Machine
open Tools.ShippingMachineClose (Zip₂)
open Tools.ShippingFGCircuitRunLocal
open Sparkle.IR.Builder Tools.ShippingChildTranslateA Tools.ShippingChildDepthC Tools.ShippingChildFrontCP Tools.ShippingChildRunAMain Tools.ShippingChildComposeC
open Tools.ShippingMachineOutcomeA (legacyTail)


/-- **(RR1)** The core head establishes `JQCX (D+1)` at its end world (the peel of `core_reads_linkA`,
ShippingMachineOutcomeA.lean, on `coreHead`). -/
theorem coreHeadOff_jqcAX (O : RefLawsAOpsX MkRefd mref cref) (hA : O.adm mctx cctx) {X : Name} {D : Nat}
    {w w1 : Void IO.RealWorld} {s : Tools.ShippingEntryReadsLinked.CoreSaved}
    (hw : JQ O.quiet D w) (hc : D = 0 ∨ CacheInvAX O (cv w))
    (hh : RunsTo (coreHeadOff X) mctx mref cctx cref w s w1) :
    JQCX O (D + 1) w1 := by
  have h := hh
  unfold coreHeadOff at h
  by_cases h0 : D = 0
  · subst h0
    obtain ⟨d, wc, s3, h⟩ := RunsTo.bind h
    have hd := triple_runsX (tripleA_depthGetX O hA (stableA_JQ _ 0)) hw s3
    have hdD : d = 0 := hd.2.trans hd.1.2.2
    have hw := hd.1
    subst hdD
    rcases RunsTo.ite h with h | h
    · obtain ⟨_, _, ht, _⟩ := RunsTo.bind h
      exact (throwError_not_runs _ ht).elim
    simp only [↓reduceIte, beq_self_eq_true] at h
    peelPX h; peelPX h; peelPX h; peelPX h; peelPX h; peelPX h; peelPX h
    peelFX O hA (stableA_JQ _ 0) h hw; peelFX O hA (stableA_JQ _ 0) h hw
    peelFX O hA (stableA_JQ _ 0) h hw; peelFX O hA (stableA_JQ _ 0) h hw
    obtain ⟨_, _, step, h⟩ := RunsTo.bind h
    have hw := triple_runsX (tripleC_clearX O hA 0 (R := fun _ _ => False)) hw step
    clear step
    peelFX O hA (stableA_JQCX O 0) h hw; peelFX O hA (stableA_JQCX O 0) h hw
    peelFX O hA (stableA_JQCX O 0) h hw; peelFX O hA (stableA_JQCX O 0) h hw
    peelFX O hA (stableA_JQCX O 0) h hw; peelFX O hA (stableA_JQCX O 0) h hw
    peelFX O hA (stableA_JQCX O 0) h hw
    obtain ⟨_, _, step, h⟩ := RunsTo.bind h
    have hw := triple_runsX (tripleC_depthSetX O hA 0 (0 + 1) (R := fun _ _ => False)) hw step
    clear step
    obtain ⟨-, rfl⟩ := RunsTo.pure_world h
    exact hw
  · replace hw : JQCX O D w := ⟨hw, hc.resolve_left h0⟩
    obtain ⟨d, wc, s3, h⟩ := RunsTo.bind h
    have hd := triple_runsX (tripleA_depthGetX O hA (stableA_JQCX O D)) hw s3
    have hdD : d = D := hd.2.trans hd.1.1.2.2
    have hw := hd.1
    subst hdD
    rcases RunsTo.ite h with h | h
    · obtain ⟨_, _, ht, _⟩ := RunsTo.bind h
      exact (throwError_not_runs _ ht).elim
    have h0' : ¬ ((d == 0) = true) := by simpa using h0
    simp only [h0', Bool.false_eq_true, ↓reduceIte] at h
    peelFX O hA (stableA_JQCX O d) h hw; peelFX O hA (stableA_JQCX O d) h hw
    peelFX O hA (stableA_JQCX O d) h hw; peelFX O hA (stableA_JQCX O d) h hw
    peelFX O hA (stableA_JQCX O d) h hw; peelFX O hA (stableA_JQCX O d) h hw
    peelFX O hA (stableA_JQCX O d) h hw
    peelFX O hA (stableA_JQCX O d) h hw; peelFX O hA (stableA_JQCX O d) h hw
    peelFX O hA (stableA_JQCX O d) h hw; peelFX O hA (stableA_JQCX O d) h hw
    peelFX O hA (stableA_JQCX O d) h hw; peelFX O hA (stableA_JQCX O d) h hw
    peelFX O hA (stableA_JQCX O d) h hw
    obtain ⟨_, _, step, h⟩ := RunsTo.bind h
    have hw := triple_runsX (tripleC_depthSetX O hA d (d + 1) (R := fun _ _ => False)) hw step
    clear step
    obtain ⟨-, rfl⟩ := RunsTo.pure_world h
    exact hw



/-- `machine_run_of_coreRX` on the linked chain -/
theorem machine_run_of_coreCOffX (O : RefLawsAOpsX MkRefd mref cref) (hA : O.adm mctx cctx)
    {declName : Name} {shape : MachineShape} {D : Nat}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCoreOff declName) mctx mref cctx cref w (m, d) w')
    (entry : MachineDefinesLinkedOff mctx mref cctx cref declName shape w m d w')
    (hw : JQ O.quiet D w) (hc : D = 0 ∨ CacheInvAX O (cv w)) :
    ∃ (tenv : Lean.Environment) (b : Bool) (r : Option Res) (w9 w10 : Void IO.RealWorld),
      RunsTo (synthesizeMachineCertified
        (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b) declName shape)
        mctx mref cctx cref w9 r w10 ∧ JQCX O (D + 1) w9 ∧
      ∀ res, r = some res → res = (m, d) := by
  obtain ⟨s, w1, envR, ci, w2, w3, w4, hh, hgetX, henv, hbody, -⟩ := core_chainOffX hr
  have hw1 := coreHeadOff_jqcAX O hA hw hc hh
  have hw2 := triple_runsX (keeps_iff.mp (keepsA_framedX O hA (stableA_JQCX O (D + 1)) (FramedA.constInfo _))) hw1 hgetX
  have hw3 := triple_runsX (keeps_iff.mp (keepsA_framedX O hA (stableA_JQCX O (D + 1)) FramedA.env)) hw2 henv
  obtain ⟨old, miss, hshape⟩ := entry hr s w1 w2 w3 w4 envR ci hh hgetX henv hbody
  obtain ⟨envR', w8, henv', hmach⟩ := synthesizeFromConst_machine_invRX O hA old miss hw3 hbody
  obtain ⟨r, w9, w10, hrun, hw9, hres⟩ := hmach shape (hshape _ _ henv')
  exact ⟨_, false, r, w9, w10, hrun, hw9, hres⟩


theorem machineRunJQC_of_closesCOffX (O : RefLawsAOpsX MkRefd mref cref) (hA : O.adm mctx cctx)
    {declName : Name} {shape : MachineShape} {D : Nat}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCoreOff declName) mctx mref cctx cref w (m, d) w')
    (entry : MachineDefinesLinkedOff mctx mref cctx cref declName shape w m d w')
    (closes : MachineClosesAtAX (mref := mref) (cref := cref) O mctx cctx declName shape)
    (hw : JQ O.quiet D w) (hc : D = 0 ∨ CacheInvAX O (cv w)) :
    MachineRunJQCX O mctx cctx (D + 1) declName shape m d := by
  obtain ⟨tenv, b, r, w9, w10, hrun, hw9, hres⟩ := machine_run_of_coreCOffX O hA hr entry hw hc
  have hne := closes b (D + 1) w9 r w10 hw9 (by omega) hrun
  cases r with
  | none => exact absurd rfl hne
  | some res =>
    have := hres res rfl
    subst this
    exact ⟨tenv, b, w9, w10, hrun, hw9⟩


/-- `synthesizeCombinationalCore_machine_soundRX` on the linked chain of the profile-free entry -/
theorem synthesizeCombinationalCore_machine_soundCOffX {declName : Name}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    {shape : MachineShape} {bsIn slotBs letBs : List (Name × MixedGateBinder)}
    (hr : RunsTo (synthesizeCombinationalCoreOff declName) mctx mref cctx cref w (m, d) w')
    (entry : MachineDefinesLinkedOff mctx mref cctx cref declName shape w m d w')
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
  obtain ⟨s, w1, envR, ci, w2, w3, w4, hh, hgetX, henv, hbody, -⟩ := core_chainOffX hr
  obtain ⟨old, miss, hshape⟩ := entry hr s w1 w2 w3 w4 envR ci hh hgetX henv hbody
  obtain ⟨envR', w8, henv', hmach⟩ := synthesizeFromConst_machineR old miss hbody
  obtain ⟨r, w9, w10, hrun, hres⟩ := hmach shape (hshape _ _ henv')
  have hne := closes _ _ _ _ hrun
  cases r with
  | none => exact absurd rfl hne
  | some res =>
    have := hres res rfl
    subst this
    exact synthesizeMachineCertified_sound hrun.mreturns hbs hlets positive slotKinds letKinds
      layW outsOk outsNodup

end Consumers

end Tools.ShippingFGCircuitS1qLinked

#print axioms Tools.ShippingFGCircuitS1qLinked.core_eqOff
#print axioms Tools.ShippingFGCircuitS1qLinked.core_chainOffX
#print axioms Tools.ShippingFGCircuitS1qLinked.coreHeadOff_jqcAX
#print axioms Tools.ShippingFGCircuitS1qLinked.machineRunJQC_of_closesCOffX
#print axioms Tools.ShippingFGCircuitS1qLinked.synthesizeCombinationalCore_machine_soundCOffX

