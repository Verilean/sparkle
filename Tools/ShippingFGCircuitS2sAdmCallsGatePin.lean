import Tools.ShippingCallsGatePin
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
import Tools.ShippingFGCircuitS2sAdmCallsGateA
-- FG circuit pilot S2s4: SELECTIVE port of ShippingCallsGatePin.lean onto the context-predicate bundles (only the declarations that mention RefLawsAOps/AdmCtx/Laws/... or an already-ported name; the rest is taken from the imported original); rename-only script scripts/s2s_port2.py (suffix X, `AdmCtx O.quiet` -> `O.adm`). No sorry/axiom/native_decide/TRUSTED/law.
-- BUILT (unit CN2): cn2g exit 0 (Tools.ShippingCallsGatePin); axioms standard.
-- No `sorry`, no `axiom`, no `native_decide`, no new law / field.

/-! # Unit CN2, step 1: `callsPureA_of_gateKids_pin` (INTERMEDIATE lemma, not a final theorem)

`SameCalleeChildren shape children` : two calls with the SAME callee have the SAME child entry.
`callsPureA_of_gateKids_pin` is `callsPureA_of_gateKids` (CA) with `hnodup` REPLACED by the
hypothesis `hpin : ∀ children, ChildrenRealA O shape children → SameCalleeChildren shape children`.

LABEL: `hpin` is exactly what is missing. It is NOT provable from `ChildrenRealA` (a history of past
runs; two `RealChildA` of one callee are not known equal). This lemma only pins down the missing fact;
it does NOT replace `hnodup` in any final theorem. -/

namespace Tools.ShippingCallsGatePin
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData Tools.ShippingMachineCloses
open Tools.ShippingMixedEntrySoundness
open Tools.ShippingCallsShape Tools.ShippingCallsRun Tools.ShippingCallsAssembly
open Tools.ShippingGateChildComb Tools.ShippingChildInv Tools.ShippingRankRun
open Tools.ShippingInlineSoundness (EntryDefines)
open Tools.ShippingCallsGate
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Tools.ShippingChildInvA
open Tools.ShippingChildFresh Tools.ShippingChildCacheA Tools.ShippingChildRunAKids
open Tools.ShippingCallsCloseA Tools.ShippingCallsGateA

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- **`CallsPureAX` with the pin as a hypothesis of the one-output branch**: the same statement as
`CallsPureAX`, but the one-output conjunct may assume `SameCalleeChildren shape children`. Delivered
by `closeInstsM_runPX` (`Tools/ShippingCallsGatePinned.lean`), so it is NOT an extra premise of a final theorem. -/
def CallsPurePX (O : RefLawsAOpsX MkRefd mref cref) (declName : Name) (shape : MachineShape) : Prop :=
  ∀ {tenv : Lean.Environment}, ∀ (b : Bool) t d₀ t' children,
    MReturns (synthesizeMixedCertified
      (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b) declName
      shape.binders shape.body) (t, d₀) →
    Sparkle.IR.Machine.closeLets shape.layout.lets t = some t' →
    ChildrenRealAX O shape children →
    (shape.instFields = [] → SameCalleeChildren shape children →
      (Sparkle.IR.Machine.closeInsts (machNIn shape) shape.insts.length
        shape.layout.slots.length (t.inputs.map (·.name)) (shape.insts.map (·.2.1)) children
        (Sparkle.IR.Machine.closeMachine shape.layout t', d₀)).isSome = true) ∧
    (shape.instFields ≠ [] → MemChildren shape children →
      (Sparkle.IR.Machine.closeInstsG (machNIn shape) shape.insts.length
        shape.layout.slots.length (t.inputs.map (·.name)) (shape.insts.map (·.2.1))
        shape.instFields children
        (Sparkle.IR.Machine.closeMachine shape.layout t', d₀)).isSome = true)


set_option maxHeartbeats 1000000 in
/-- `callsPureA_of_gateKidsX` with `hnodup` replaced by `SameCalleeChildren` as a hypothesis of the
children list (inside `CallsPurePX`). The pin is NOT proved here. -/
theorem callsPureP_of_gateKidsX (O : RefLawsAOpsX MkRefd mref cref) {declName : Name}
    (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hS : d.gateCallsOk nDecl = true)
    (nk : Nat → Nat)
    (hnomemO : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true)
    (hkid : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChildAX O (d.shape.insts[k]).1 y → ChildIface (d.shape.insts[k]).1 (nk k) y.1 y.2)
    (hargsN : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      nk k = (d.shape.insts[k]).2.1.length)
    (hsep : ∀ c ∈ d.shape.insts.map (·.1), ∀ c' ∈ d.shape.insts.map (·.1),
      (Sparkle.IR.ModuleName.ofDecl c) = (Sparkle.IR.ModuleName.ofDecl c') → c = c')
    (hparent : ∀ c ∈ d.shape.insts, (Sparkle.IR.ModuleName.ofDecl c.1) ≠ (Sparkle.IR.ModuleName.ofDecl declName))
    (hfresh : ∀ (k : Nat) (hk : k < d.shape.insts.length), ∀ o ∈ d.shape.layout.outs,
      o.name ≠ s!"inst{k}_{(Sparkle.IR.ModuleName.ofDecl (d.shape.insts[k]).1)}") :
    CallsPurePX O declName d.shape := by
  have hf : d.shape.instFields = [] := by
    simp only [MachineData.gateCallsOk, Bool.and_eq_true, List.isEmpty_iff] at hS
    exact hS.2
  intro tenv b t d₀ t' children run hcl hreal
  refine ⟨fun _ hsame => ?_, fun hne => absurd hf hne⟩
  obtain ⟨hlenC, hall⟩ := hreal
  have hfull : ∀ (k : Nat) (c : Res), children[k]? = some c → ∃ hk : k < d.shape.insts.length,
      ChildIface (d.shape.insts[k]).1 (nk k) c.1 c.2 := by
    intro k c hc
    have hk : k < d.shape.insts.length := by
      rw [← hlenC]
      exact (List.getElem?_eq_some_iff.mp hc).1
    obtain ⟨y, hy, hor⟩ := hall k hk
    rw [hc] at hy
    cases hy
    rcases hor with hmem | hre
    · rw [Tools.ShippingChildInv.notag_at hnomemO hk] at hmem
      cases hmem
    · exact ⟨hk, hkid k hk c hre⟩
  refine closeInsts_of_run d ok hbody hS run hcl hlenC ?_ ?_ ?_
  · intro k c hc
    obtain ⟨hk, full⟩ := hfull k c hc
    obtain ⟨fcomb, flen, fname, fdes⟩ := full
    refine ⟨fcomb, fdes, ?_, ?_⟩
    · intro args hargs
      obtain ⟨x, hx, rfl⟩ := inst_get hargs
      have hx' : d.shape.insts[k] = x := by
        have := List.getElem?_eq_getElem hk
        rw [hx] at this
        exact (Option.some.inj this).symm
      rw [flen, hargsN k hk, hx']
    · rw [fname]
      exact hparent _ (List.getElem_mem hk)
  · intro a ha c hc' hn
    obtain ⟨i, hi, hai⟩ := List.getElem_of_mem ha
    obtain ⟨j, hj, hcj⟩ := List.getElem_of_mem hc'
    obtain ⟨hki, fi⟩ := hfull i a (by rw [List.getElem?_eq_getElem hi, hai])
    obtain ⟨hkj, fj⟩ := hfull j c (by rw [List.getElem?_eq_getElem hj, hcj])
    rw [fi.2.2.1, fj.2.2.1] at hn
    have hni : (d.shape.insts.map (·.1))[i]? = some (d.shape.insts[i]).1 := by simp [hki]
    have hnj : (d.shape.insts.map (·.1))[j]? = some (d.shape.insts[j]).1 := by simp [hkj]
    have hcc := hsep _ (List.mem_of_getElem? hni) _ (List.mem_of_getElem? hnj) hn
    have := hsame i j hki hkj hcc
    rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj, hai, hcj] at this
    have hac := Option.some.inj this
    first | exact hac | (subst hac; rfl) | exact congrArg Prod.fst hac
  · intro k c hc o ho
    obtain ⟨hk, full⟩ := hfull k c hc
    rw [full.2.2.1]
    exact hfresh k hk o ho


/-- **INTERMEDIATE**: `callsPureA_of_gateKidsX` with `hnodup` replaced by the pin hypothesis `hpin`
(`SameCalleeChildren` for every `ChildrenRealAX` children list). `hpin` is NOT proved here. -/
theorem callsPureA_of_gateKids_pinX (O : RefLawsAOpsX MkRefd mref cref) {declName : Name}
    (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hS : d.gateCallsOk nDecl = true)
    (nk : Nat → Nat)
    (hnomemO : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true)
    (hkid : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChildAX O (d.shape.insts[k]).1 y → ChildIface (d.shape.insts[k]).1 (nk k) y.1 y.2)
    (hargsN : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      nk k = (d.shape.insts[k]).2.1.length)
    (hsep : ∀ c ∈ d.shape.insts.map (·.1), ∀ c' ∈ d.shape.insts.map (·.1),
      (Sparkle.IR.ModuleName.ofDecl c) = (Sparkle.IR.ModuleName.ofDecl c') → c = c')
    (hpin : ∀ children, ChildrenRealAX O d.shape children → SameCalleeChildren d.shape children)
    (hparent : ∀ c ∈ d.shape.insts, (Sparkle.IR.ModuleName.ofDecl c.1) ≠ (Sparkle.IR.ModuleName.ofDecl declName))
    (hfresh : ∀ (k : Nat) (hk : k < d.shape.insts.length), ∀ o ∈ d.shape.layout.outs,
      o.name ≠ s!"inst{k}_{(Sparkle.IR.ModuleName.ofDecl (d.shape.insts[k]).1)}") :
    CallsPureAX O declName d.shape := by
  intro tenv b t d₀ t' children run hcl hreal
  have h := callsPureP_of_gateKidsX O d ok hbody hS nk hnomemO hkid hargsN hsep hparent hfresh
    b t d₀ t' children run hcl hreal
  exact ⟨fun hf => h.1 hf (hpin children hreal), h.2⟩

end Tools.ShippingCallsGatePin

#print axioms Tools.ShippingCallsGatePin.callsPureP_of_gateKidsX
#print axioms Tools.ShippingCallsGatePin.callsPureA_of_gateKids_pinX

