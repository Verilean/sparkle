import Tools.ShippingCallsGateA
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

/-- Two calls of the same callee carry the same child entry. -/
def SameCalleeChildren (shape : MachineShape) (children : List Res) : Prop :=
  ∀ (k₁ k₂ : Nat) (h₁ : k₁ < shape.insts.length) (h₂ : k₂ < shape.insts.length),
    (shape.insts[k₁]).1 = (shape.insts[k₂]).1 → children[k₁]? = children[k₂]?

/-- **`CallsPureA` with the pin as a hypothesis of the one-output branch**: the same statement as
`CallsPureA`, but the one-output conjunct may assume `SameCalleeChildren shape children`. Delivered
by `closeInstsM_runP` (`Tools/ShippingCallsGatePinned.lean`), so it is NOT an extra premise of a final theorem. -/
def CallsPureP (O : RefLawsAOps MkRefd mref cref) (declName : Name) (shape : MachineShape) : Prop :=
  ∀ {tenv : Lean.Environment}, ∀ (b : Bool) t d₀ t' children,
    MReturns (synthesizeMixedCertified
      (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b) declName
      shape.binders shape.body) (t, d₀) →
    Sparkle.IR.Machine.closeLets shape.layout.lets t = some t' →
    ChildrenRealA O shape children →
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
/-- `callsPureA_of_gateKids` with `hnodup` replaced by `SameCalleeChildren` as a hypothesis of the
children list (inside `CallsPureP`). The pin is NOT proved here. -/
theorem callsPureP_of_gateKids (O : RefLawsAOps MkRefd mref cref) {declName : Name}
    (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hS : d.gateCallsOk nDecl = true)
    (nk : Nat → Nat)
    (hnomemO : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true)
    (hkid : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChildA O (d.shape.insts[k]).1 y → ChildIface (d.shape.insts[k]).1 (nk k) y.1 y.2)
    (hargsN : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      nk k = (d.shape.insts[k]).2.1.length)
    (hsep : ∀ c ∈ d.shape.insts.map (·.1), ∀ c' ∈ d.shape.insts.map (·.1),
      (Sparkle.IR.ModuleName.ofDecl c) = (Sparkle.IR.ModuleName.ofDecl c') → c = c')
    (hparent : ∀ c ∈ d.shape.insts, (Sparkle.IR.ModuleName.ofDecl c.1) ≠ (Sparkle.IR.ModuleName.ofDecl declName))
    (hfresh : ∀ (k : Nat) (hk : k < d.shape.insts.length), ∀ o ∈ d.shape.layout.outs,
      o.name ≠ s!"inst{k}_{(Sparkle.IR.ModuleName.ofDecl (d.shape.insts[k]).1)}") :
    CallsPureP O declName d.shape := by
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

/-- **INTERMEDIATE**: `callsPureA_of_gateKids` with `hnodup` replaced by the pin hypothesis `hpin`
(`SameCalleeChildren` for every `ChildrenRealA` children list). `hpin` is NOT proved here. -/
theorem callsPureA_of_gateKids_pin (O : RefLawsAOps MkRefd mref cref) {declName : Name}
    (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hS : d.gateCallsOk nDecl = true)
    (nk : Nat → Nat)
    (hnomemO : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true)
    (hkid : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChildA O (d.shape.insts[k]).1 y → ChildIface (d.shape.insts[k]).1 (nk k) y.1 y.2)
    (hargsN : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      nk k = (d.shape.insts[k]).2.1.length)
    (hsep : ∀ c ∈ d.shape.insts.map (·.1), ∀ c' ∈ d.shape.insts.map (·.1),
      (Sparkle.IR.ModuleName.ofDecl c) = (Sparkle.IR.ModuleName.ofDecl c') → c = c')
    (hpin : ∀ children, ChildrenRealA O d.shape children → SameCalleeChildren d.shape children)
    (hparent : ∀ c ∈ d.shape.insts, (Sparkle.IR.ModuleName.ofDecl c.1) ≠ (Sparkle.IR.ModuleName.ofDecl declName))
    (hfresh : ∀ (k : Nat) (hk : k < d.shape.insts.length), ∀ o ∈ d.shape.layout.outs,
      o.name ≠ s!"inst{k}_{(Sparkle.IR.ModuleName.ofDecl (d.shape.insts[k]).1)}") :
    CallsPureA O declName d.shape := by
  intro tenv b t d₀ t' children run hcl hreal
  have h := callsPureP_of_gateKids O d ok hbody hS nk hnomemO hkid hargsN hsep hparent hfresh
    b t d₀ t' children run hcl hreal
  exact ⟨fun hf => h.1 hf (hpin children hreal), h.2⟩

end Tools.ShippingCallsGatePin

#print axioms Tools.ShippingCallsGatePin.callsPureP_of_gateKids
#print axioms Tools.ShippingCallsGatePin.callsPureA_of_gateKids_pin
