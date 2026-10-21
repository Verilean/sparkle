import Tools.ShippingCallsCloseA
import Tools.ShippingCallsGate
-- BUILT (unit CA): ca6 exit 0 (Tools.ShippingCallsGateA); axioms standard.
-- No `sorry`, no `axiom`, no `native_decide`, no new law / field.

/-! # Unit CA, item 4: `CallsPureA` for one-output calls of gate children (distinct callees)

The old boundary discharged `CallsPure` INSIDE `machineClosesAt_of_gateKidsO`
(`Tools/ShippingCallsGate.lean`, from `closeInsts_of_run` and the children's `ChildIface`).
Here the same pure derivation is stated as `CallsPureA` on the new boundary:

* `childFull_of_realA`: a `RealChildA` of a gate declaration has the child-side facts (`gate_child_fullFacts`
  at the child's own run, taken from the `RealChildA.run` witness);
* `callsPureA_of_gateKids`: `CallsPureA O declName d.shape` for one-output gate calls — premises as in the
  old `machineClosesAt_of_gateKidsO`, `hkid` at `RealChildA`, and `hnodup`: the calls name PAIRWISE DISTINCT
  callees;
* `machineClosesAtA_of_gateKids`: with `T`, `MachineClosesAtA`.

NOT covered (OPEN): shapes with two calls of ONE declaration (`callerTwice`, `callerRep`). The old proof gets
"same callee ⇒ same child" from the cache pin (`synthesizeChild_pin`, RefLaws, depth `≠ 0`); there is no
pin on the `JQC` boundary (it would need a pin conjunct through `BodyStepC` / `childKeepsC_all`), so `hnodup`
replaces it and the duplicate-callee shapes remain without a `MachineClosesAtA`.
`ChildrenRealA` is a history, not semantic correctness; nothing here is a runtime-fit proof. -/

namespace Tools.ShippingCallsGateA
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
open Tools.ShippingCallsCloseA

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- **A `RealChildA` of a gate declaration has the child-side facts** (from its own run). -/
theorem childFull_of_realA (O : RefLawsAOps MkRefd mref cref) {c : Name} {y : Res}
    {value dom : Lean.Expr} {bs : List (Name × MixedGateBinder)}
    {kb kv : Nat} {vw : Nat → Nat} {bpos vpos : Nat → Nat} {srt : SType} {e : Term srt}
    (entry : EntryDefines mctx mref cctx cref c value)
    (old : ∀ d : DefinitionVal, d.value = value → certifiedShape? false [] (.defnInfo d) = none)
    (peel : mixedGatePeel value = some (bs,
      quote dom (fun j => inputExpr bs.length (bpos j)) (fun j => inputExpr bs.length (vpos j)) e))
    (he : e.WF kb kv vw)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hv : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits (vw j)))
    (h : RealChildA O c y) : ChildFull c bs y.1 y.2 := by
  cases h with
  | run mctx' cctx' w w' adm cache synth quiet hr =>
    exact gate_child_fullFacts hr (Tools.ShippingReflectCtx.EntryDefines.ctx entry) old peel he hb hv

set_option maxHeartbeats 1000000 in
/-- **`CallsPureA` for one-output calls of gate children with pairwise distinct callees.** -/
theorem callsPureA_of_gateKids (O : RefLawsAOps MkRefd mref cref) {declName : Name}
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
    (hnodup : (d.shape.insts.map (·.1)).Nodup)
    (hparent : ∀ c ∈ d.shape.insts, (Sparkle.IR.ModuleName.ofDecl c.1) ≠ (Sparkle.IR.ModuleName.ofDecl declName))
    (hfresh : ∀ (k : Nat) (hk : k < d.shape.insts.length), ∀ o ∈ d.shape.layout.outs,
      o.name ≠ s!"inst{k}_{(Sparkle.IR.ModuleName.ofDecl (d.shape.insts[k]).1)}") :
    CallsPureA O declName d.shape := by
  have hf : d.shape.instFields = [] := by
    simp only [MachineData.gateCallsOk, Bool.and_eq_true, List.isEmpty_iff] at hS
    exact hS.2
  intro tenv b t d₀ t' children run hcl hreal
  refine ⟨fun _ => ?_, fun hne => absurd hf hne⟩
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
    have hij : i = j := by
      refine Classical.byContradiction fun hne => ?_
      have hlen' : (d.shape.insts.map (·.1)).length = d.shape.insts.length := by simp
      have hpw := List.pairwise_iff_getElem.mp hnodup
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · exact hpw i j (by omega) (by omega) h (by simpa [hki, hkj] using hcc)
      · exact hpw j i (by omega) (by omega) h (by simpa [hki, hkj] using hcc.symm)
    subst hij
    rw [← hai, ← hcj]
  · intro k c hc o ho
    obtain ⟨hk, full⟩ := hfull k c hc
    rw [full.2.2.1]
    exact hfresh k hk o ho

/-- **`MachineClosesAtA` for one-output calls of gate children with distinct callees**, premises
`O`, `hA`, `T` and the data/name conditions of the old `machineClosesAt_of_gateKidsO`. -/
theorem machineClosesAtA_of_gateKids (O : RefLawsAOps MkRefd mref cref)
    (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx) {declName : Name}
    (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (halias : d.letsAliasOk = true)
    {nDecl : Nat} (hS : d.gateCallsOk nDecl = true)
    (nk : Nat → Nat)
    (hnomemO : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true)
    (hkid : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChildA O (d.shape.insts[k]).1 y → ChildIface (d.shape.insts[k]).1 (nk k) y.1 y.2)
    (hargsN : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      nk k = (d.shape.insts[k]).2.1.length)
    (hsep : ∀ c ∈ d.shape.insts.map (·.1), ∀ c' ∈ d.shape.insts.map (·.1),
      (Sparkle.IR.ModuleName.ofDecl c) = (Sparkle.IR.ModuleName.ofDecl c') → c = c')
    (hnodup : (d.shape.insts.map (·.1)).Nodup)
    (hparent : ∀ c ∈ d.shape.insts, (Sparkle.IR.ModuleName.ofDecl c.1) ≠ (Sparkle.IR.ModuleName.ofDecl declName))
    (hfresh : ∀ (k : Nat) (hk : k < d.shape.insts.length), ∀ o ∈ d.shape.layout.outs,
      o.name ≠ s!"inst{k}_{(Sparkle.IR.ModuleName.ofDecl (d.shape.insts[k]).1)}") :
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx declName d.shape :=
  machineClosesAtA_of_tele O T hA
    (letsClose_of_data d ok hbody halias mctx mref cctx cref)
    (callsPureA_of_gateKids O d ok hbody hS nk hnomemO hkid hargsN hsep hnodup hparent hfresh)

end Tools.ShippingCallsGateA

#print axioms Tools.ShippingCallsGateA.callsPureA_of_gateKids
#print axioms Tools.ShippingCallsGateA.machineClosesAtA_of_gateKids
