import Tools.ShippingCallsGatePinned
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
import Tools.ShippingFGCircuitS2sAdmCallsGatePin
-- FG circuit pilot S2s4: SELECTIVE port of ShippingCallsGatePinned.lean onto the context-predicate bundles (only the declarations that mention RefLawsAOps/AdmCtx/Laws/... or an already-ported name; the rest is taken from the imported original); rename-only script scripts/s2s_port2.py (suffix X, `AdmCtx O.quiet` -> `O.adm`). No sorry/axiom/native_decide/TRUSTED/law.
-- BUILT (unit CN2): cn2j exit 0 (Tools.ShippingCallsGatePinned); axioms standard.
-- No `sorry`, no `axiom`, no `native_decide`, no new law / field.

/-! # Unit CN2, step 2: `SameCalleeChildren` DELIVERED by the closing run, `hnodup` dropped

* `mapM_loop_pin` / `closeInstsM_runP`: a returning run of the one-output closing from a `JQC O (D+1)`
  world returns children satisfying `ChildrenRealA` AND `SameCalleeChildren`. Proof: each
  `synthesizeChild` step is `synthesizeChild_pinned` (PinC) — it keeps every earlier `(callee, child)`
  as a cache entry and leaves the callee mapped to the child it returned; so two calls of one callee
  see the same cache entry at the end. NOT from `RealChildA`/types.
* `machineClosesAtA_of_pure_pin`, `machineClosesAtA_of_tele_pin`: `MachineClosesAtA` from `CallsPureP`.
* `machineClosesAtA_of_gateKids'`: `machineClosesAtA_of_gateKids` WITHOUT `hnodup`
  (repeated callees allowed).
Premises: `O`, `hA`, `T` (as `machineClosesAtA_of_tele`); no pin hypothesis.
`ChildrenRealA` is a history; not a runtime-fit proof. -/

namespace Tools.ShippingCallsGatePinned
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
open Tools.ShippingClosesSplit
open Tools.ShippingChildBndInit Tools.ShippingChildBndCore
open Tools.ShippingChildInvA Tools.ShippingChildVCA Tools.ShippingChildDepthC
open Tools.ShippingChildFresh Tools.ShippingChildCacheA Tools.ShippingChildRunAKids
open Tools.ShippingChildCoreC Tools.ShippingChildPinC Tools.ShippingChildRunA
open Tools.ShippingCallsCloseA Tools.ShippingCallsGateA Tools.ShippingCallsGatePin
open Tools.ShippingChildTranslateA Tools.ShippingChildFrontCP

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- The `mapM` loop of `synthesizeChild` keeps the pin and records every callee at its child. -/
theorem mapM_loop_pinX (O : RefLawsAOpsX MkRefd mref cref) (T : RefLawsATeleX O.quiet O.adm mref cref)
    (hA : O.adm mctx cctx) {D : Nat} (hD : 1 ≤ D) {α : Type} (key : α → Name)
    (f : α → MetaM Res) (hf : ∀ x, f x = synthesizeChild (key x)) :
    ∀ (l : List α) (acc : List Res) (L : List (Name × Res)) (r : List Res)
      (w w' : Void IO.RealWorld), JQPX O D L w →
      RunsTo (List.mapM.loop f l acc) mctx mref cctx cref w r w' →
      ∃ ys, r = acc.reverse ++ ys ∧ ys.length = l.length ∧
        (∀ k (hk : k < l.length), ∃ y, ys[k]? = some y ∧ RealChildAX O (key l[k]) y ∧
          (cv w').get? (key l[k]) = some y) ∧ JQPX O D L w'
  | [], acc, L, r, w, w', hp, h => by
    obtain ⟨rfl, rfl⟩ := RunsTo.pure_world h
    exact ⟨[], by simp, rfl, fun k hk => absurd hk (Nat.not_lt_zero k), hp⟩
  | x :: xs, acc, L, r, w, w', hp, h => by
    obtain ⟨y, w1, hy, h⟩ := RunsTo.bind h
    rw [hf] at hy
    obtain ⟨hreal, hjq, hgetX⟩ := triple_runsX (synthesizeChild_pinnedX O T hA hD L (key x)) hp hy
    have hp1 : JQPX O D ((key x, y) :: L) w1 := by
      refine ⟨hjq.1, fun p hp' => ?_⟩
      rcases List.mem_cons.mp hp' with rfl | hm
      · exact hgetX
      · exact hjq.2 p hm
    obtain ⟨ys, hr, hlen, hk, hp'⟩ :=
      mapM_loop_pinX O T hA hD key f hf xs (y :: acc) ((key x, y) :: L) r w1 w' hp1 h
    refine ⟨y :: ys, by simp [hr], by simp [hlen], fun k hk' => ?_, ⟨hp'.1, fun p hm => hp'.2 p
      (List.mem_cons_of_mem _ hm)⟩⟩
    cases k with
    | zero => exact ⟨y, rfl, hreal, hp'.2 (key x, y) (List.mem_cons_self ..)⟩
    | succ k =>
      obtain ⟨z, hz, hrz, hcz⟩ := hk k (by simpa using hk')
      exact ⟨z, by simpa using hz, by simpa using hrz, by simpa using hcz⟩


/-- **A run of the one-output closing from a `JQCX O (D+1)` world delivers `SameCalleeChildren`.** -/
theorem closeInstsM_runPX (O : RefLawsAOpsX MkRefd mref cref) (T : RefLawsATeleX O.quiet O.adm mref cref)
    (hA : O.adm mctx cctx) {D : Nat}
    {shape : MachineShape} {t m₀ : Sparkle.IR.AST.Module} {d₀ : Sparkle.IR.AST.Design}
    {r : Option (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)} {w w' : Void IO.RealWorld}
    (hw : JQCX O (D + 1) w)
    (hr : RunsTo (closeInstsM shape t m₀ d₀) mctx mref cctx cref w r w') :
    ∃ children, r = Sparkle.IR.Machine.closeInsts (machNIn shape) shape.insts.length
        shape.layout.slots.length (t.inputs.map (·.name)) (shape.insts.map (·.2.1))
        children (m₀, d₀) ∧
      ChildrenRealAX O shape children ∧ SameCalleeChildren shape children := by
  unfold closeInstsM at hr
  obtain ⟨synth?, w1, hgetX, hr⟩ := RunsTo.bind hr
  obtain ⟨hw1, rfl⟩ := triple_runsX (tripleC_synthReadX O hA (D + 1)) hw hgetX
  dsimp only at hr
  obtain ⟨children, w2, hch, hr⟩ := RunsTo.bind hr
  obtain ⟨heq, rfl⟩ := RunsTo.pure_world hr
  obtain ⟨ys, hys, hlen, hk, _⟩ := mapM_loop_pinX O T hA (Nat.succ_le_succ (Nat.zero_le D))
    (fun (x : Name × List Nat × MixedGateBinder) => x.1)
    (fun (x : Name × List Nat × MixedGateBinder) => synthesizeChild x.1) (fun _ => rfl)
    shape.insts [] [] children w1 w' ⟨hw1, fun p hp => by cases hp⟩ hch
  simp only [List.reverse_nil, List.nil_append] at hys
  subst hys
  refine ⟨children, heq, ⟨hlen, fun k hk' => ?_⟩, fun k₁ k₂ h₁ h₂ hc => ?_⟩
  · obtain ⟨y, hy, hre, _⟩ := hk k hk'
    exact ⟨y, hy, Or.inr hre⟩
  · obtain ⟨y₁, hy₁, _, hc₁⟩ := hk k₁ h₁
    obtain ⟨y₂, hy₂, _, hc₂⟩ := hk k₂ h₂
    rw [hy₁, hy₂]
    rw [hc] at hc₁
    rw [hc₁] at hc₂
    exact congrArg some (Option.some.inj hc₂)


/-- **`MachineClosesAtAX` from `LetsClose` and `CallsPurePX`** (as `machineClosesAtA_of_pureX`; the
pin comes from `closeInstsM_runPX`). -/
theorem machineClosesAtA_of_pure_pinX (O : RefLawsAOpsX MkRefd mref cref)
    (T : RefLawsATeleX O.quiet O.adm mref cref) (hA : O.adm mctx cctx)
    {declName : Name} {shape : MachineShape}
    (hl : LetsClose mctx mref cctx cref declName shape)
    (hp : CallsPurePX O declName shape) :
    MachineClosesAtAX (mref := mref) (cref := cref) O mctx cctx declName shape := by
  have hB := Tools.ShippingChildComposeC.bodyStepC_of_teleX O T
  have htr := fun (tenv : Lean.Environment) (D : Nat) =>
    Tools.ShippingChildRunAMain.htr_of_teleX O hA T D tenv
  intro tenv b n w r w' hw hn hr
  obtain ⟨D, rfl⟩ : ∃ D, n = D + 1 := ⟨n - 1, by omega⟩
  unfold synthesizeMachineCertified at hr
  obtain ⟨⟨t, d'⟩, w1, run, hr⟩ := RunsTo.bind hr
  have hw1 := triple_runsX (keeps_iff.mp (mixed_keepsAPX O hA (stableA_JQCX O (D + 1)) _ b declName
    shape.binders shape.body (htr tenv D))) hw run
  dsimp only at hr
  obtain ⟨t', ht'⟩ := Option.isSome_iff_exists.mp (hl (profLogIO b) w t d' w1 run)
  rw [ht'] at hr
  dsimp only at hr
  split at hr
  · have := RunsTo.pure_eq hr
    rw [this]
    exact Option.some_ne_none _
  · split at hr
    · rename_i hf
      obtain ⟨children, rfl, hreal, hsame⟩ := closeInstsM_runPX O T hA hw1 hr
      have := (hp b t d' t' children run.mreturns ht' hreal).1 (List.isEmpty_iff.mp hf) hsame
      intro h
      rw [h] at this
      cases this
    · rename_i hf
      obtain ⟨children, rfl, hmem, hreal, _⟩ := closeInstsGM_runCX O hB hA hw1 hr
      have := (hp b t d' t' children run.mreturns ht' hreal).2
        (fun h => hf (List.isEmpty_iff.mpr h)) hmem
      intro h
      rw [h] at this
      cases this


/-- **`MachineClosesAtAX` for one-output calls of gate children, repeated callees allowed**
(`machineClosesAtA_of_gateKidsX` of CA with `hnodup` DROPPED; the same-callee ⇒ same-child fact is
`closeInstsM_runPX`, from the cache pin). Premises: `O`, `hA`, `T`, and the data/name conditions
of CA's lemma. -/
theorem machineClosesAtA_of_gateKids'X (O : RefLawsAOpsX MkRefd mref cref)
    (T : RefLawsATeleX O.quiet O.adm mref cref) (hA : O.adm mctx cctx) {declName : Name}
    (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (halias : d.letsAliasOk = true)
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
    MachineClosesAtAX (mref := mref) (cref := cref) O mctx cctx declName d.shape :=
  machineClosesAtA_of_pure_pinX O T hA
    (letsClose_of_data d ok hbody halias mctx mref cctx cref)
    (callsPureP_of_gateKidsX O d ok hbody hS nk hnomemO hkid hargsN hsep hparent hfresh)

end Tools.ShippingCallsGatePinned

#print axioms Tools.ShippingCallsGatePinned.closeInstsM_runPX
#print axioms Tools.ShippingCallsGatePinned.machineClosesAtA_of_gateKids'X

