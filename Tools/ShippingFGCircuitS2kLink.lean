import Tools.ShippingFGCircuitS2cLink
set_option autoImplicit false
-- FG circuit pilot S2k: `HftRootLink` assembly. The conclusion part is an independent lemma with the typed valuations as abstract variables (`link_concl`). No `sorry`, no `axiom`, no `native_decide`, no TRUSTED, no new law. Results: docs/FG-CIRCUIT-PILOT.md §37.
namespace Tools.ShippingFGCircuitS2kLink
open Lean Sparkle.Compiler.Elab Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingMachineDenote Tools.ShippingMachineAuto Tools.ShippingMachineSource
open Tools.ShippingMachineRef (reads)
open Tools.ShippingGen5Sem
open Tools.ShippingUnifiedSource
open Tools.ShippingFGCircuitS2cLink
open Tools.ShippingFGCircuitS1kStmt Tools.ShippingFGCircuitS1kRoot Tools.ShippingFGCircuitS1uSrc
open Tools.ShippingMachineTeleStates (callArgVals callArgsOf teleState)
open Tools.ShippingFGCircuit (monoObs)

/-- **the conclusion part of `HftRootLink`, with the typed valuations as abstract variables**: if the declaration's observation equals the data's outputs over `T'` and `T`, `T'` agree at the declared sorts, then it equals the outputs over `T`. -/
theorem link_concl (d : MachineData) (hok : d.ok = true) (hw : ∀ o ∈ d.outs, o.2.WF d.kb d.kv d.vw) {T T' : TVal}
    (h : ∀ p, p < d.nIn + d.ss.length + d.ls.length → AgrAt d T T' p) {src : List (Nat → Nat)} {t : Nat}
    (hobs : src.map (fun f => f t) = d.outs.map (fun o => enc o.1 (eval (fun j => T'.b (d.bpos j)) (fun j w => T'.v (d.vpos j) w) o.2))) :
    src.map (fun f => f t) = d.outs.map (fun o => enc o.1 (eval (fun j => T.b (d.bpos j)) (fun j w => T.v (d.vpos j) w) o.2)) :=
  hobs.trans (outs_tagree d hok hw h).symm

/-- **`HftRootLink`**, proved from the chain endpoint's `machine_states` (fused state stream) and `machine_arg_0/1` (per-call argument facts), the children's pointwise-ness (`http_pw`, `tlp_pw` from their `machine_result`), and the typed agreement of the `ExtStage` family with the Lean extension. -/
theorem hftRootLink : HftRootLink := by
  intro ι gi hgi
  obtain ⟨d, wf, inits, ok, bodyEq, init⟩ := gi
  simp only at hgi
  subst hgi
  intro i bools bits S hS0 hrec t
  have hss : [SType.bits 6] ++ synth_hftPcieOutByte.machineInners.sss = synth_hftPcieOutByte.machineData.ss := rfl
  obtain ⟨S₂, Ss, h0, hstep, hobs⟩ := synth_hftPcieOutByte.machine_states () bools bits
  let sg : Nat → HList (tys synth_hftPcieOutByte.machineData.ss) := fun t =>
    teleState synth_hftPcieOutByte.machineInners hss () bools bits S₂ Ss t
  -- the Lean extension, and the typed agreement of the `ExtStage` family with it, at a cycle
  have hext : ∀ t, S.val t = sg t →
      (ExtStage (dom := fun _ => defaultDomain) (hftKids (ι := ι)) (GenIn.mk synth_hftPcieOutByte.machineData wf inits ok bodyEq init) i bools bits S 2).1 = bools ∧
      ∀ p w, p < 7 → synth_hftPcieOutByte.machineData.K p = some (.bits w) →
        ((ExtStage (dom := fun _ => defaultDomain) (hftKids (ι := ι)) (GenIn.mk synth_hftPcieOutByte.machineData wf inits ok bodyEq init) i bools bits S 2).2 p w).val t =
          (synth_hftPcieOutByte.machineExt () bools bits S₂ Ss p w).val t := by
    intro t hSt
    have a0 := synth_hftPcieOutByte.machine_arg_0 () bools bits S₂ Ss t
    have a1 := synth_hftPcieOutByte.machine_arg_1 () bools bits S₂ Ss t
    have s1 := stage1 (GenIn.mk synth_hftPcieOutByte.machineData wf inits ok bodyEq init) rfl i bools bits S t _
      (by show callArgVals synth_hftPcieOutByte.machineData bools bits t (S.val t) _ = _; rw [hSt]; exact a0)
    exact stage2 (GenIn.mk synth_hftPcieOutByte.machineData wf inits ok bodyEq init) rfl i bools bits S t _ s1.1 s1.2 _ _ _ _ _ _
      (by show callArgVals synth_hftPcieOutByte.machineData bools _ t (S.val t) _ = _; rw [hSt]; exact a1)
  have hok : synth_hftPcieOutByte.machineData.ok = true := synth_hftPcieOutByte.machine_ok
  have hlen2 : (GenIn.mk synth_hftPcieOutByte.machineData wf inits ok bodyEq init).d.shape.insts.length = 2 := root_insts_len
  -- the agreement of the two families' typed valuations at a cycle
  have hagree : ∀ t, S.val t = sg t →
      (∀ p, p < synth_hftPcieOutByte.machineData.nIn + synth_hftPcieOutByte.machineData.ss.length +
        synth_hftPcieOutByte.machineData.ls.length →
        AgrAt synth_hftPcieOutByte.machineData
          (typedVal synth_hftPcieOutByte.machineData.nIn synth_hftPcieOutByte.machineData.bpos
            synth_hftPcieOutByte.machineData.vpos synth_hftPcieOutByte.machineData.ss synth_hftPcieOutByte.machineData.ls
            (extBOf (dom := fun _ => defaultDomain) (hftKids (ι := ι)) (GenIn.mk synth_hftPcieOutByte.machineData wf inits ok bodyEq init) i bools bits S)
            (extOf (dom := fun _ => defaultDomain) (hftKids (ι := ι)) (GenIn.mk synth_hftPcieOutByte.machineData wf inits ok bodyEq init) i bools bits S) t (S.val t))
          (typedVal synth_hftPcieOutByte.machineData.nIn synth_hftPcieOutByte.machineData.bpos
            synth_hftPcieOutByte.machineData.vpos synth_hftPcieOutByte.machineData.ss synth_hftPcieOutByte.machineData.ls
            bools (synth_hftPcieOutByte.machineExt () bools bits S₂ Ss) t (sg t)) p) := by
    intro t hSt
    obtain ⟨hb, hv⟩ := hext t hSt
    have hB : extBOf (dom := fun _ => defaultDomain) (hftKids (ι := ι)) (GenIn.mk synth_hftPcieOutByte.machineData wf inits ok bodyEq init) i bools bits S = bools := by
      unfold extBOf; rw [hlen2]; exact hb
    rw [hB, ← hSt]
    exact typedVal_tagree synth_hftPcieOutByte.machineData hok _ _ _ _ t _ (fun _ _ => rfl)
      (fun p w hp hK => by
        unfold extOf; rw [hlen2]
        exact hv p w (by rw [← root_nIn]; exact hp) hK)
  have hSg : ∀ t, S.val t = sg t := by
    intro t
    induction t with
    | zero =>
      rw [hS0]
      exact inits_unique _ inits (sg 0) init (by rw [show sg 0 = _ from h0]; exact synth_hftPcieOutByte.machine_inits)
    | succ t ih =>
      rw [hrec t]
      refine Eq.trans ?_ (hstep t).symm
      exact nexts_tagree _ hok (hagree t ih)
  have hw := outs_wf _ hok root_outs_len
  have hag := hagree t (hSg t)
  rw [monoObs_root bools bits]
  exact link_concl _ hok hw hag (hobs t)

end Tools.ShippingFGCircuitS2kLink

#print axioms Tools.ShippingFGCircuitS2kLink.link_concl
#print axioms Tools.ShippingFGCircuitS2kLink.hftRootLink
