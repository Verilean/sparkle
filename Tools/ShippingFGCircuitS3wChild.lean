import Tools.ShippingFGCircuitS3vChild
import Tools.ShippingFGCircuitS3wRun
import Tools.ShippingFGCircuitS3wBridge
set_option autoImplicit false
-- FG circuit pilot S3w, step 3: the second closed child `pilotK1` (`tlpCplByte`, 159 statements) end to end, as S3v did for `pilotK0`.  From `checkCombN_sound`, `checkWithN kd1 pilotK1 = true` (kernel), the bridge `ofData_soundW` (S3v's `ofData_sound` with one added case, `Tools.ShippingFGCircuitS3wBridge`) and `tlpCplByte.machine_result`: `ChildFn pilotK1 (childRange kd1) (childValue …)` for all inputs in range (6 arguments), no run premise.  The bridge's side conditions are proved for `tlpCplByte` by the kernel (per-field closed facts, no `decide` over the whole `machineData`).  docs/FG-CIRCUIT-PILOT.md §72.
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace Tools.ShippingFGCircuitS3wChild
open Tools.ShippingFGCircuitS3tComb Tools.ShippingFGCircuitS3tCombRun Tools.ShippingFGCircuitS3vBridge
open Tools.ShippingFGCircuitS3wComb Tools.ShippingFGCircuitS3wRun Tools.ShippingFGCircuitS3wBridge
open Tools.ShippingUnifiedSource Tools.ShippingMachineAuto Tools.ShippingMachineDenote
open Tools.ShippingFGCircuitS3rArtifact (pilotK0 pilotK1)
open Tools.ShippingMachineCompose (ChildFn argPorts)
open Tools.ShippingMachineChild (childValue childRange decB decV portIdx InRange inRange_get)
open Sparkle.IP.Bus.PCIe (tlpCplByte)
open Sparkle.Core.Domain (defaultDomain)
open Sparkle.Core (HList)
open Tools.ShippingFGCircuitS3tSpec (kidData kidFs)

/-! ### the bridge's side conditions, proved for `tlpCplByte` (closed facts, kernel) -/
theorem k1_ss : kd1.ss.length = 0 := by decide +kernel
theorem k1_frag_ls : kd1.ls.all (fun l => FragW kd1 l.2) = true := by decide +kernel
theorem k1_frag_outs : kd1.outs.all (fun o => FragW kd1 o.2) = true := by decide +kernel
theorem k1_outs_len : kd1.outs.length = 1 := by decide +kernel
theorem k1_inpos : inputPositions kd1 = [1, 2, 3, 4, 5, 6] := by decide +kernel
theorem k1_inputs_len : pilotK1.inputs.length = 6 := by decide +kernel
theorem k1_inputs_ok : pilotK1.inputs.all (fun p => p.name != "clk" && p.name != "rst") = true := by decide +kernel
theorem k1_outputs_len : pilotK1.outputs.length = 1 := by decide +kernel

/-- the facts per input index: the i-th argument port and the i-th ranged binder, the port's width is the binder's width, the source position i+1 reads the i-th value -/
noncomputable def k1Fact (i : Nat) : Bool :=
  match pilotK1.inputs[i]?, (kd1.bsIn.filter (fun b => b.2 != .domain))[i]?, (inputPositions kd1)[i]? with
  | some p, some b, some q => decide (b.2 = .bits (portW p)) && (q == i + 1) && (portIdx kd1.bsIn q == i)
  | _, _, _ => false

theorem k1_facts : (List.range 6).all k1Fact = true := by decide +kernel

theorem k1_fact_of (i : Nat) (p : Sparkle.IR.AST.Port) (hp : (pilotK1.inputs[i]? = some p) :
    ∃ b q, (kd1.bsIn.filter (fun b => b.2 != .domain))[i]? = some b ∧ (inputPositions kd1)[i]? = some q ∧
      b.2 = .bits (portW p) ∧ q = i + 1 ∧ portIdx kd1.bsIn q = i := by
  have hi : i < 6 := by
    have := (List.getElem?_eq_some_iff.mp hp).1
    rw [k1_inputs_len] at this; exact this
  have h := List.all_eq_true.mp k1_facts i (List.mem_range.mpr hi)
  unfold k1Fact at h
  rw [hp] at h
  split at h
  · rename_i p' b q hp' hb hq
    simp only [Option.some.injEq] at hp'
    subst hp'
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    exact ⟨b, q, hb, hq, h.1.1, h.1.2, h.2⟩
  · cases h

/-- **`ChildFn` for the closed child `pilotK1`**: the module computes, on every environment with reset low and argument values in the range of `tlpCplByte`'s inputs, `childValue` of `tlpCplByte`'s own `machineSource`.  Full type, all inputs, no run premise. -/
theorem k1_childFn : ChildFn pilotK1 (childRange kd1)
    (childValue tlpCplByte.machineSource kd1.bsIn defaultDomain) := by
  obtain ⟨s, hs, hc⟩ : ∃ s, ofData kd1 = some s ∧ checkCombN s pilotK1 = true := by
    have h := k1_checkN
    unfold checkWithN at h
    split at h
    · rename_i s hs; exact ⟨s, hs, h⟩
    · cases h
  obtain ⟨outP, hout⟩ := List.length_eq_one_iff.mp k1_outputs_len
  refine ⟨outP, hout, ?_⟩
  intro mems env hrst hP
  have hargs : argPorts pilotK1 = pilotK1.inputs := by
    unfold argPorts
    exact List.filter_eq_self.mpr (fun p hp => by
      have := List.all_eq_true.mp k1_inputs_ok p hp
      exact this)
  have hvals : (argPorts pilotK1).map (fun p => env p.name) = pilotK1.inputs.map (fun p => env p.name) := by rw [hargs]
  rw [hvals] at hP ⊢
  -- each argument value is in range of its port width
  have hlt : ∀ (i : Nat) (p : Sparkle.IR.AST.Port), pilotK1.inputs[i]? = some p → env p.name < 2 ^ portW p := by
    intro i p hp
    obtain ⟨b, q, hb, hq, hb2, hq1, hpi⟩ := k1_fact_of i p hp
    have := inRange_get hP i b hb
    rw [hb2] at this
    have hv : (pilotK1.inputs.map (fun p => env p.name)).getD i 0 = env p.name := by
      simp [List.getD_eq_getElem?_getD, hp]
    simpa [hv] using this
  -- the source valuation
  let vals : List Nat := pilotK1.inputs.map (fun p => env p.name)
  let V : Nat → Nat := fun q => vals.getD (portIdx kd1.bsIn q) 0
  have hW : ∀ p w, p < kd1.nIn → ((decV kd1.bsIn vals p w).toNat) = V p % 2 ^ w := by
    intro p w _
    simp [decV, V]
  have hsound := ofData_soundW kd1 k1_ss V (tlpCplByte.machineInits)
    (fun p => decB kd1.bsIn vals p) (fun p w => decV kd1.bsIn vals p w) hW
    (by simpa using k1_frag_ls) (by simpa using k1_frag_outs) s hs
  obtain ⟨hinPos, hlen, hrel⟩ := hsound
  obtain ⟨env', he, hov⟩ := checkCombN_sound s pilotK1 hc V mems env (by
    intro i p q hi hq
    obtain ⟨b, q', hb, hq', hb2, hq1, hpi⟩ := k1_fact_of i p hi
    rw [hinPos] at hq
    rw [hq'] at hq
    have : q = q' := (Option.some.inj hq).symm
    subst this
    have hv : V q = env p.name := by
      show vals.getD (portIdx kd1.bsIn q) 0 = _
      rw [hpi]
      simp [vals, List.getD_eq_getElem?_getD, hi]
    rw [hv]
    exact (Nat.mod_eq_of_lt (hlt i p hi)).symm)
  refine ⟨env', he, ?_⟩
  obtain ⟨o0, ho0⟩ := List.length_eq_one_iff.mp k1_outs_len
  have hslen : s.outs.length = 1 := by rw [hlen]; exact k1_outs_len
  obtain ⟨c0, hc0⟩ := List.length_eq_one_iff.mp hslen
  have h1 := hov 0 outP c0 (by simp [hout]) (by simp [hc0])
  have h2 := hrel 0 o0 c0 (by simp [ho0]) (by simp [hc0])
  rw [h1, h2.1]
  have hres := tlpCplByte.machine_result defaultDomain
    (fun p => Sparkle.Core.Signal.Signal.pure (decB kd1.bsIn vals p))
    (fun p n => Sparkle.Core.Signal.Signal.pure (decV kd1.bsIn vals p n)) 0
  simp only [ho0, List.map_cons, List.map_nil, tlpCplByte.machineSource] at hres
  unfold childValue
  simp only [tlpCplByte.machineSource]
  simp only [List.cons.injEq, and_true] at hres
  simp only [List.getElem?_cons_zero, Option.map_some, Option.getD_some]
  exact hres.symm

end Tools.ShippingFGCircuitS3wChild
