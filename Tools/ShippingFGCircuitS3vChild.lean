import Tools.ShippingFGCircuitS3vBridge
set_option autoImplicit false
-- FG circuit pilot S3v, steps 2-3: the closed child `pilotK0` (`httpGetByte`) end to end.  From `checkComb_sound` (the module's IR semantics equals the source terms' value), `checkK0 pilotK0 = true`, and the bridge `ofData_sound` (the source terms denote what `Term.eval` on `typedVal` gives), together with `httpGetByte.machine_result` (`machineSource` = those evaluated outputs): `ChildFn pilotK0 (childRange kd) (childValue …)`, the exact conjunct `RootShowsAt` needs for call 0.  Full type, all inputs, no run premise.  The side conditions of the bridge are PROVED for `httpGetByte` by the kernel (per-field closed facts).  docs/FG-CIRCUIT-PILOT.md §71.
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace Tools.ShippingFGCircuitS3vChild
open Tools.ShippingFGCircuitS3tComb Tools.ShippingFGCircuitS3tCombRun Tools.ShippingFGCircuitS3vBridge
open Tools.ShippingUnifiedSource Tools.ShippingMachineAuto Tools.ShippingMachineDenote
open Tools.ShippingFGCircuitS3rArtifact (pilotK0)
open Tools.ShippingMachineCompose (ChildFn argPorts)
open Tools.ShippingMachineChild (childValue childRange decB decV portIdx InRange inRange_get)
open Sparkle.IP.Net.HTTP (httpGetByte)
open Sparkle.Core.Domain (defaultDomain)
open Sparkle.Core (HList)

/-- the data of `httpGetByte` -/
noncomputable abbrev kd0 : MachineData := httpGetByte.machineData

/-! ### the bridge's side conditions, proved for `httpGetByte` (closed facts, kernel) -/
theorem k0_ss : kd0.ss.length = 0 := by decide +kernel
theorem k0_frag_ls : kd0.ls.all (fun l => Frag kd0 l.2) = true := by decide +kernel
theorem k0_frag_outs : kd0.outs.all (fun o => Frag kd0 o.2) = true := by decide +kernel
theorem k0_outs_len : kd0.outs.length = 1 := by decide +kernel
theorem k0_inpos : inputPositions kd0 = [1] := by decide +kernel
theorem k0_portIdx : portIdx kd0.bsIn 1 = 0 := by decide +kernel
theorem k0_range_bs : (kd0.bsIn.filter (fun b => b.2 != .domain)).map (·.2) = [.bits 6] := by decide +kernel
theorem k0_inputs_len : pilotK0.inputs.length = 1 := by decide +kernel
theorem k0_inputs_ok : pilotK0.inputs.all
    (fun p => p.name != "clk" && p.name != "rst" && portW p == 6) = true := by decide +kernel
theorem k0_outputs_len : pilotK0.outputs.length = 1 := by decide +kernel


/-- **`ChildFn` for the closed child `pilotK0`**: the module computes, on every environment with reset low and argument values in the range of `httpGetByte`'s input, `childValue` of `httpGetByte`'s own `machineSource` (decoded by `decB`/`decV`).  Full type, all inputs, no run premise; the child's source function is the one `kidFs[0]` of the root's `SourceData` fixes. -/
theorem k0_childFn : ChildFn pilotK0 (childRange kd0)
    (childValue httpGetByte.machineSource kd0.bsIn defaultDomain) := by
  obtain ⟨s, hs, hc⟩ : ∃ s, ofData kd0 = some s ∧ checkComb s pilotK0 = true := by
    have h := k0_check
    unfold checkK0 at h
    split at h
    · rename_i s hs; exact ⟨s, hs, h⟩
    · cases h
  obtain ⟨outP, hout⟩ := List.length_eq_one_iff.mp k0_outputs_len
  refine ⟨outP, hout, ?_⟩
  intro mems env hrst hP
  obtain ⟨p0, hin⟩ := List.length_eq_one_iff.mp k0_inputs_len
  have hp0 : p0.name ≠ "clk" ∧ p0.name ≠ "rst" ∧ portW p0 = 6 := by
    have h := k0_inputs_ok
    rw [hin] at h
    simp at h
    exact ⟨h.1.1, h.1.2, h.2⟩
  have hargs : argPorts pilotK0 = [p0] := by
    simp [argPorts, hin, hp0.1, hp0.2.1]
  have hvals : (argPorts pilotK0).map (fun p => env p.name) = [env p0.name] := by rw [hargs]; rfl
  rw [hvals] at hP ⊢
  -- the argument value is in range
  have hlt : env p0.name < 2 ^ 6 := by
    obtain ⟨b0, hb0⟩ : ∃ b, kd0.bsIn.filter (fun b => b.2 != .domain) = [b] := by
      apply List.length_eq_one_iff.mp
      have := congrArg List.length k0_range_bs
      simpa using this
    have hb2 : b0.2 = .bits 6 := by
      have := k0_range_bs
      rw [hb0] at this
      simpa using this
    have := inRange_get hP 0 b0 (by rw [childRange] at hP; simp [hb0])
    rw [hb2] at this
    simpa using this
  -- the source valuation
  let V : Nat → Nat := fun q => [env p0.name].getD (portIdx kd0.bsIn q) 0
  have hV1 : V 1 = env p0.name := by
    show [env p0.name].getD (portIdx kd0.bsIn 1) 0 = _
    rw [k0_portIdx]; rfl
  have hW : ∀ p w, p < kd0.nIn →
      ((decV kd0.bsIn [env p0.name] p w).toNat) = V p % 2 ^ w := by
    intro p w _
    simp [decV, V]
  have hsound := ofData_sound kd0 k0_ss V (httpGetByte.machineInits)
    (fun p => decB kd0.bsIn [env p0.name] p) (fun p w => decV kd0.bsIn [env p0.name] p w) hW
    (by simpa using k0_frag_ls) (by simpa using k0_frag_outs) s hs
  obtain ⟨hinPos, hlen, hrel⟩ := hsound
  rw [k0_inpos] at hinPos
  obtain ⟨env', he, hov⟩ := checkComb_sound s pilotK0 hc V mems env (by
    intro i p q hi hq
    rw [hin] at hi
    rw [hinPos] at hq
    cases i with
    | zero =>
      simp at hi hq
      subst hi; subst hq
      rw [hV1, hp0.2.2]
      exact (Nat.mod_eq_of_lt hlt).symm
    | succ i => simp at hi)
  refine ⟨env', he, ?_⟩
  obtain ⟨o0, ho0⟩ := List.length_eq_one_iff.mp k0_outs_len
  have hslen : s.outs.length = 1 := by rw [hlen]; exact k0_outs_len
  obtain ⟨c0, hc0⟩ := List.length_eq_one_iff.mp hslen
  have h1 := hov 0 outP c0 (by simp [hout]) (by simp [hc0])
  have h2 := hrel 0 o0 c0 (by simp [ho0]) (by simp [hc0])
  rw [h1, h2.1]
  have hres := httpGetByte.machine_result defaultDomain
    (fun p => Sparkle.Core.Signal.Signal.pure (decB kd0.bsIn [env p0.name] p))
    (fun p n => Sparkle.Core.Signal.Signal.pure (decV kd0.bsIn [env p0.name] p n)) 0
  simp only [ho0, List.map_cons, List.map_nil, httpGetByte.machineSource] at hres
  unfold childValue
  simp only [httpGetByte.machineSource]
  simp only [List.cons.injEq, and_true] at hres
  simp only [List.getElem?_cons_zero, Option.map_some, Option.getD_some]
  exact hres.symm

end Tools.ShippingFGCircuitS3vChild
