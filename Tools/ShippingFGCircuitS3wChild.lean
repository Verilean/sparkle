import Tools.ShippingFGCircuitS3vChild
import Tools.ShippingFGCircuitS3wRun
import Tools.ShippingFGCircuitS3wBridge
set_option autoImplicit false
-- FG circuit pilot S3w, step 3: the second closed child `pilotK1` (`tlpCplByte`, 159 statements) end to end, as S3v did for `pilotK0`.  From `checkCombN_sound`, `checkWithN tlpCplByte.machineData pilotK1 = true` (kernel), the bridge `ofData_soundW` (S3v's `ofData_sound` with one added case, `Tools.ShippingFGCircuitS3wBridge`) and `tlpCplByte.machine_result`: `ChildFn pilotK1 (childRange tlpCplByte.machineData) (childValue …)` for all inputs in range (6 arguments), no run premise.  The bridge's side conditions are proved for `tlpCplByte` by the kernel (per-field closed facts, no `decide` over the whole `machineData`).  docs/FG-CIRCUIT-PILOT.md §72.
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
theorem k1_ss : tlpCplByte.machineData.ss.length = 0 := by decide +kernel
theorem k1_frag_ls : tlpCplByte.machineData.ls.all (fun l => FragW tlpCplByte.machineData l.2) = true := by decide +kernel
theorem k1_frag_outs : tlpCplByte.machineData.outs.all (fun o => FragW tlpCplByte.machineData o.2) = true := by decide +kernel
theorem k1_outs_len : tlpCplByte.machineData.outs.length = 1 := by decide +kernel
theorem k1_inpos : inputPositions tlpCplByte.machineData = [1, 2, 3, 4, 5, 6] := by decide +kernel
theorem k1_inputs_len : pilotK1.inputs.length = 6 := by decide +kernel
theorem k1_inputs_ok : pilotK1.inputs.all (fun p => p.name != "clk" && p.name != "rst") = true := by decide +kernel
theorem k1_outputs_len : pilotK1.outputs.length = 1 := by decide +kernel

/-- the facts per input index: the i-th argument port and the i-th ranged binder, the port's width is the binder's width, the source position i+1 reads the i-th value -/
noncomputable def k1Fact (i : Nat) : Bool :=
  match pilotK1.inputs[i]?, (tlpCplByte.machineData.bsIn.filter (fun b => b.2 != .domain))[i]?, (inputPositions tlpCplByte.machineData)[i]? with
  | some p, some b, some q => decide (b.2 = .bits (portW p)) && (q == i + 1) && (portIdx tlpCplByte.machineData.bsIn q == i)
  | _, _, _ => false

theorem k1_facts : (List.range 6).all k1Fact = true := by decide +kernel

theorem k1_fact_of (i : Nat) (p : Sparkle.IR.AST.Port) (hp : pilotK1.inputs[i]? = some p) :
    ∃ b q, (tlpCplByte.machineData.bsIn.filter (fun b => b.2 != .domain))[i]? = some b ∧ (inputPositions tlpCplByte.machineData)[i]? = some q ∧
      b.2 = .bits (portW p) ∧ q = i + 1 ∧ portIdx tlpCplByte.machineData.bsIn q = i := by
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

/-- `typedVal` at a time is `letTV` at the values read at that time (S3v's `typedVal_eq`, in the form the tail of `k1_childFn` needs, for an arbitrary `d` so that nothing of `tlpCplByte`'s data is unfolded) -/
theorem tail_gen {D : Sparkle.Core.Domain.DomainConfig} (d : MachineData)
    (bools : Nat → Sparkle.Core.Signal.Signal D Bool)
    (bits : (j : Nat) → (n : Nat) → Sparkle.Core.Signal.Signal D (BitVec n)) (t : Nat) (x : HList (tys d.ss))
    (B : Nat → Bool) (W : (p w : Nat) → BitVec w)
    (hB : ∀ p, (bools p).val t = B p) (hW : ∀ p w, (bits p w).val t = W p w)
    (o : Σ s : SType, Term s) (F : Nat)
    (h : enc o.1 (eval (fun k => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t x).b (d.bpos k))
        (fun k w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t x).v (d.vpos k) w) o.2) = F) :
    enc o.1 (eval (fun j => (letTV d x B W).b (d.bpos j))
        (fun j w => (letTV d x B W).v (d.vpos j) w) o.2) = F := by
  have e1 : (fun p => (bools p).val t) = B := funext hB
  have e2 : (fun p w => (bits p w).val t) = W := funext fun p => funext fun w => hW p w
  rw [← e1, ← e2]
  exact h

/-- **`ChildFn` for the closed child `pilotK1`**: the module computes, on every environment with reset low and argument values in the range of `tlpCplByte`'s inputs, `childValue` of `tlpCplByte`'s own `machineSource`.  Full type, all inputs, no run premise. -/
theorem k1_childFn : ChildFn pilotK1 (childRange tlpCplByte.machineData)
    (childValue tlpCplByte.machineSource tlpCplByte.machineData.bsIn defaultDomain) := by
  obtain ⟨s, hs, hc⟩ : ∃ s, ofData tlpCplByte.machineData = some s ∧ checkCombN s pilotK1 = true := by
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
    rw [hv] at this
    simpa using this
  -- the source valuation
  let vals : List Nat := pilotK1.inputs.map (fun p => env p.name)
  let V : Nat → Nat := fun q => vals.getD (portIdx tlpCplByte.machineData.bsIn q) 0
  have hW : ∀ p w, p < tlpCplByte.machineData.nIn → ((decV tlpCplByte.machineData.bsIn vals p w).toNat) = V p % 2 ^ w := by
    intro p w _
    simp [decV, V]
  have hsound := ofData_soundW tlpCplByte.machineData k1_ss V (tlpCplByte.machineInits)
    (fun p => decB tlpCplByte.machineData.bsIn vals p) (fun p w => decV tlpCplByte.machineData.bsIn vals p w) hW
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
      show vals.getD (portIdx tlpCplByte.machineData.bsIn q) 0 = _
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
    (fun p => Sparkle.Core.Signal.Signal.pure (decB tlpCplByte.machineData.bsIn vals p))
    (fun p n => Sparkle.Core.Signal.Signal.pure (decV tlpCplByte.machineData.bsIn vals p n)) 0
  rw [ho0] at hres
  obtain ⟨f, hf⟩ : ∃ f, tlpCplByte.machineSource defaultDomain
      (fun p => Sparkle.Core.Signal.Signal.pure (decB tlpCplByte.machineData.bsIn vals p))
      (fun p n => Sparkle.Core.Signal.Signal.pure (decV tlpCplByte.machineData.bsIn vals p n)) = [f] := ⟨_, rfl⟩
  rw [hf] at hres
  unfold childValue
  rw [hf]
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hres
  simp only [List.getElem?_cons_zero, Option.map_some, Option.getD_some]
  exact (tail_gen (D := defaultDomain) tlpCplByte.machineData (fun p => Sparkle.Core.Signal.Signal.pure (decB tlpCplByte.machineData.bsIn vals p))
    (fun p n => Sparkle.Core.Signal.Signal.pure (decV tlpCplByte.machineData.bsIn vals p n)) 0 tlpCplByte.machineInits (fun p => decB tlpCplByte.machineData.bsIn vals p) (fun p w => decV tlpCplByte.machineData.bsIn vals p w) (fun _ => rfl) (fun _ _ => rfl) o0 (f 0) hres.symm)


/-- the same conjunct, in the form `RootShowsAt` has it for call 1: the root's `SourceData` fixes `kidData[1]` and `kidFs[1]`, and the closed child's module computes that function on that range -/
theorem k1_childFn_slot : ∃ (kd : MachineData) (f : List Nat → Nat),
    kidData[1]? = some kd ∧ kidFs[1]? = some f ∧ ChildFn pilotK1 (childRange kd) f :=
  ⟨_, _, rfl, rfl, k1_childFn⟩

/-! ### controls: the conclusion is not vacuous; a changed module or function does not satisfy it -/

open Tools.ShippingFGCircuitS3tCombRun (dropFirst)

/-- an environment with the count argument 1 and everything else 0 -/
def k1env : Sparkle.IR.Semantics.Env := fun n => if n = "_gen_cntSig" then 1 else 0

/-- the value a combinational module gives its first output port at `k1env` (no memories) -/
def k1eval (m : Sparkle.IR.AST.Module) : Option Nat :=
  (Sparkle.IR.Semantics.evalAssigns (Sparkle.IR.RegDedup.declWidth m) (fun _ _ => 0) m.body k1env).map
    (fun e => e ((m.outputs.map (·.name)).headD ""))

theorem k1_eval : k1eval pilotK1 = some 74 := by decide +kernel
theorem k1_eval_flip : k1eval (flip74 pilotK1) = some 75 := by decide +kernel

theorem k1_bs : tlpCplByte.machineData.bsIn.filter (fun b => b.2 != .domain) =
    [(`cplId, .bits 16), (`reqId, .bits 16), (`tag, .bits 8), (`lowerAddr, .bits 8), (`data, .bits 32), (`cntSig, .bits 5)] := by
  decide +kernel

theorem k1_range_vec : childRange tlpCplByte.machineData [0, 0, 0, 0, 0, 1] := by
  unfold childRange InRange
  rw [k1_bs]
  repeat' first | exact .nil | (apply Tools.ShippingMachineClose.Zip₂.cons; decide)

theorem k1_args_vec : (argPorts pilotK1).map (fun p => k1env p.name) = [0, 0, 0, 0, 0, 1] := by decide +kernel
theorem k1_rst_zero : k1env "rst" = 0 := by decide +kernel

/-- a module with `pilotK1`'s inputs that satisfies `ChildFn` for `f` gives `f [0,0,0,0,0,1]` at `k1env` -/
theorem childFn_k1eval (m : Sparkle.IR.AST.Module) (hm : m.inputs = pilotK1.inputs) (f : List Nat → Nat)
    (h : ChildFn m (childRange tlpCplByte.machineData) f) : k1eval m = some (f [0, 0, 0, 0, 0, 1]) := by
  obtain ⟨outP, hout, h⟩ := h
  have hargs : argPorts m = argPorts pilotK1 := by simp [argPorts, hm]
  obtain ⟨cres, he, hv⟩ := h (fun _ _ => 0) k1env k1_rst_zero (by rw [hargs, k1_args_vec]; exact k1_range_vec)
  rw [hargs, k1_args_vec] at hv
  simp only [k1eval, he, Option.map_some, hout, List.map_cons, List.map_nil, List.headD_cons, hv]

/-- the conclusion is not vacuous: the function `fun _ => 0` is NOT what `pilotK1` computes -/
theorem k1_not_zero : ¬ ChildFn pilotK1 (childRange tlpCplByte.machineData) (fun _ => 0) := by
  intro h
  have := childFn_k1eval pilotK1 rfl _ h
  rw [k1_eval] at this
  simp at this

/-- a mutated module (the constant 74 changed to 75) does NOT satisfy the same `ChildFn` -/
theorem flip74_not_childFn : ¬ ChildFn (flip74 pilotK1) (childRange tlpCplByte.machineData)
    (childValue tlpCplByte.machineSource tlpCplByte.machineData.bsIn defaultDomain) := by
  intro h
  have h1 := childFn_k1eval (flip74 pilotK1) rfl _ h
  have h0 := childFn_k1eval pilotK1 rfl _ k1_childFn
  rw [k1_eval] at h0
  rw [k1_eval_flip, ← Option.some.inj h0] at h1
  simp at h1

end Tools.ShippingFGCircuitS3wChild
