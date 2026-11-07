import Tools.ShippingFGCircuitS3tSpec
set_option autoImplicit false
-- FG circuit pilot S3t, step 1 (example, gap G2): `CallsEq` for the concrete root — the SOURCE's call facts (no IR): at the state the witnesses give, every call's argument values are in the child's range, and the child's source function on them is the value the root's extension carries at the call's input position.  Proved per call by the SAME facts the generated `machine_linked` uses (`machine_arg_k`, decoding is the inverse of encoding, the child is pointwise), with the kernel checking the definitional steps (`kernel_rfl`: the proof term `Eq.refl lhs`, rechecked by the kernel; an untrusted tactic, no axiom).  With `Tools.ShippingFGCircuitS3tSpec.rootS_srcCore` this gives `rootS.SrcEq`.  No sorry/axiom/native_decide/TRUSTED/law. docs/FG-CIRCUIT-PILOT.md §69.
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

-- close an equality `a = b` by the proof term `Eq.refl a`, which the KERNEL checks (the elaborator's `rfl` does not finish on the root's large generated terms; if `a` and `b` are not definitionally equal the kernel rejects the theorem)
open Lean Elab Tactic Meta in
elab "kernel_rfl" : tactic => do
  let g ← getMainGoal
  let t ← whnfR (← instantiateMVars (← g.getType))
  let some (α, lhs, _) := t.eq? | throwError "kernel_rfl: not an equality: {t}"
  let u ← getLevel α
  g.assign (mkApp2 (mkConst ``Eq.refl [u]) α lhs)

namespace Tools.ShippingFGCircuitS3tCalls
open Lean hiding Module Expr
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Tools.ShippingFGCircuitS1kRoot Tools.ShippingMachineDenote
open Tools.ShippingUnifiedSource Tools.ShippingMachineTeleStates Tools.ShippingMachineEntry Tools.ShippingMachineChild
open Tools.ShippingFGCircuitS3tSpec

theorem args_insts : (rootS.d.shape.insts.map (·.2.1)) = [[6], [38, 39, 40, 41, 42, 43]] := by decide +kernel

theorem kind0 : (((rootS.d.bsIn.drop rootS.kD)[0]?.map (·.2)).getD .domain) = .bits 8 := by decide +kernel
theorem kind1 : (((rootS.d.bsIn.drop rootS.kD)[1]?.map (·.2)).getD .domain) = .bits 8 := by decide +kernel

theorem calls0 (i : Unit) (bools : Nat → Signal defaultDomain Bool) (bits : (j n : Nat) → Signal defaultDomain (BitVec n))
    (S₂ : Signal defaultDomain (HList (tys [SType.bits 6])))
    (Ss : Tools.ShippingMachineTele.Tele.Sigs (synth_hftPcieOutByte.machineInners.at i bools bits)) (j : Nat) :
    childRange Sparkle.IP.Net.HTTP.httpGetByte.machineData
      (callArgVals synth_hftPcieOutByte.machineData bools (synth_hftPcieOutByte.machineExt i bools bits S₂ Ss) j
        (teleState synth_hftPcieOutByte.machineInners (d := synth_hftPcieOutByte.machineData)
          Tools.ShippingFGCircuitS2vLink.root_hss i bools bits S₂ Ss j) [6]) ∧
    childValue Sparkle.IP.Net.HTTP.httpGetByte.machineSource Sparkle.IP.Net.HTTP.httpGetByte.machineData.bsIn defaultDomain
      (callArgVals synth_hftPcieOutByte.machineData bools (synth_hftPcieOutByte.machineExt i bools bits S₂ Ss) j
        (teleState synth_hftPcieOutByte.machineInners (d := synth_hftPcieOutByte.machineData)
          Tools.ShippingFGCircuitS2vLink.root_hss i bools bits S₂ Ss j) [6]) =
      posEnc (fun p => (bools p).val j) (fun p n => ((synth_hftPcieOutByte.machineExt i bools bits S₂ Ss) p n).val j) 5 (.bits 8) := by
  have e1 : callArgVals synth_hftPcieOutByte.machineData bools (synth_hftPcieOutByte.machineExt i bools bits S₂ Ss) j
        (teleState synth_hftPcieOutByte.machineInners (d := synth_hftPcieOutByte.machineData)
          Tools.ShippingFGCircuitS2vLink.root_hss i bools bits S₂ Ss j) [6] =
      callArgVals synth_hftPcieOutByte.machineData bools bits j
        (teleState synth_hftPcieOutByte.machineInners (d := synth_hftPcieOutByte.machineData)
          Tools.ShippingFGCircuitS2vLink.root_hss i bools bits S₂ Ss j) (callArgsOf synth_hftPcieOutByte.machineData 0) := by
    kernel_rfl
  have h0 := synth_hftPcieOutByte.machine_arg_0 i bools bits S₂ Ss j
  rw [e1.trans h0]
  constructor
  · delta childRange
    exact Tools.ShippingMachineClose.Zip₂.cons (BitVec.isLt _) Tools.ShippingMachineClose.Zip₂.nil
  · have hp1 : portIdx Sparkle.IP.Net.HTTP.httpGetByte.machineData.bsIn 1 = 0 := by decide
    delta childValue Sparkle.IP.Net.HTTP.httpGetByte.machineSource
    simp only [decV, hp1, List.getD_cons_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    kernel_rfl

theorem calls1 (i : Unit) (bools : Nat → Signal defaultDomain Bool) (bits : (j n : Nat) → Signal defaultDomain (BitVec n))
    (S₂ : Signal defaultDomain (HList (tys [SType.bits 6])))
    (Ss : Tools.ShippingMachineTele.Tele.Sigs (synth_hftPcieOutByte.machineInners.at i bools bits)) (j : Nat) :
    childRange Sparkle.IP.Bus.PCIe.tlpCplByte.machineData
      (callArgVals synth_hftPcieOutByte.machineData bools (synth_hftPcieOutByte.machineExt i bools bits S₂ Ss) j
        (teleState synth_hftPcieOutByte.machineInners (d := synth_hftPcieOutByte.machineData)
          Tools.ShippingFGCircuitS2vLink.root_hss i bools bits S₂ Ss j) [38, 39, 40, 41, 42, 43]) ∧
    childValue Sparkle.IP.Bus.PCIe.tlpCplByte.machineSource Sparkle.IP.Bus.PCIe.tlpCplByte.machineData.bsIn defaultDomain
      (callArgVals synth_hftPcieOutByte.machineData bools (synth_hftPcieOutByte.machineExt i bools bits S₂ Ss) j
        (teleState synth_hftPcieOutByte.machineInners (d := synth_hftPcieOutByte.machineData)
          Tools.ShippingFGCircuitS2vLink.root_hss i bools bits S₂ Ss j) [38, 39, 40, 41, 42, 43]) =
      posEnc (fun p => (bools p).val j) (fun p n => ((synth_hftPcieOutByte.machineExt i bools bits S₂ Ss) p n).val j) 6 (.bits 8) := by
  have e1 : callArgVals synth_hftPcieOutByte.machineData bools (synth_hftPcieOutByte.machineExt i bools bits S₂ Ss) j
        (teleState synth_hftPcieOutByte.machineInners (d := synth_hftPcieOutByte.machineData)
          Tools.ShippingFGCircuitS2vLink.root_hss i bools bits S₂ Ss j) [38, 39, 40, 41, 42, 43] =
      callArgVals synth_hftPcieOutByte.machineData
        bools (Tools.ShippingMachineAuto.extendBits bits 5 8 (synth_hftPcieOutByte.machineCall_0 i bools bits S₂ Ss)) j
        (teleState synth_hftPcieOutByte.machineInners (d := synth_hftPcieOutByte.machineData)
          Tools.ShippingFGCircuitS2vLink.root_hss i bools bits S₂ Ss j) (callArgsOf synth_hftPcieOutByte.machineData 1) := by
    kernel_rfl
  have h1 := synth_hftPcieOutByte.machine_arg_1 i bools bits S₂ Ss j
  rw [e1.trans h1]
  constructor
  · delta childRange
    exact Tools.ShippingMachineClose.Zip₂.cons (BitVec.isLt _) (Tools.ShippingMachineClose.Zip₂.cons (BitVec.isLt _)
      (Tools.ShippingMachineClose.Zip₂.cons (BitVec.isLt _) (Tools.ShippingMachineClose.Zip₂.cons (BitVec.isLt _)
      (Tools.ShippingMachineClose.Zip₂.cons (BitVec.isLt _) (Tools.ShippingMachineClose.Zip₂.cons (BitVec.isLt _)
        Tools.ShippingMachineClose.Zip₂.nil)))))
  · have hp1 : portIdx Sparkle.IP.Bus.PCIe.tlpCplByte.machineData.bsIn 1 = 0 := by decide
    have hp2 : portIdx Sparkle.IP.Bus.PCIe.tlpCplByte.machineData.bsIn 2 = 1 := by decide
    have hp3 : portIdx Sparkle.IP.Bus.PCIe.tlpCplByte.machineData.bsIn 3 = 2 := by decide
    have hp4 : portIdx Sparkle.IP.Bus.PCIe.tlpCplByte.machineData.bsIn 4 = 3 := by decide
    have hp5 : portIdx Sparkle.IP.Bus.PCIe.tlpCplByte.machineData.bsIn 5 = 4 := by decide
    have hp6 : portIdx Sparkle.IP.Bus.PCIe.tlpCplByte.machineData.bsIn 6 = 5 := by decide
    delta childValue Sparkle.IP.Bus.PCIe.tlpCplByte.machineSource
    simp only [decV, hp1, hp2, hp3, hp4, hp5, hp6, List.getD_cons_zero, List.getD_cons_succ,
      BitVec.ofNat_toNat, BitVec.setWidth_eq]
    kernel_rfl

/-- **the source's call facts for the concrete root** (`CallsEq`): both calls -/
theorem rootS_callsEq : rootS.CallsEq := by
  intro i bools bits S₂ Ss _ k args kd f j hargs hkd hf
  have hins := args_insts
  rcases k with _ | _ | k
  · have ha : args = [6] := by
      rw [hins] at hargs; simpa using hargs.symm
    subst ha
    have hkd' : kd = Sparkle.IP.Net.HTTP.httpGetByte.machineData := by
      simpa [kidData] using hkd.symm
    have hf' : f = childValue Sparkle.IP.Net.HTTP.httpGetByte.machineSource Sparkle.IP.Net.HTTP.httpGetByte.machineData.bsIn defaultDomain := by
      simpa [kidFs] using hf.symm
    subst hkd' hf'
    obtain ⟨hr, hv⟩ := calls0 i bools bits S₂ Ss j
    refine ⟨by decide +kernel, hr, ?_⟩
    rw [hv]
    show _ = posEnc _ _ (rootS.kD + 0) _
    rw [kind0]
    rfl
  · have ha : args = [38, 39, 40, 41, 42, 43] := by
      rw [hins] at hargs; simpa using hargs.symm
    subst ha
    have hkd' : kd = Sparkle.IP.Bus.PCIe.tlpCplByte.machineData := by
      simpa [kidData] using hkd.symm
    have hf' : f = childValue Sparkle.IP.Bus.PCIe.tlpCplByte.machineSource Sparkle.IP.Bus.PCIe.tlpCplByte.machineData.bsIn defaultDomain := by
      simpa [kidFs] using hf.symm
    subst hkd' hf'
    obtain ⟨hr, hv⟩ := calls1 i bools bits S₂ Ss j
    refine ⟨by decide +kernel, hr, ?_⟩
    rw [hv]
    show _ = posEnc _ _ (rootS.kD + 1) _
    rw [kind1]
    rfl
  · have h2 : kidData[k + 1 + 1]? = none := by simp [kidData]
    rw [h2] at hkd
    cases hkd

/-- **`rootS.SrcEq`**: the connection of the ORIGINAL value `R` to `machineSource` (and the fields, the witnesses, the source's call facts), for the concrete root.  No IR. -/
theorem rootS_srcEq : rootS.SrcEq := ⟨rootS_srcCore, rootS_callsEq⟩

end Tools.ShippingFGCircuitS3tCalls
