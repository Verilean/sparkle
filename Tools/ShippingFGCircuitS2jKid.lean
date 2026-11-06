import Tools.ShippingFGCircuitS2dKids
import Tools.ShippingGen2SlotlessLeaf
import Tools.ShippingFGCircuitS2jCopy
set_option autoImplicit false
-- FG circuit pilot S2j, unit 2: a combinational leaf child's `ShipsRes` from its own run (the children of the non-leaf root). No `sorry`, no `axiom`, no `native_decide`, no TRUSTED, no new law. docs/FG-CIRCUIT-PILOT.md §36.

namespace Tools.ShippingFGCircuitS2jKid
open Lean Meta Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData Tools.ShippingMachineCloses
open Tools.ShippingMixedEntrySoundness
open Tools.ShippingCallsShape Tools.ShippingCallsRun Tools.ShippingCallsAssembly
open Tools.ShippingGateChildComb Tools.ShippingChildInv Tools.ShippingRankRun
open Tools.ShippingMachineChildComb Tools.ShippingTransitionClosed Tools.ShippingCallsGate
open Tools.ShippingChildInvA Tools.ShippingChildVCA Tools.ShippingChildCacheA Tools.ShippingChildFresh
open Tools.ShippingChildRunA Tools.ShippingChildRunAKids Tools.ShippingChildRunAMain Tools.ShippingChildComposeC
open Tools.ShippingGen2 Tools.ShippingChildBndCore Tools.ShippingFGCircuitS1qLinked Tools.ShippingFGCircuitS1qHead
open Tools.ShippingFGCircuitLinked
open Tools.ShippingFGCircuitS1iHead (HeadAt)
open Tools.ShippingFGCircuitS1oHead (GetEnvProfileAt headAt_of_profileOff)
open Tools.ShippingFGCircuitCover Tools.ShippingFGCircuitFinal4
open Tools.ShippingEntryReadsLinked (envAt)
open Tools.ShippingGen5Env (ReadsAt)
open Tools.ShippingGen5EnvFrame3 (CellPrem)
open Tools.ShippingFGCircuitS1hFrame (getEnvFrame_of_cellPrem)

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 2000000 in
/-- (S2j copy of `machineChild_ifaceK`, conclusion extended by the core run, the machine run and `D.modules = []`) **`machineChild_ifaceA` with the all-world `MachineDefines` replaced by the run-local linked boundary** (the machine run is taken by `machine_run_of_coreC` on the run's own core chain; `entry` is asked only of THIS child run's core run, at its start world `w`) ( `synthesizeMachineCertified_runsA`; the rest of the proof is the old one) -/
theorem kidRunK (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx) {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hS : d.gateCallsOk nDecl = true) (hK : d.shape.layout.lets ≠ 0)
    (hno : d.shape.insts = []) (hsl : d.shape.layout.slots = [])
    (houts : ∃ o, d.shape.layout.outs = [o] ∧ o.name = "out")
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Design}
    (hw : JQC O (dv w) w)
    (hr : RunsTo (synthesizeCombinational c) mctx mref cctx cref w (b, design) w')
    (entry : ∀ {M : Sparkle.IR.AST.Module} {D : Design} {w1 : Void IO.RealWorld},
      RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1 →
      MachineDefinesLinked mctx mref cctx cref c d.shape w M D w1)
    (closes : MachineCloses mctx mref cctx cref c d.shape) :
    ∃ (M : Sparkle.IR.AST.Module) (D : Design) (w1 : Void IO.RealWorld),
      RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1 ∧
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨ b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)) ∧
      Tools.ShippingServedRealA.MachineRunJQC O mctx cctx (dv w + 1) c d.shape M D ∧ D.modules = [] ∧
      (ChildComb b ∧
        b.inputs.length = ((d.shape.binders.take nDecl).filter fun x => x.2 != .domain).length ∧
        b.name = (Sparkle.IR.ModuleName.ofDecl c) ∧ design.modules = []) := by
  obtain ⟨M, D, w1, hcore, hpost, hdesM⟩ := synthesizeCombinational_parts hr
  obtain ⟨tenv, bb, r, w9, w10, hrun9, hw9, hres⟩ :=
    machine_run_of_coreC O hA hcore (entry hcore) hw.1 (Or.inr hw.2)
  have hne := closes (profLogIO bb) w9 r w10 hrun9
  cases r with
  | none => exact absurd rfl hne
  | some res =>
  have hres' := hres res rfl
  subst hres'
  obtain ⟨t, t', d₀, run, hcl, hmt⟩ :=
    synthesizeMachineCertified_runsA O (bodyStepC_of_tele O T) hA (htr_of_tele O hA T (dv w) tenv) hw9 hrun9
  rcases hmt with ⟨-, hMeq, hDeq⟩ | ⟨hne', -⟩
  rotate_left
  · exact absurd hno hne'
  simp only [MachineData.gateCallsOk, MachineData.callsOk, Bool.and_eq_true, decide_eq_true_eq,
    List.isEmpty_iff] at hS
  obtain ⟨⟨⟨⟨⟨⟨hnIn, hargs⟩, hfields⟩, hcoreR⟩, hslots⟩, hdomB⟩, -⟩ := hS
  simp only [MachineData.ok, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at ok
  obtain ⟨hlen, hlets, positive, _, _, _, outsOk, outsNodup, hwf, hb, hv,
    _, _, hscoped, _, _, _, _, _, _, _, _⟩ := ok
  obtain ⟨hfitL, -⟩ := scoped_fit d.letBs d.letFields _ hscoped
  have hlsLen : d.letFields.length = d.ls.length := by simp [MachineData.letFields]
  have hletBs : d.letBs.length = d.shape.binders.length - (d.nIn + d.ss.length) := by
    simp [MachineData.letBs]
  have hposv : PositiveBinders d.shape.binders := by
    intro name n hmem
    have := List.all_eq_true.mp positive _ hmem
    simpa using this
  have hb' : ∀ j, j < d.kb → ∃ name, d.shape.binders[d.bpos j]? = some (name, .bool) := by
    intro j hj
    have := hb j hj
    cases h : d.shape.binders[d.bpos j]? with
    | none => rw [h] at this; cases this
    | some b =>
      obtain ⟨name, k⟩ := b
      rw [h] at this
      simp only [Option.map_some, Option.some.injEq] at this
      exact ⟨name, by rw [← this]⟩
  have hv' : ∀ j, j < d.kv → ∃ name, d.shape.binders[d.vpos j]? = some (name, .bits (d.vw j)) := by
    intro j hj
    have := hv j hj
    cases h : d.shape.binders[d.vpos j]? with
    | none => rw [h] at this; cases this
    | some b =>
      obtain ⟨name, k⟩ := b
      rw [h] at this
      simp only [Option.map_some, Option.some.injEq] at this
      exact ⟨name, by rw [← this]⟩
  obtain ⟨ids, cache, returned, st, nd, len, hrun, hm, hD, nameLegal⟩ :=
    synthesizeMixedCertified_returns run
  have hA : (d.shape.binders.take nDecl).length = nDecl := by
    rw [List.length_take]
    omega
  have hsplit : d.shape.binders = d.shape.binders.take nDecl ++ d.shape.binders.drop nDecl :=
    (List.take_append_drop ..).symm
  have hKne : d.letBs.length ≠ 0 := by rw [← hlets]; exact hK
  have hBlen : (d.shape.binders.drop nDecl).length =
      d.shape.insts.length + d.ss.length + d.letBs.length := by
    rw [List.length_drop]
    omega
  have hcoreWF := core_wf d.core.2 d.letFields hwf
  obtain ⟨PI, ls, bodyB, w, P, bnd, hin, hPI, hlsL, hndI, hinW, hwAlloc, hbodyT, hacy, hnamed, hnw,
      hP, hF, hdes, hname⟩ :=
    transition_calls_facts (cs := d.callBounds) nd len hrun hm nameLegal hposv d.letFields d.core.2
      hwf hb' hv' hbody hsplit hdomB hBlen hfitL
      (by rw [hA]; exact fieldsOK_of_B d.letFields 0 d.core.2 hfields hwf)
      (by
        rw [hA, hlsLen]
        exact uses_of_reads (fun j hj hr => ⟨hj, posOk_rule hr⟩)
          (fun j hj hr => ⟨hj, posOk_rule hr⟩) d.core.2 hcoreWF hcoreR)
  obtain ⟨hclosedT, -, ⟨ow, pb⟩, ready, -, -⟩ :=
    transition_closed nd len hrun hm nameLegal hposv d.packed hwf hb' hv' hbody
  rw [hlets] at hcl
  have hss : d.ss.length = 0 := by rw [hslots, hsl]; rfl
  have h0 : d.shape.insts.length + d.ss.length = 0 := by rw [hno, hss]; rfl
  obtain ⟨hC, hI, hN⟩ := slotless_childComb_full (b := b) hKne hcl hin (by rw [hlsL, h0]; omega)
    hndI hinW hwAlloc hbodyT hacy hnamed
    (fun al core h => by
      obtain ⟨es, ws, hf, hal, hc⟩ := hF al core h
      rw [h0, List.drop_zero] at hal
      exact ⟨es, ws, hf, hal, hc⟩)
    hclosedT ready.typed ready.wiresNodup pb.wires outsOk outTy hsl houts (hMeq ▸ hpost)
  have hD0 : D.modules = [] := by rw [hDeq, hD, hdes]; rfl
  exact ⟨M, D, w1, hcore, hpost, ⟨tenv, bb, w9, w10, hrun9, hw9⟩, hD0, hC, by rw [hI, hPI], by rw [hN, hname], hdesM hD0⟩

end Tools.ShippingFGCircuitS2jKid

#print axioms Tools.ShippingFGCircuitS2jKid.kidRunK
