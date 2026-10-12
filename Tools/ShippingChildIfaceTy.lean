import Tools.ShippingChecksCore

/-! # A leaf child's output ports WITH their types (G1, conjunct 8)

`instOutWidthsOk C (declWidth b) b.body` asks, for every instance statement
of the parent and every output port `p` of the child connected to a wire
`w`, `declWidth b w = p.ty.bitWidth`. The child interfaces
(`ChildIfaceG`, `ChildIfaceD`) carry the output port NAMES only
(`outs : b.outputs.map (·.name) = …`). This file gives the child side with
the types, as a NEW structure (the existing ones are not changed):

* `ChildOutTys outs b`: the child module's output ports are the layout's
  fields, names and types;
* `leaf_run_outputs` / `leaf_real_outTys`: a machine without calls and with
  a register provides it, over every run of its full entry / from its
  `RealChild` witness — the closed machine's outputs
  (`closeMachine_outputs`), kept by the cleanup and by the checked merge.
  The proof up to the cleanup facts is `leaf_run_outsAssigned`'s (my own),
  copied by a script.

What is NOT here, and what conjunct 8 still needs on the PARENT side: for
the call's output wire `w` (a port name of the transition at position
`machNIn + k`, removed from the inputs by the closing), that
`declWidth b w` is the width of the child's field — i.e. that the parent's
declared wire for the call port has the type the transition gave the call's
result, and that this type is the child's output field's. `MachineWired`
states the call statements (`CallStmtG`) and the ports' allocation, not the
declared widths of the call ports. Not derived.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingChildIfaceTy
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData Tools.ShippingMachineCloses
open Tools.ShippingMixedEntrySoundness
open Tools.ShippingGateChildComb Tools.ShippingChildInv
open Tools.ShippingInstStmtG Tools.ShippingCallsAssemblyG Tools.ShippingTransitionClosed
open Tools.ShippingSeqChildIface Tools.ShippingCallsKidsD Tools.ShippingKidsChildIface
open Sparkle.IR.RefineCheck (mergeChecked hierBinds)
open Sparkle.IR.OptCheck (seqStmtOk checkedOptimize)
open Tools.ShippingMachineLinked (childMap)

/-- The child module's output ports are the layout's output fields, with
their types. -/
structure ChildOutTys (outs : List OutField) (b : Sparkle.IR.AST.Module) : Prop where
  outputs : b.outputs = outs.map (fun o => ({ name := o.name, ty := o.ty } : Port))

/-- Each output port's width is its field's, under the endpoints' `outTy`. -/
theorem ChildOutTys.width {outs : List OutField} {b : Sparkle.IR.AST.Module}
    (h : ChildOutTys outs b) (outTy : ∀ o ∈ outs, o.ty.bitWidth = o.width) :
    ∀ p ∈ b.outputs, ∃ o ∈ outs, p.name = o.name ∧ p.ty.bitWidth = o.width := by
  intro p hp
  rw [h.outputs] at hp
  obtain ⟨o, ho, e⟩ := List.mem_map.mp hp
  exact ⟨o, ho, by rw [← e], by rw [← e]; exact outTy o ho⟩

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 2000000 in
/-- **A leaf machine's returned module has the layout's output ports, with
their types**, over every run of the full entry. -/

theorem leaf_run_outputs {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hno : d.shape.insts = [])
    (hsl : d.shape.layout.slots ≠ [])
    (hSS : d.ss.length = d.shape.layout.slots.length)
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Design}
    (hw : InvW mref cref w)
    (hr : RunsTo (synthesizeCombinational c) mctx mref cctx cref w (b, design) w')
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closesM : MachineCloses mctx mref cctx cref c d.shape) :
    b.outputs = d.shape.layout.outs.map (fun o => ({ name := o.name, ty := o.ty } : Port)) := by
  obtain ⟨M, D, w1, hcore, hpost, hdesM⟩ := synthesizeCombinational_parts hr
  have closes : MachineClosesAt mctx mref cctx cref c d.shape := machineClosesAt_of_closes closesM
  obtain ⟨bb, r, w9, w10, hrun9, hw9, hd9, hres⟩ :=
    machine_run_of_core hcore entry (ChildBnd.of_invW mctx cctx hw)
  have hne := closes bb _ _ _ hw9 hd9 hrun9
  cases r with
  | none => exact absurd rfl hne
  | some res =>
  have hres' := hres res rfl
  subst hres'
  obtain ⟨t, t', d₀, run, hcl, hmt⟩ := synthesizeMachineCertified_runs hw9 hrun9
  rcases hmt with ⟨-, hMeq, hDeq⟩ | ⟨hne', -⟩
  rotate_left
  · exact absurd hno hne'
  simp only [MachineData.ok, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at ok
  obtain ⟨hlen, hlets, positive, slotKinds, letKinds, layB, outsOk, outsNodup, hwf, hb, hv,
    hfit, houtfit, hscoped, _, _, _, _, _, _, _, _⟩ := ok
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
  obtain ⟨ids', cache', returned, st, nd, len, hrun, hm, hD, nameLegal⟩ :=
    synthesizeMixedCertified_returns run
  -- the transition ends in `assign out = w`, and so does the `let`-closed one
  obtain ⟨wP, hpw⟩ := Tools.ShippingChecksPacked.transition_packed nd len hrun hm d.packed hwf
    hb' hv' hbody
  obtain ⟨wP', hpw'⟩ := Option.isSome_iff_exists.mp
    (Tools.ShippingChecksPacked.closeLets_packed hcl hpw)
  have hrawA : Tools.ShippingDesignSVBack.outsAssigned M = true := by
    rw [hMeq]
    exact Tools.ShippingChecksDerived3.closeMachine_outsAssigned hpw'
  -- the raw module's wiring: the core entry's theorem at this run
  have layW : Tools.ShippingMachineClose.Zip₂
      (fun (f : SlotField) (b : Name × MixedGateBinder) =>
        f.width = machWidth b.2 ∧ b.2 ≠ .domain ∧ f.init < 2 ^ f.width)
      d.shape.layout.slots d.slotBs :=
    zip_of_all (by
      intro a b h
      simpa only [Bool.and_eq_true, decide_eq_true_eq] using h) layB
  obtain ⟨ids, -, hlenIds, cache, hP⟩ :=
    synthesizeCombinationalCore_machine_sound hcore entry closesM d.binders_split hlets hposv
      slotKinds letKinds (layW.imp fun _ _ h => h.1) outsOk outsNodup
  obtain ⟨regs, -, rlen, lets, -, wired, -⟩ :=
    hP d.dom d.kb d.kv d.vw d.bpos d.vpos d.letFields d.core.2 hwf hb' hv' hbody hfit houtfit
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hclean, -⟩ := wired
  obtain ⟨⟨hzb, -, -, hzo⟩, -, hregs, -, -, -, -, -, -⟩ := hclean hno outTy
  -- the core module has a register (a slot)
  obtain ⟨f0, hf0⟩ : ∃ f, d.shape.layout.slots[0]? = some f := by
    cases hs : d.shape.layout.slots with
    | nil => exact absurd hs hsl
    | cons f _ => exact ⟨f, rfl⟩
  obtain ⟨r0n, hr0n⟩ : ∃ r, regs[0]? = some r := by
    cases hrs : regs with
    | nil =>
      have hreg0 : regs.length = 0 := by simp [hrs]
      have hsb : d.slotBs.length = d.ss.length := by
        simp only [MachineData.slotBs, List.length_take, List.length_drop]
        omega
      have : d.shape.layout.slots.length = 0 := by omega
      rw [List.length_eq_zero_iff] at this; exact absurd this hsl
    | cons r _ => exact ⟨r, rfl⟩
  obtain ⟨_, _, rk0, inp0, hm0⟩ := hregs 0 r0n f0 hr0n hf0
  have hnA : M.body.all Sparkle.IR.RegDedup.isAssign = false := by
    apply List.all_eq_false.mpr
    exact ⟨_, hm0, by simp [Sparkle.IR.RegDedup.isAssign]⟩
  have hMout : M.outputs = d.shape.layout.outs.map
      (fun o => ({ name := o.name, ty := o.ty } : Port)) := by
    rw [hMeq]
    exact Tools.ShippingChecksCore.closeMachine_outputs hpw'
  rcases hpost with h | h
  · rw [h, hzo]
    exact hMout
  · rw [h, (Sparkle.IR.RefineCheck.mergeChecked_ports
      (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)).2.1, hzo]
    exact hMout

/-- **A real leaf child's output ports, with their types.** -/
theorem leaf_real_outTys {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hno : d.shape.insts = [])
    (hsl : d.shape.layout.slots ≠ [])
    (hSS : d.ss.length = d.shape.layout.slots.length)
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : ∀ (mctx' : Meta.Context) (cctx' : Core.Context),
      MachineCloses mctx' mref cctx' cref c d.shape)
    {y : Res} (h : RealChild mref cref c y) : ChildOutTys d.shape.layout.outs y.1 := by
  obtain ⟨mctx', cctx', w, w', hw, hr⟩ := h.inv
  exact ⟨leaf_run_outputs d ok hbody hno hsl hSS outTy hw hr
    (Tools.ShippingReflectCtx.MachineDefines.ctx entry) (closes mctx' cctx')⟩

end Tools.ShippingChildIfaceTy
