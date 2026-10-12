import Tools.ShippingChecksDerived3
import Tools.ShippingChecksPacked
import Tools.ShippingKidsChildIface

/-! # Output checks from runs (G1): children's outputs, and a parent's `outsCheck`

Theorems over every run of the full entry — no per-declaration evaluation of
the check itself.

* `leaf_run_outsAssigned`: the module the full entry returns on a machine
  WITHOUT calls and WITH a register assigns every output port. From one run:
  the core module is the register-closed transition
  (`synthesizeMachineCertified_runs`), the transition ends in
  `assign out = w` (`transition_packed`) and `closeLets` keeps that
  (`closeLets_packed`), so `closeMachine` writes one assignment per output
  (`closeMachine_outsAssigned`); the cleanup keeps body and outputs and a
  slot's register is a statement (`MachineWired`), so the merge is a checked
  refinement or the identity (`entry_outsAssigned`). Hypotheses: those of
  `Tools.ShippingSeqChildIface.seqChild_iface`, plus a slot.
* `leaf_real_outsAssigned`: the same from a `RealChild` witness.
* `parent_run_outsCheck0`: for a run of the full entry on a machine WITH
  calls and a register (the hypotheses of
  `Tools.ShippingKidsChildIface.kidsChild_iface`), with the gate
  `hierBinds b`, and every module of the run's design assigning its outputs
  (`outsA`): the depth-0 `outsCheck` of the PRINTED module, and every
  instance statement of the printed module resolves in the design.

What is NOT proved here
* `outsA` for the design's modules from the parent's run: it needs "every
  module of the full entry's design is the full-entry module of a real child
  (or of a descendant)" — `ChildIfaceD` has the modules' NAMES
  (`desNames`) and that instances resolve (`resolves`), not which module
  each is. With that export, `leaf_real_outsAssigned` discharges `outsA`
  for children without calls and with a register.
* `hierBinds b` (the gate): a hypothesis. Whether it holds on the real
  parents is what `Tests/Compiler/ChecksDerivedTest.lean` measures.
* That the design `D` of `ships_design_svN_all` is the full entry's design
  this theorem speaks about: not checked.
* Slotless children; memory children; the other conjuncts. -/
namespace Tools.ShippingChecksRun
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

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 2000000 in
/-- **Every run of the full entry on a machine without calls and with a
register returns a module that assigns every output.** -/
theorem leaf_run_outsAssigned {c : Name} (d : MachineData) (ok : d.ok = true)
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
    Tools.ShippingDesignSVBack.outsAssigned b = true := by
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
  exact Tools.ShippingChecksDerived3.entry_outsAssigned hrawA hzb hzo hnA hpost

/-- **A real child without calls and with a register assigns every output**
— from its OWN run (the `RealChild` witness). -/
theorem leaf_real_outsAssigned {c : Name} (d : MachineData) (ok : d.ok = true)
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
    {y : Res} (h : RealChild mref cref c y) :
    Tools.ShippingDesignSVBack.outsAssigned y.1 = true := by
  obtain ⟨mctx', cctx', w, w', hw, hr⟩ := h.inv
  exact leaf_run_outsAssigned d ok hbody hno hsl hSS outTy hw hr
    (Tools.ShippingReflectCtx.MachineDefines.ctx entry) (closes mctx' cctx')

set_option maxHeartbeats 2000000 in
/-- **The depth-0 `outsCheck` of the printed module of a machine with calls,
over every run of the full entry**, and the resolution of the printed
module's instance statements. Hypotheses: those of `kidsChild_iface`, the
gate `hierBinds b`, and `outsA` — every module of the run's design assigns
its outputs. -/
theorem parent_run_outsCheck0 {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hsl : d.shape.layout.slots ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (kD : Nat) (hkD : kD ≤ d.bsIn.length)
    (hIlen : (d.bsIn.drop kD).length = d.shape.insts.length)
    (hSL : ∀ b ∈ d.slotBs ++ d.letBs, b.2 ≠ .domain)
    (hSlen : d.slotBs.length = d.shape.layout.slots.length)
    (hLlen : d.letBs.length = d.shape.layout.lets)
    (hNIn : machNIn d.shape = ((d.bsIn.take kD).filter (fun b => b.2 != .domain)).length)
    (namesK : Nat → List String)
    (hnomem : ∀ c ∈ d.shape.insts, Sparkle.Compiler.MachMemory.memChild? c.1 = none)
    (hkid : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      KidNames (d.shape.insts[k]).1 (namesK k) y.1 y.2)
    (hself : c.toString ∉ namesOf d namesK)
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Design}
    (hw : InvW mref cref w)
    (hr : RunsTo (synthesizeCombinational c) mctx mref cctx cref w (b, design) w')
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape)
    (hb : hierBinds b = true)
    (outsA : ∀ g ∈ design.modules, Tools.ShippingDesignSVBack.outsAssigned g = true) :
    Tools.ShippingDesignSVBack.outsCheck (childMap design.modules) 0 (checkedOptimize b) = true ∧
      ∀ mn iname conns, Stmt.inst mn iname conns ∈ (checkedOptimize b).body →
        ∃ mc, moduleByName design.modules mn = some mc := by
  have hI := kidsChild_iface d ok hbody hC hslots hdomB hins hsl outTy kD hkD hIlen hSL hSlen
    hLlen hNIn namesK hnomem hkid hself hw hr entry closes
  refine ⟨Tools.ShippingChecksDerived2.outsCheck0_opt hb hI.resolves
    (fun mn mc hmc _ => outsA mc (Tools.ShippingHierPremisesBase.moduleByName_mem hmc).1), ?_⟩
  intro mn iname conns hm
  exact hI.resolves mn iname conns
    ((Tools.ShippingChecksDerived2.checkedOptimize_inst_iff hb mn iname conns).mp hm)

end Tools.ShippingChecksRun
