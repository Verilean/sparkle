import Tools.ShippingCallsRunG
import Tools.ShippingMachineDepthRunR
import Tools.ShippingTransitionClosed
import Tools.ShippingReflectCtx

/-! # A sequential (or several-output) machine child without calls, from its own run

What the general closing (`closeInstsG_of_facts`) asks of a child's module,
as ONE predicate (`ChildIfaceG`), and that a run of the FULL entry on a
machine-route declaration WITHOUT calls returns a module with it:

* the non-clock input ports are the declaration's hardware arguments,
  distinct;
* the output ports are the layout's outputs, distinct, none an input, the
  clock or the reset;
* the body is assignments and registers (no instance, no memory);
* the name is the declaration's, the design has no module.

From ONE run witness: the core run reaches the machine synthesis, which does
not fall back (the CHILD's closing); the raw module's wiring is
`MachineWired`, by the core entry's theorem at this run
(`synthesizeCombinationalCore_machine_sound` on the declaration's data); the post-passes (zero-width cleanup, checked
merge) keep the ports, the name and the statement kinds.

Data conditions, decided per declaration: the endpoint's `ok`, no call, the
output types of their widths. Children with calls of their own: not here. -/
namespace Tools.ShippingSeqChildIface
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData Tools.ShippingMachineCloses
open Tools.ShippingMixedEntrySoundness
open Tools.ShippingGateChildComb Tools.ShippingChildInv
open Tools.ShippingInstStmtG Tools.ShippingCallsAssemblyG Tools.ShippingTransitionClosed
open Sparkle.IR.RefineCheck (mergeChecked)
open Sparkle.IR.OptCheck (seqStmtOk)

/-- **What the general closing asks of a child's full-entry result.** -/
structure ChildIfaceG (c : Name) (nArgs : Nat) (outs : List String)
    (b : Sparkle.IR.AST.Module) (design : Design) : Prop where
  name : b.name = c.toString
  design : design.modules = []
  nIn : (inPortsOf b).length = nArgs
  inNd : ((inPortsOf b).map (·.name)).Nodup
  outs : b.outputs.map (·.name) = outs
  outsIn : ∀ p ∈ b.outputs, (∀ q ∈ inPortsOf b, q.name ≠ p.name) ∧ p.name ≠ "clk" ∧
    p.name ≠ "rst"
  outsNd : (b.outputs.map (·.name)).Nodup
  seqOk : b.body.all seqStmtOk = true

theorem closeLets_name {K : Nat} {t t' : Sparkle.IR.AST.Module} (h : closeLets K t = some t') :
    t'.name = t.name := by
  unfold closeLets at h
  split at h
  · cases h; rfl
  · split at h
    · cases h
    · dsimp only at h
      split at h
      · cases h
      · split at h
        · cases h; rfl
        · cases h

theorem closeMachine_name (lay : Layout) (t : Sparkle.IR.AST.Module) :
    (closeMachine lay t).name = t.name := by
  unfold closeMachine
  split <;> rfl

/-- The checked merge of an assignments-and-registers body is one. -/
theorem mergeChecked_seqOk {r : Sparkle.IR.AST.Module} (h : r.body.all seqStmtOk = true) :
    (mergeChecked r).body.all seqStmtOk = true := by
  unfold mergeChecked
  dsimp only
  split
  · rename_i hall
    have hb : (Sparkle.IR.RegDedup.mergeDuplicates r).body.all Sparkle.IR.RegDedup.isAssign =
        true := by
      unfold Sparkle.IR.RegDedup.mergeDuplicates
      simp only [hall, if_true]
      split
      · rename_i hv
        exact Tools.ShippingMachineShipsHier.validateMerge_go_assign _ _ _ hv hall
      · exact hall
    rw [List.all_eq_true] at hb ⊢
    intro st hst
    have := hb st hst
    cases st <;> simp_all [Sparkle.IR.RegDedup.isAssign, seqStmtOk]
  · split
    · rename_i _ hrc
      exact Tools.ShippingMachineShipping.refineCheck_stmtOk_o hrc
    · exact h

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 2000000 in
/-- **The interface of a machine child without calls, at its full entry.** -/
theorem seqChild_iface {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hno : d.shape.insts = [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Design}
    (hw : InvW mref cref w)
    (hr : RunsTo (synthesizeCombinational c) mctx mref cctx cref w (b, design) w')
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closesM : MachineCloses mctx mref cctx cref c d.shape) :
    ChildIfaceG c
      ((d.shape.binders.take (d.shape.binders.length - d.shape.layout.slots.length -
        d.shape.layout.lets)).filter fun x => x.2 != .domain).length
      (d.shape.layout.outs.map (·.name)) b design := by
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
  obtain ⟨-, -, -, -, hdesign, hname⟩ :=
    transition_closed nd len hrun hm nameLegal hposv d.packed hwf hb' hv' hbody
  have hMname : M.name = c.toString := by
    rw [hMeq, closeMachine_name, closeLets_name hcl, hname]
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
  obtain ⟨regs, -, -, lets, -, wired, -⟩ :=
    hP d.dom d.kb d.kv d.vw d.bpos d.vpos d.letFields d.core.2 hwf hb' hv' hbody hfit houtfit
  obtain ⟨-, -, -, -, -, -, -, houtsM, hinsM, -, hclean, -⟩ := wired
  obtain ⟨⟨hzb, -, hzi, hzo⟩, -, -, -, hinNd, -, houtIn, -, hseq⟩ := hclean hno outTy
  have hinsM' := hinsM hno
  -- the cleaned module
  have hX : ∀ X : Sparkle.IR.AST.Module, X.inputs = M.inputs → X.outputs = M.outputs →
      X.name = M.name → X.body.all seqStmtOk = true →
      ChildIfaceG c
        ((d.shape.binders.take (d.shape.binders.length - d.shape.layout.slots.length -
          d.shape.layout.lets)).filter fun x => x.2 != .domain).length
        (d.shape.layout.outs.map (·.name)) X design := by
    intro X hXi hXo hXn hXb
    have hin : inPortsOf X = machPorts c ids cache
        (d.shape.binders.take (d.shape.binders.length - d.shape.layout.slots.length -
          d.shape.layout.lets)) := by
      unfold inPortsOf
      rw [hXi]
      exact hinsM'
    have houtNames : X.outputs.map (·.name) = d.shape.layout.outs.map (·.name) := by
      rw [hXo, houtsM, List.map_map]
      rfl
    refine ⟨by rw [hXn, hMname], hdesM (by rw [hDeq, hD, hdesign]; rfl), ?_, ?_, houtNames, ?_,
      by rw [houtNames]; exact outsNodup, hXb⟩
    · rw [hin]
      exact Tools.ShippingMachineCompose.machPorts_length _ (by
        rw [List.length_take, hlenIds]
        omega)
    · unfold inPortsOf
      rw [hXi]
      exact hinNd.sublist ((List.filter_sublist).map _)
    · intro p hp
      have hpo : p.name ∈ M.outputs.map (·.name) := by
        rw [← hXo]
        exact List.mem_map_of_mem hp
      have hnotIn := houtIn p.name hpo
      have hpn : p.name ∈ d.shape.layout.outs.map (·.name) := by
        rw [← houtNames]
        exact List.mem_map_of_mem hp
      obtain ⟨o, ho, hoe⟩ := List.mem_map.mp hpn
      refine ⟨fun q hq e => hnotIn ?_, ?_⟩
      · unfold inPortsOf at hq
        rw [hXi] at hq
        rw [← e]
        exact List.mem_map_of_mem (List.mem_filter.mp hq).1
      · rw [← hoe]
        exact outName_ne_clk (outsOk o ho).2
  have hZ := hX (Sparkle.IR.ZeroWidth.dropZeroWidthModule M) hzi hzo
    (Tools.ShippingMachineDepthRun.dropZW_name M) (by rw [hzb]; exact hseq)
  rcases hpost with rfl | rfl
  · exact hZ
  · obtain ⟨p1, p2, -⟩ := Sparkle.IR.RefineCheck.mergeChecked_ports
      (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)
    exact hX _ (p1.trans hzi) (p2.trans hzo)
      ((Tools.ShippingMachineDepthRun.mergeChecked_name _).trans
        (Tools.ShippingMachineDepthRun.dropZW_name M))
      (mergeChecked_seqOk (by rw [hzb]; exact hseq))

/-- **A real child of a machine declaration without calls has the interface**
— from its OWN run (the `RealChild` witness): the declaration's reflection
moved to that run's contexts, the child's closing there (a machine without
calls closes in every context: `c.machine_closes`). -/
theorem seqChild_of_real {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hno : d.shape.insts = [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : ∀ (mctx' : Meta.Context) (cctx' : Core.Context),
      MachineCloses mctx' mref cctx' cref c d.shape)
    {y : Res} (h : RealChild mref cref c y) :
    ChildIfaceG c
      ((d.shape.binders.take (d.shape.binders.length - d.shape.layout.slots.length -
        d.shape.layout.lets)).filter fun x => x.2 != .domain).length
      (d.shape.layout.outs.map (·.name)) y.1 y.2 := by
  obtain ⟨mctx', cctx', w, w', hw, hr⟩ := h.inv
  exact seqChild_iface d ok hbody hno outTy hw hr
    (Tools.ShippingReflectCtx.MachineDefines.ctx entry) (closes mctx' cctx')

end Tools.ShippingSeqChildIface
