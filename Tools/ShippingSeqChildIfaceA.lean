import Tools.ShippingSeqChildIface
import Tools.ShippingLeafInputWidthsA
import Tools.ShippingChildRunA
-- UNBUILT (unit CPX): see REPORT-CPX.md for run names / exits.
-- No `sorry`, no `axiom`, no `native_decide`, no new law / field. Witness `O : RefLawsAOps MkRefd mref cref`.

/-! # `seqChild_of_realA`: the leaf child interface from a `RealChildA` (unit CPX)

Port of `Tools.ShippingSeqChildIface.seqChild_of_real` (`RealChild`, old `InvW` start, `machine_run_of_core`
from a `ChildBnd`) to the new boundary. The run inside `RealChildA O c y` starts in a world with
`O.quiet`, `sv = some synthesizeChild` and a `RealChildA`-only cache, so it is in `JQ O.quiet (dv w)` with
`CacheInvA O (cv w)`; `machine_run_of_coreA` replaces `machine_run_of_core`, and
`synthesizeMachineCertified_leaf_runs` (no calls: the closing of calls is not reached) replaces
`synthesizeMachineCertified_runs`. Premises: `O`, the reflection `MachineDefines`, the data conditions,
`closes` (old, every context). `RealChildA` is a HISTORY of a past run; the conclusion is about the
module that run returned, not about the current environment. No `RefLawsATele`. -/
namespace Tools.ShippingSeqChildIfaceA
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
open Tools.ShippingSeqChildIface
open Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildVCA Tools.ShippingChildCacheA
open Tools.ShippingChildRunA Tools.ShippingCallWidthsChildRealA Tools.ShippingChildBndCore

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 2000000 in
/-- The interface of a machine child without calls, at its full entry, from a run in a `JQ` world
whose cache half holds (or depth 0). -/
theorem seqChild_ifaceA {c : Name} (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hno : d.shape.insts = [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    {D : Nat} {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Design}
    (hw : JQ O.quiet D w) (hc : D = 0 ∨ CacheInvA O (cv w))
    (hr : RunsTo (synthesizeCombinational c) mctx mref cctx cref w (b, design) w')
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closesM : MachineCloses mctx mref cctx cref c d.shape) :
    ChildIfaceG c
      ((d.shape.binders.take (d.shape.binders.length - d.shape.layout.slots.length -
        d.shape.layout.lets)).filter fun x => x.2 != .domain).length
      (d.shape.layout.outs.map (·.name)) b design := by
  obtain ⟨M, D', w1, hcore, hpost, hdesM⟩ := synthesizeCombinational_parts hr
  obtain ⟨tenv, bb, r, w9, w10, hrun9, hw9, hres⟩ := machine_run_of_coreA O hA hcore entry hw hc
  have hne := closesM (profLogIO bb) _ _ _ hrun9
  cases r with
  | none => exact absurd rfl hne
  | some res =>
  have hres' := hres res rfl
  subst hres'
  obtain ⟨t, t', d₀, run, hcl, hMeq, hDeq⟩ := synthesizeMachineCertified_leaf_runs hno hrun9
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
  have hMname : M.name = (Sparkle.IR.ModuleName.ofDecl c) := by
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

/-- **A `RealChildA` of a machine declaration without calls has the interface** — from its OWN run.
Port of `seqChild_of_real`. -/
theorem seqChild_of_realA {c : Name} (O : RefLawsAOps MkRefd mref cref) (d : MachineData)
    (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hno : d.shape.insts = [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : ∀ (mctx' : Meta.Context) (cctx' : Core.Context),
      MachineCloses mctx' mref cctx' cref c d.shape)
    {y : Res} (h : RealChildA O c y) :
    ChildIfaceG c
      ((d.shape.binders.take (d.shape.binders.length - d.shape.layout.slots.length -
        d.shape.layout.lets)).filter fun x => x.2 != .domain).length
      (d.shape.layout.outs.map (·.name)) y.1 y.2 := by
  cases h with
  | run mctx' cctx' w w' adm cache synth quiet hr =>
    exact seqChild_ifaceA O adm d ok hbody hno outTy ⟨quiet, synth, rfl⟩ (Or.inr (fun c r h => cache c r h)) hr
      (Tools.ShippingReflectCtx.MachineDefines.ctx entry) (closes mctx' cctx')

end Tools.ShippingSeqChildIfaceA
