import Tools.ShippingCallsGate
import Tools.ShippingMachineChildComb

/-! # A slotless machine child, from its own run

A machine-route child without registers and without calls (`pickByteH`): a
run of the FULL entry on it, from an invariant world, returns a module with
the child-side facts of the one-output closing — `ChildComb`, as many input
ports as the declaration has hardware binders, the declaration's name, no
module in its design.

From ONE run witness: the entry's core run reaches the machine synthesis
(`machine_run_of_core`), which does not fall back (`MachineClosesAt` of the
CHILD — proved for a let-only child, `c.machine_closes`); its harness run
gives the transition's facts (`transition_calls_facts`, `transition_closed`:
the same run), `closeLets` succeeded, and the module is `closeMachine` of it
(`slotless_childComb_full`).

Data conditions, decided per declaration: the endpoint's `ok`, S3
(`gateCallsOk`: here the `let`s' scoping), at least one `let`, no call, no slot, one output named
`out`, output types of their widths. -/
namespace Tools.ShippingMachineChildRun
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData Tools.ShippingMachineCloses
open Tools.ShippingMixedEntrySoundness
open Tools.ShippingCallsShape Tools.ShippingCallsRun Tools.ShippingCallsAssembly
open Tools.ShippingGateChildComb Tools.ShippingChildInv Tools.ShippingRankRun
open Tools.ShippingInlineSoundness (EntryDefines)

open Tools.ShippingMachineChildComb Tools.ShippingTransitionClosed Tools.ShippingCallsGate

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 2000000 in
/-- **The interface of a slotless machine child's full-entry module.** -/
theorem machineChild_iface {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hS : d.gateCallsOk nDecl = true) (hK : d.shape.layout.lets ≠ 0)
    (hno : d.shape.insts = []) (hsl : d.shape.layout.slots = [])
    (houts : ∃ o, d.shape.layout.outs = [o] ∧ o.name = "out")
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Design}
    (hw : InvW mref cref w)
    (hr : RunsTo (synthesizeCombinational c) mctx mref cctx cref w (b, design) w')
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape) :
    ChildComb b ∧
      b.inputs.length = ((d.shape.binders.take nDecl).filter fun x => x.2 != .domain).length ∧
      b.name = (Sparkle.IR.ModuleName.ofDecl c) ∧ design.modules = [] := by
  obtain ⟨M, D, w1, hcore, hpost, hdesM⟩ := synthesizeCombinational_parts hr
  obtain ⟨_, bb, r, w9, w10, hrun9, hw9, hd9, hres⟩ :=
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
  exact ⟨hC, by rw [hI, hPI], by rw [hN, hname], hdesM (by rw [hDeq, hD, hdes]; rfl)⟩

/-- **A real child of a slotless machine declaration has the interface** —
from its OWN run (the `RealChild` witness): the declaration's reflection moved
to that run's contexts, the child's closing there (a let-only child closes in
every context). -/
theorem machineChild_of_real {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hS : d.gateCallsOk nDecl = true) (hK : d.shape.layout.lets ≠ 0)
    (hno : d.shape.insts = []) (hsl : d.shape.layout.slots = [])
    (houts : ∃ o, d.shape.layout.outs = [o] ∧ o.name = "out")
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : ∀ (mctx' : Meta.Context) (cctx' : Core.Context),
      MachineCloses mctx' mref cctx' cref c d.shape)
    {y : Res} (h : RealChild mref cref c y) :
    ChildIface c ((d.shape.binders.take nDecl).filter fun x => x.2 != .domain).length y.1 y.2 := by
  obtain ⟨mctx', cctx', w, w', hw, hr⟩ := h.inv
  exact machineChild_iface d ok hbody hS hK hno hsl houts outTy hw hr
    (Tools.ShippingReflectCtx.MachineDefines.ctx entry)
    (machineClosesAt_of_closes (closes mctx' cctx'))

end Tools.ShippingMachineChildRun
