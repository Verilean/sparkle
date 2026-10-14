import Tools.ShippingFirstGateChild
import Tools.ShippingGatePorts

variable {tenv : Lean.Environment}

/-! # The port facts of a FIRST-gate child (worker N, round 14)

WRITTEN, NOT BUILT.

`Tools.ShippingGatePorts.gate_child_ports` / `gate_real_ports` give
`GateChildPorts c bs w y.1` (input ports = typed wires, the one output `out`
of width `w`, typed ordered body: `childTyped`, both width tables) for a
child of the SECOND (mixed) gate; their premises assume the first gate
refuses the declaration. `childAdd` is a FIRST-gate child
(`quoteDecl dn names n fe`). Here the same facts for the first gate, the
prelude replaced by the bridge exactly as in `first_child_fullFacts`:

* `first_child_base`: `gate_child_base` for the first gate — the raw module
  `M` of the run with `PrintBaseAt n M` and `TypedPostReady M`
  (`transition_facts` at the first gate's positions; the width is the
  fragment's `n`);
* `first_child_ports`: `GateChildPorts declName (firstBs dn names n) n b`
  (the proof of `gate_child_ports`, `first_child_fullFacts` for the input
  types, the name and the driven output);
* `first_real_ports`: the same for a `RealChild` (its own run). -/
namespace Tools.ShippingFirstGateChild
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.IR.Builder
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto
open Tools.ShippingMixedEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingEntrySoundness (RunsTo FExpr quoteDecl quoteBody)
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedExecutionSoundness
open Tools.ShippingInlineSoundness (EntryDefines)
open Tools.ShippingTransitionClosed
open Tools.ShippingGateChildComb
open Tools.ShippingGatePorts (GateChildPorts post_facts)

set_option linter.unusedSectionVars false

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 1000000 in
/-- **A first-gate child's raw module, with the output width NAMED**
(`gate_child_base` for the first gate). -/
theorem first_child_base {declName : Name} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Design} {dn : Name} {names : List Name} {n : Nat}
    {fe : FExpr}
    (hr : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, design) w')
    (entry : EntryDefines mctx mref cctx cref declName (quoteDecl dn names n fe))
    (hwf : fe.WF names.length n) (hn : 0 < n) :
    ∃ M : Sparkle.IR.AST.Module,
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
        b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)) ∧
      PrintBaseAt n M ∧ Tools.ShippingTypedPostSoundness.TypedPostReady M := by
  obtain ⟨M, D, w1, hcore, hpost, -⟩ := synthesizeCombinational_parts hr
  obtain ⟨envR, logProf, ids, cache, returned, st, nd, len, hrun, hm, hD, nameLegal⟩ :=
    first_core_run hcore entry hwf
  have he := wf_ofF 0 names.length n hn fe hwf
  have facts :=
    transition_facts (dom := .bvar names.length) (bpos := fun _ => 0) (vpos := fun j => j + 1)
      nd len hrun hm nameLegal he
      (fun j hj => absurd hj (Nat.not_lt_zero j)) (fun j hj => ⟨names[j], firstBs_bits hj⟩)
      (first_body (dn := dn) hwf)
  have zero : SourceInputs declName (firstBs dn names n) ids cache (fun _ => false)
      (fun _ k => 0#k) (fun _ => 0) := Tools.ShippingMachineEntry.admissible_zero _ _
  obtain ⟨_, _, _, ready, _, _, _, _, base⟩ := facts.1 _ _ _ (fun _ _ => 0) zero
  exact ⟨M, hpost, base (firstBs_positive hn), ready⟩

set_option maxHeartbeats 1000000 in
/-- **The common port facts of a first-gate child's full-entry module**
(`gate_child_ports` for the first gate; a copy of its proof). -/
theorem first_child_ports {declName : Name} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Design} {dn : Name} {names : List Name} {n : Nat}
    {fe : FExpr}
    (hr : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, design) w')
    (entry : EntryDefines mctx mref cctx cref declName (quoteDecl dn names n fe))
    (hwf : fe.WF names.length n) (hn : 0 < n) :
    GateChildPorts declName (firstBs dn names n) n b := by
  obtain ⟨M, hpost, pb, ready⟩ := first_child_base hr entry hwf hn
  have hfull := first_child_fullFacts hr entry hwf hn
  obtain ⟨hin, hout, hwires, hord, hty, hoty⟩ := post_facts pb ready hpost
  obtain ⟨ty, hty0⟩ := pb.output
  have hmemO : ({ name := "out", ty := ty } : Port) ∈ M.outputs := by
    rw [hty0]
    exact List.mem_singleton.mpr rfl
  have hsub : ∀ p ∈ b.wires, p ∈ M.wires := by
    intro p hp
    rw [hwires] at hp
    exact Tools.ShippingInstWidthsParts.dropZW_wires_sub M p hp
  have hinM : ∀ p ∈ b.inputs, p ∈ M.inputs := by
    intro p hp
    rw [hin] at hp
    exact hp
  exact
    { name := hfull.name
      inTys := hfull.tys
      inPrintable := fun p hp => pb.inputs p (hinM p hp)
      inWire := fun p hp => by
        rw [hwires]
        exact Tools.ShippingOutsExtractedParts.dropZW_wires (pb.inputWires p (hinM p hp))
          (Tools.ShippingGatePorts.printable_ne_zero (pb.inputs p (hinM p hp)))
      inNodup := hfull.comb.inputNames
      wireAlloc := fun p hp => pb.wireNames p (hsub p hp)
      wireUnique := fun p hp r hr' hn' =>
        Tools.ShippingTransitionPortTys.port_of_name ready.wiresNodup (hsub r hr') (hsub p hp) hn'
      out := ⟨ty, hout.trans hty0, pb.outputs _ hmemO, pb.outputWidth _ hmemO⟩
      order := hord
      typed := hty
      outTyped := hoty
      outDriven := hfull.comb.outDriven }

/-- **The common port facts of a REAL first-gate child.** -/
theorem first_real_ports {c : Name} {y : Tools.ShippingChildInv.Res} {dn : Name}
    {names : List Name} {n : Nat} {fe : FExpr}
    (entry : EntryDefines mctx mref cctx cref c (quoteDecl dn names n fe))
    (hwf : fe.WF names.length n) (hn : 0 < n)
    (h : Tools.ShippingChildInv.RealChild mref cref c y) :
    GateChildPorts c (firstBs dn names n) n y.1 := by
  obtain ⟨b, design⟩ := y
  obtain ⟨mctx', cctx', w, w', -, hr⟩ := h.inv
  have entry' : EntryDefines mctx' mref cctx' cref c (quoteDecl dn names n fe) :=
    Tools.ShippingReflectCtx.EntryDefines.ctx entry
  exact first_child_ports hr entry' hwf hn

end Tools.ShippingFirstGateChild

#print axioms Tools.ShippingFirstGateChild.first_child_base
#print axioms Tools.ShippingFirstGateChild.first_child_ports
#print axioms Tools.ShippingFirstGateChild.first_real_ports
