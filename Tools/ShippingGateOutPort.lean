import Tools.ShippingGateDesignRun
import Tools.ShippingGateOptComb

/-! # Gate-route parents: `out` is an output port of the returned module (worker N, round 12)

WRITTEN, NOT BUILT.

`Tools.ShippingGateOptComb.optKeepsOut_comb_post` (obstacle (C) without
`rst`) asks `"out" ∈ b.outputs.map (·.name)` of the module `b` the full entry
returns. The walk's `ModOk` does not record the output ports, so it is
derived here from the SAME run, at the harness level, without the walk:

* the mixed harness (`mixedHarness_runs`) returns
  `m = (addClockResetIfSequential st.module).finalize` with
  `st = emitAssign "out" … (addOutput "out" ty sm0)`: `out` is an output of
  the core module (`harness_out`; `addClockReset_facts` keeps the outputs,
  `finalize` reverses them);
* the post passes keep the outputs (`post_outputs`: the zero-width cleanup
  rewrites the body and the wires only; `mergeChecked_ports`);
* `gate_out_port`: the full entry's run, `GateDefines` and `ChildBnd` (the
  premises of every `…_gate_designSV'`) give `"out" ∈ b.outputs.map (·.name)`.
  The reads of the core run are those of `gate_cone_runGED` (a copy of its
  first half). -/
namespace Tools.ShippingGateOutPort

set_option linter.unusedSectionVars false

open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Builder
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingChildInv (RefLaws InvV ChildBnd bodyRel profLogIO)
open Tools.ShippingGateDefines (GateDefines)

/-- The zero-width cleanup keeps the output ports. -/
theorem dz_outputs (m : Sparkle.IR.AST.Module) :
    (Sparkle.IR.ZeroWidth.dropZeroWidthModule m).outputs = m.outputs := by
  unfold Sparkle.IR.ZeroWidth.dropZeroWidthModule
  split
  · rfl
  · rfl

/-- **The full entry's post passes keep the output ports.** -/
theorem post_outputs {b M : Sparkle.IR.AST.Module}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)) :
    b.outputs = M.outputs := by
  rcases hpost with e | e
  · rw [e]
    exact dz_outputs M
  · rw [e, (Sparkle.IR.RefineCheck.mergeChecked_ports _).2.1]
    exact dz_outputs M

/-- **The harness's tail makes `out` an output port.** -/
theorem harness_out {m : Sparkle.IR.AST.Module} {sm0 st : CircuitState} {wire : String}
    {ty : Sparkle.IR.Type.HWType}
    (hst : st = (CircuitM.emitAssign "out" (.ref wire) (CircuitM.addOutput "out" ty sm0).2).2)
    (hm : m = (addClockResetIfSequential st.module).finalize) :
    "out" ∈ m.outputs.map (·.name) := by
  have hout : m.outputs = st.module.outputs.reverse := by
    rw [hm]
    simp only [Sparkle.IR.AST.Module.finalize,
      (Tools.ShippingEntrySoundness.addClockReset_facts st.module).2.2.1]
  have hmod : st.module.outputs = ({ name := "out", ty := ty } : Port) :: sm0.module.outputs := by
    subst hst
    rfl
  rw [hout, hmod]
  exact List.mem_map.mpr ⟨({ name := "out", ty := ty } : Port),
    List.mem_reverse.mpr List.mem_cons_self, rfl⟩

variable {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}

/-- **`out` is an output port of the module the full entry returns**, for a
gate-route parent: from the run, `GateDefines` (NOT ALLOWED, as in every
`…_gate_designSV'`) and `ChildBnd`. -/
theorem gate_out_port {f : Lean.Name} {bs : List (Lean.Name × MixedGateBinder)}
    {body : Lean.Expr} {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module}
    {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinational f) mctx mref cctx cref w (b, design) w')
    (gdef : GateDefines mctx mref cctx cref f bs body)
    (bnd : ChildBnd mref cref w) :
    "out" ∈ b.outputs.map (·.name) := by
  obtain ⟨L, ⟨hsv, hdep⟩, hq⟩ := bnd
  obtain ⟨M, Dd, w1, hcore, hpost⟩ :=
    Tools.ShippingMachineShipping.synthesizeCombinational_checked hr
  have hreads : ∃ (bb : Bool) (envR : Lean.Environment) (ci : Lean.ConstantInfo)
      (a1 a2 a3 a4 a5 a6 : Void IO.RealWorld),
      RunsTo (Lean.getConstInfo f) mctx mref cctx cref a1 ci a2 ∧
      RunsTo (Lean.getEnv : Lean.Meta.MetaM Lean.Environment) mctx mref cctx cref a5 envR a6 ∧
      RunsTo (synthesizeFromConst (fun e h t n => translateExprToWire envR e h t n)
        (profLogIO bb) f [] false true
        (entryConst true false [] ci (Sparkle.Compiler.Elab.instancePredicate envR)
          (userInliner envR) (structEnv envR))
        (Sparkle.Compiler.Elab.instancePredicate envR))
        mctx mref cctx cref a3 (M, Dd) a4 ∧ InvV L a3 ∧ L.dval a3 ≠ 0 := by
    by_cases h0 : L.dval w = 0
    · obtain ⟨bb, envR, ci, a1, a2, a3, a4, a5, a6, hget, henv, run, hw3, hd3, -, -, -⟩ :=
        Tools.ShippingCacheCoherentOuter.core_reads_val0 L (fun L' => bodyRel L') hsv hq h0 hcore
      exact ⟨bb, envR, ci, a1, a2, a3, a4, a5, a6, hget, henv, run, hw3, hd3⟩
    · rcases hdep with hz | hci
      · exact absurd hz h0
      · obtain ⟨bb, envR, ci, a1, a2, a3, a4, a5, a6, hget, henv, run, hw3, hd3, -, -, -⟩ :=
          Tools.ShippingCacheCoherentVia.core_reads_val L (fun L' => bodyRel L')
            ⟨hci, hsv, hq⟩ h0 hcore
        exact ⟨bb, envR, ci, a1, a2, a3, a4, a5, a6, hget, henv, run, hw3, hd3⟩
  obtain ⟨bb, envR, ci, a1, a2, a3, a4, a5, a6, hget, henv, run, hw3, hd3⟩ := hreads
  obtain ⟨dv, hdv, hold, hshape⟩ := gdef a1 ci a2 a5 envR a6 hget henv
  rw [hdv] at run
  obtain ⟨wa, wb, hwa, hda, hharn⟩ := Tools.ShippingGateParentRun.sfc_mixed_run L hold hshape hw3 run
  obtain ⟨ids, cache, wT, wT', wire, sm0, ty, st, -, -, -, -, -, -, hst, -, hm, -⟩ :=
    Tools.ShippingGateParentRun.mixedHarness_runs L hwa rfl hharn
  rw [post_outputs hpost]
  exact harness_out hst hm

end Tools.ShippingGateOutPort

#print axioms Tools.ShippingGateOutPort.post_outputs
#print axioms Tools.ShippingGateOutPort.harness_out
#print axioms Tools.ShippingGateOutPort.gate_out_port
