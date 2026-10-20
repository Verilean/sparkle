import Tools.ShippingChecksWidths
import Tools.ShippingKidsPassLeaf
import Tools.ShippingTextShipped
-- ORIGIN DISPATCH (par/o-close, compiler change "explicit call-entry origin"):
-- BUILT against the origin-tag compiler (integration run ig4, 3 GiB, swap 0, -j 1, exit 0; fixes: see docs/parallel/O-origin-integration.md).

/-! # The statement-kind gate and the children's check WITHOUT `instFields ≠ []` (G1, round par/a-5)

`Tools.ShippingChecksWidths.core_hierGate` takes `hfne : d.shape.instFields ≠ []`
and uses it in ONE place: to pick the `closeInstsG` disjunct of the run's
closing (`CloseCalls`) and read the first call's instance statement off
`closeInstsG_calls`. Everything else in its proof comes from
`CloseCalls.some`, which holds of BOTH closings. The one-output closing
(`closeInsts`, `instFields = []`: every call a one-output combinational
child — the parents `caller…`, `callerL`, `callerLN`, `hftByte`) has the
same fact as `Tools.ShippingMachineInst.closeInsts_calls`. So the hypothesis
is INHERITED, not essential:

* `core_hierGate_any`: `hierGate b = true` for the full entry's module of a
  machine with calls, whichever closing the run took. Statement =
  `core_hierGate`'s without `hfne`; proof = `core_hierGate`'s (copied) with
  the case split on the closing kept and the first disjunct proved.
* `core_kidsPass_any`: `Tools.ShippingKidsPassLeaf.core_kidsPass_leaf`
  without `hfne` (its only use of `hfne` was the gate).
* `core_text_shipped_any`: `Tools.ShippingTextShipped.core_text_shipped`
  without `hfne` (conjuncts 2 and 3 of `textCheckI` of the SHIPPED module;
  its only use of `hfne` was the gate; `core_text_raw` never asked it).

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingHierGateAny
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData Tools.ShippingMachineCloses
open Tools.ShippingMixedEntrySoundness
open Tools.ShippingGateChildComb Tools.ShippingChildInv
open Tools.ShippingInstStmtG Tools.ShippingCallsAssemblyG Tools.ShippingTransitionClosed
open Tools.ShippingSeqChildIface Tools.ShippingCallsKidsD Tools.ShippingDesignWithG
open Tools.ShippingClosedKinds Tools.ShippingKidsChildIface
open Sparkle.IR.RefineCheck (mergeChecked hierBinds)
open Sparkle.IR.OptCheck (seqStmtOk checkedOptimize)
open Tools.ShippingMachineLinked (childMap)

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 4000000 in
/-- **The statement-kind gate of the hierarchical check, for either
closing**: the full entry's module of a machine with calls has an instance
statement, and every statement is an instance, an assignment or a
register. -/
theorem core_hierGate_any {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true ∧ (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape) :
    Sparkle.IR.RefineCheck.hierGate b = true := by
  have hbody' : b.body = M.body :=
    (Tools.ShippingChecksCore.core_kids_facts d ok hbody hC hslots hdomB hins outTy hnomem hB
      hcore hpost entry closes).2.1
  obtain ⟨_, bb, r, w9, w10, hrun9, hw9, hd9, hres⟩ :=
    machine_run_of_core hcore entry hB
  have hne := closes bb _ _ _ hw9 hd9 hrun9
  cases r with
  | none => exact absurd rfl hne
  | some res =>
  have hres' := hres res rfl
  subst hres'
  obtain ⟨t, t', d₀, run, hcl, hmt⟩ := synthesizeMachineCertified_runs hw9 hrun9
  rcases hmt with ⟨hno, -, -⟩ | ⟨-, children, hcc, hreal⟩
  · exact absurd hno hins
  obtain ⟨-, -, -, L, hLinst, hperm, -, -, -, -, -, -, -⟩ := hcc.some
  obtain ⟨hseq0, -, -⟩ := closedBody_kinds_of_run d ok hbody hC hslots hdomB run hcl
  have hk0 : 0 < (d.shape.insts.map (·.2.1)).length := by
    rw [List.length_map]
    exact List.length_pos_iff.mpr hins
  refine Tools.ShippingInstWidthsParts.hierGate_of ?_ ?_
  · -- the instance statement of the first call, in either closing
    rw [hbody']
    rcases hcc with ⟨-, hI⟩ | ⟨-, hG, -⟩
    · -- the one-output closing
      obtain ⟨args, child, mc, -, -, -, st, hst, hcs⟩ :=
        Tools.ShippingMachineInst.closeInsts_calls hI 0 hk0
      obtain ⟨outW, argWs, outP, iname, -, -, -, -, -, -, -, -, -, he⟩ := hcs
      rw [he] at hst
      exact ⟨mc.name, iname, _, hst⟩
    · -- the group closing (the proof of `core_hierGate`)
      obtain ⟨st, hst, args, outs, child, mc, hcs, -⟩ :=
        Tools.ShippingMachineInstG.closeInstsG_calls hG 0 hk0
      obtain ⟨_, _, iname, -, -, -, -, -, -, -, -, -, -, -, he⟩ := hcs
      exact ⟨mc.name, iname, _, he ▸ hst⟩
  · intro st hst
    rw [hbody'] at hst
    rcases List.mem_append.mp (hperm.symm.subset hst) with h0 | h0
    · exact Or.inr (List.all_eq_true.mp hseq0 _ h0)
    · exact Or.inl (List.all_eq_true.mp hLinst _ h0)

set_option maxHeartbeats 4000000 in
/-- **The children's check of the shipped module of a machine with calls**,
on the core run's design, at every depth, from one fact per real child —
`core_kidsPass_leaf` without `hfne`. -/
theorem core_kidsPass_any {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true ∧ (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true)
    (hkidK : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      (∀ (C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)) (n : Nat),
          Tools.ShippingChecksDesign.kidCheck C n y.1 = true) ∧
        ∀ g ∈ y.2.modules,
          ∀ (C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)) (n : Nat),
            Tools.ShippingChecksDesign.kidCheck C n g = true)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape) (n : Nat) :
    Tools.ShippingDesignSV.kidsPass (childMap D.modules)
      (Tools.ShippingChecksDesign.kidCheck (childMap D.modules) n)
      (checkedOptimize b).body = true := by
  obtain ⟨-, hbody', -, hresM, hrealD, -⟩ :=
    Tools.ShippingChecksCore.core_kids_facts d ok hbody hC hslots hdomB hins outTy hnomem hB
      hcore hpost entry closes
  have hgate : Sparkle.IR.RefineCheck.hierGate b = true :=
    core_hierGate_any d ok hbody hC hslots hdomB hins outTy hnomem hB hcore hpost entry closes
  unfold Tools.ShippingDesignSV.kidsPass
  rw [List.all_eq_true]
  intro st hst
  cases st with
  | inst mn iname conns =>
    have hm : Stmt.inst mn iname conns ∈ b.body :=
      (Tools.ShippingChecksDepthGate.checkedOptimize_inst_iff_gate hgate mn iname conns).mp hst
    rw [hbody'] at hm
    obtain ⟨mc, hmc⟩ := hresM mn iname conns hm
    have hmem : mc ∈ D.modules := (Tools.ShippingHierPremisesBase.moduleByName_mem hmc).1
    obtain ⟨k, hk, y, hre, hor, -⟩ := hrealD mc hmem
    have hCm : childMap D.modules mn = some (mc, Sparkle.IR.RegDedup.declWidth mc) :=
      congrArg (fun o : Option Sparkle.IR.AST.Module =>
        o.map fun g => (g, Sparkle.IR.RegDedup.declWidth g)) hmc
    simp only [hCm]
    rcases hor with heq | hin
    · rw [heq]
      exact (hkidK k hk y hre).1 _ n
    · exact (hkidK k hk y hre).2 mc hin _ n
  | _ => rfl

set_option maxHeartbeats 4000000 in
/-- **Conjuncts 2 and 3 of `textCheckI` of the SHIPPED module, from the core
run, for either closing** — `core_text_shipped` without `hfne`. -/
theorem core_text_shipped_any {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true ∧ (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape)
    (hon : ∀ o ∈ d.shape.layout.outs, Sparkle.Backend.Verilog.sanitizeName o.name = o.name)
    (hoty : ∀ o ∈ d.shape.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true) :
    Tools.SVParser.EmitSem.seqCheck (Tools.ShippingDesignSV.wofOf (checkedOptimize b))
        (Tools.ShippingDesignSV.weS (checkedOptimize b)) (checkedOptimize b).body = true ∧
      (Tools.ShippingSeqSVSoundness.seqNames (checkedOptimize b).body).all
        (fun x => Sparkle.IR.RegDedup.declWidth (checkedOptimize b) x ==
          Tools.ShippingDesignSV.weS (checkedOptimize b) x) = true :=
  Tools.ShippingTextShipped.text_shipped_of
    (core_hierGate_any d ok hbody hC hslots hdomB hins outTy hnomem hB hcore hpost entry closes)
    (Tools.ShippingClosedTyped.core_text_raw d ok hbody hC hslots hdomB hins outTy hnomem hB
      hcore hpost entry closes hon hoty)

end Tools.ShippingHierGateAny
