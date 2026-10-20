import Tools.ShippingGateChild
import Tools.ShippingTransitionClosed
import Tools.ShippingMergeClosed
import Tools.ShippingTransitionFields
import Tools.ShippingMachineDepthRunR

/-! # A gate-compiled child at the FULL entry: what `kidsCombB` asks of it

The child an instance refers to is the result of the full entry
(`synthesizeCombinational`): the core module after the zero-width cleanup
and, unless disabled, the checked merge — nothing else
(`synthesizeCombinational_checked`, from the entry's definition; no
optimizer). For a declaration the unified gate accepts, from a run of that
entry and the declaration's reflection (`EntryDefines`): the module is
assignments only, its body reads only its input ports and names driven
earlier, its one output `out` is driven, and its input ports are distinct
allocated names (so none is `out`, `clk` or `rst`). These are the
child-side conditions of `kidsCombB`; the fifth (every input connected by a
wire) is about the instance statement. -/
namespace Tools.ShippingGateChildComb
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto Tools.ShippingMachineCompose
open Tools.ShippingMachineChild
open Tools.ShippingMixedEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineClose (Zip₂)
open Tools.ShippingEntrySoundness (RunsTo EnvDefines entry_kept synthesizeCombinationalCore_reads
  MReturns)
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedExecutionSoundness
open Tools.ShippingUnifiedMeaning (pack)
open Tools.ShippingInlineSoundness (EntryDefines)

open Tools.ShippingTransitionClosed Tools.ShippingMergeClosed
open Tools.ShippingSettledSoundness (Acyclic)
open Sparkle.IR.NameHints (Allocated)
open Sparkle.IR.Reorder

/-- The child-side facts. -/
structure ChildComb (b : Sparkle.IR.AST.Module) : Prop where
  assigns : b.body.all Sparkle.IR.RegDedup.isAssign = true
  closed : readsClosedB (b.inputs.map (·.name)) b.body = true
  output : ∃ ty, b.outputs = [{ name := "out", ty := ty }]
  outDriven : "out" ∈ writesOf b.body
  inputNames : (b.inputs.map (·.name)).Nodup
  inputAlloc : ∀ p ∈ b.inputs, Allocated p.name

theorem acyclic_isAssign : ∀ {body : List Stmt}, Acyclic body →
    body.all Sparkle.IR.RegDedup.isAssign = true := by
  intro body hb
  induction hb with
  | nil => rfl
  | cons _ _ _ ih => simpa [Sparkle.IR.RegDedup.isAssign] using ih

set_option maxHeartbeats 1000000 in
/-- **A gate child's full-entry module is combinational, closed and
one-output** — from a run of the full entry and the reflection of the
declaration. -/
theorem gate_child_comb {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Design}
    {value dom : Lean.Expr} {bs : List (Name × MixedGateBinder)}
    {kb kv : Nat} {vw : Nat → Nat} {bpos vpos : Nat → Nat} {srt : SType} {e : Term srt}
    (hr : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, design) w')
    (entry : EntryDefines mctx mref cctx cref declName value)
    (old : ∀ d : DefinitionVal, d.value = value → certifiedShape? false [] (.defnInfo d) = none)
    (peel : mixedGatePeel value = some (bs,
      quote dom (fun j => inputExpr bs.length (bpos j)) (fun j => inputExpr bs.length (vpos j)) e))
    (he : e.WF kb kv vw)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hv : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits (vw j))) :
    ChildComb b := by
  obtain ⟨M, D, w1, hcore, hpost⟩ := Tools.ShippingMachineShipping.synthesizeCombinational_checked hr
  obtain ⟨logProf, envR, ci, w1', w2, w3, w4, w5, w6, get, henv, run⟩ :=
    synthesizeCombinationalCore_reads hcore
  obtain ⟨d, hd, definition⟩ := entry w1' ci w2 w5 envR w6 get henv
  rw [hd] at run
  have oldGate : certifiedShape? false [] (.defnInfo d) = none := old d definition
  have shape := term_gate (d := d) (by rw [definition]; exact peel) he hb hv
  have core := Tools.ShippingGateChild.synthesizeFromConst_mixed_run oldGate (shape _) run.mreturns
  obtain ⟨ids, cache, returned, st, nd, len, hrun, hm, _, nameLegal⟩ :=
    synthesizeMixedCertified_returns core
  have positive := Tools.ShippingMixedPrintSoundness.mixedShape_positive (shape (fun _ => false))
  obtain ⟨hclosed, hassign, ⟨ow, pb⟩, ready, -, -⟩ :=
    transition_closed nd len hrun hm nameLegal positive e he hb hv rfl
  obtain ⟨_, ⟨B, wOut, hB⟩, _⟩ := transition_facts nd len hrun hm nameLegal he hb hv rfl
  -- the core module
  have hM : ChildComb M :=
    { assigns := acyclic_isAssign pb.order
      closed := hclosed
      output := pb.output
      outDriven := by
        rw [hB]
        exact List.mem_flatMap.mpr ⟨_, List.mem_append_right _ (List.mem_singleton.mpr rfl),
          by simp [stmtWrites]⟩
      inputNames := pb.inputNames
      inputAlloc := fun p hp => pb.wireNames p (pb.inputWires p hp) }
  -- the zero-width cleanup changes nothing of a typed module
  obtain ⟨dzb, _, dzi, dzo, _⟩ := Tools.ShippingTypedPostSoundness.dropZeroWidth_typed ready
  have hZ : ChildComb (Sparkle.IR.ZeroWidth.dropZeroWidthModule M) :=
    { assigns := by rw [dzb]; exact hM.assigns
      closed := by rw [dzb, dzi]; exact hM.closed
      output := by rw [dzo]; exact hM.output
      outDriven := by rw [dzb]; exact hM.outDriven
      inputNames := by rw [dzi]; exact hM.inputNames
      inputAlloc := by rw [dzi]; exact hM.inputAlloc }
  rcases hpost with rfl | rfl
  · exact hZ
  · -- the checked merge of an assignment-only body
    obtain ⟨mi, mo, _⟩ := Sparkle.IR.RefineCheck.mergeChecked_ports
      (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)
    obtain ⟨mc, mw⟩ := mergeChecked_closed (S := (Sparkle.IR.ZeroWidth.dropZeroWidthModule M).inputs.map (·.name))
      hZ.assigns hZ.closed
    have hmd : Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M) =
        Sparkle.IR.RegDedup.mergeDuplicates (Sparkle.IR.ZeroWidth.dropZeroWidthModule M) := by
      unfold Sparkle.IR.RefineCheck.mergeChecked
      simp only [hZ.assigns, if_true]
    exact
      { assigns := by
          rw [hmd]
          exact acyclic_isAssign (Tools.ShippingPostSoundness.mergeDuplicates_order
            (by rw [dzb]; exact pb.order))
        closed := by rw [mi]; exact mc
        output := by rw [mo]; exact hZ.output
        outDriven := by rw [mw]; exact hZ.outDriven
        inputNames := by rw [mi]; exact hZ.inputNames
        inputAlloc := by rw [mi]; exact hZ.inputAlloc }

/-! ## The same run's ports, name and design -/

theorem dropZeroWidth_name (m : Sparkle.IR.AST.Module) :
    (Sparkle.IR.ZeroWidth.dropZeroWidthModule m).name = m.name := by
  unfold Sparkle.IR.ZeroWidth.dropZeroWidthModule
  split <;> rfl

/-- The full entry, with its design: the core run, the returned module (the
cleanup's, or its checked merge), and a design with no module when the core's
has none. -/
theorem synthesizeCombinational_parts {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {M' : Sparkle.IR.AST.Module} {D' : Design}
    (h : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (M', D') w') :
    ∃ (M : Sparkle.IR.AST.Module) (D : Design) (w1 : Void IO.RealWorld),
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (M, D) w1 ∧
      (M' = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
        M' = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)) ∧
      (D.modules = [] → D'.modules = []) := by
  unfold synthesizeCombinational synthesizeCombinationalWith at h
  obtain ⟨⟨M, D⟩, w1, hcore, h⟩ := RunsTo.bind h
  refine ⟨M, D, w1, hcore, ?_⟩
  dsimp only at h
  obtain ⟨_, _, -, h⟩ := RunsTo.bind h
  rcases RunsTo.ite h with h | h
  · have := Tools.ShippingPostSoundness.RunsTo.pure h
    simp only [Prod.mk.injEq] at this
    exact ⟨Or.inl this.1, fun hD => by rw [this.2]; simp [hD]⟩
  · have := Tools.ShippingPostSoundness.RunsTo.pure h
    simp only [Prod.mk.injEq] at this
    exact ⟨Or.inr this.1, fun hD => by rw [this.2]; simp [hD]⟩

/-- What a parent needs of a gate child's full-entry result — from ONE run:
the child-side `kidsCombB` facts, the port types (one per hardware binder of
the declaration, in order), the module's name, and a design with no module. -/
structure ChildFull (declName : Name) (bs : List (Name × MixedGateBinder))
    (b : Sparkle.IR.AST.Module) (design : Design) : Prop where
  comb : ChildComb b
  tys : b.inputs.map (·.ty) = (bs.filter fun x => x.2 != .domain).map fun x => kindTy x.2
  name : b.name = (Sparkle.IR.ModuleName.ofDecl declName)
  design : design.modules = []

set_option maxHeartbeats 1000000 in
/-- **A gate child's full-entry result, from one run and the declaration's
reflection.** -/
theorem gate_child_fullFacts {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Design}
    {value dom : Lean.Expr} {bs : List (Name × MixedGateBinder)}
    {kb kv : Nat} {vw : Nat → Nat} {bpos vpos : Nat → Nat} {srt : SType} {e : Term srt}
    (hr : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, design) w')
    (entry : EntryDefines mctx mref cctx cref declName value)
    (old : ∀ d : DefinitionVal, d.value = value → certifiedShape? false [] (.defnInfo d) = none)
    (peel : mixedGatePeel value = some (bs,
      quote dom (fun j => inputExpr bs.length (bpos j)) (fun j => inputExpr bs.length (vpos j)) e))
    (he : e.WF kb kv vw)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hv : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits (vw j))) :
    ChildFull declName bs b design := by
  have hcomb := gate_child_comb hr entry old peel he hb hv
  obtain ⟨M, D, w1, hcore, hpost, hdes⟩ := synthesizeCombinational_parts hr
  obtain ⟨logProf, envR, ci, w1', w2, w3, w4, w5, w6, get, henv, run⟩ :=
    synthesizeCombinationalCore_reads hcore
  obtain ⟨d, hd, definition⟩ := entry w1' ci w2 w5 envR w6 get henv
  rw [hd] at run
  have oldGate : certifiedShape? false [] (.defnInfo d) = none := old d definition
  have shape := term_gate (d := d) (by rw [definition]; exact peel) he hb hv
  have core := Tools.ShippingGateChild.synthesizeFromConst_mixed_run oldGate (shape _) run.mreturns
  obtain ⟨ids, cache, returned, st, nd, len, hrun, hm, hD, nameLegal⟩ :=
    synthesizeMixedCertified_returns core
  have positive := Tools.ShippingMixedPrintSoundness.mixedShape_positive (shape (fun _ => false))
  obtain ⟨-, -, -, ready, hdesign, hname⟩ :=
    transition_closed nd len hrun hm nameLegal positive e he hb hv rfl
  obtain ⟨_, _, hin⟩ := transition_facts nd len hrun hm nameLegal he hb hv rfl
  have hMtys : M.inputs.map (·.ty) = (bs.filter fun x => x.2 != .domain).map fun x => kindTy x.2 := by
    rw [hin (fun _ => false) (fun _ n => 0#n)]
    exact Tools.ShippingTransitionFields.inputPorts_tys bs ids _ len
  have hDm : D.modules = [] := by
    rw [hD, hdesign]
    rfl
  obtain ⟨_, _, dzi, _, _⟩ := Tools.ShippingTypedPostSoundness.dropZeroWidth_typed ready
  refine ⟨hcomb, ?_, ?_, hdes hDm⟩
  · rcases hpost with rfl | rfl
    · rw [dzi]; exact hMtys
    · rw [(Sparkle.IR.RefineCheck.mergeChecked_ports _).1, dzi]; exact hMtys
  · rcases hpost with rfl | rfl
    · rw [dropZeroWidth_name]; exact hname
    · rw [Tools.ShippingMachineDepthRun.mergeChecked_name, dropZeroWidth_name]; exact hname

end Tools.ShippingGateChildComb
