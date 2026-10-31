import Tools.ShippingGen2Defs
set_option autoImplicit false
-- BUILT (unit FB-14): kjob lake build Tools.ShippingGen4FbPP exit 0 (701 jobs, Pod build); clean issue-linked build fb14v-67756b3c exit 0 (approved at 67756b3c, scope-limited). Written against scripts/gen4/FALLBACK_SUPPLY_FREEZE.md §23.3 (rev13, committed 3d58fd03 before this file).
-- No `sorry`, no `axiom`, no `native_decide`, no new law / field. One definition set and five theorems.

/-! # FB-14: T-PP-PORTS — the port/shape part of the post-processing

`PPRel` is the post-processing of `synthesizeCombinationalWith` (Elab.lean 5598-5606). `ppRel_ports`: it keeps the
module name, inputs and outputs. The six non-run conjuncts of `SeqChildRunN` / `CombChildRunN` read only those fields,
so they transfer from `raw` to `out`. The RUN conjunct (`RunOn … T ins s vals`) is NOT covered: this is a partial
supply of T-PP, not `PPTransportStmt`. -/

namespace Tools.ShippingGen4FbPP
open Lean Meta Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.IR.AST (Module)
open Tools.ShippingGen2

def PPRel (raw : Sparkle.IR.AST.Module) (dsg : Sparkle.IR.AST.Design)
    (out : Sparkle.IR.AST.Module) (dout : Sparkle.IR.AST.Design) : Prop :=
  let top : (Sparkle.IR.AST.Module → Sparkle.IR.AST.Module) → Sparkle.IR.AST.Design →
      Sparkle.IR.AST.Design := fun f d =>
    { d with modules := d.modules.map fun x => if x.name == raw.name then f x else x }
  let m' := Sparkle.IR.ZeroWidth.dropZeroWidthModule raw
  let d₁ := top Sparkle.IR.ZeroWidth.dropZeroWidthModule dsg
  (out = m' ∧ dout = d₁) ∨
  (out = Sparkle.IR.RefineCheck.mergeChecked m' ∧ dout = top Sparkle.IR.RefineCheck.mergeChecked d₁)

def SeqPortFacts (mc : Sparkle.IR.AST.Module)
    (bsC : List (Lean.Name × Sparkle.Compiler.Elab.MixedGateBinder)) (outsC : List OutField) : Prop :=
  mc.outputs = outsC.map (fun o => ({ name := o.name, ty := o.ty } : Port)) ∧
  (mc.inputs.map (·.name)).Nodup ∧ "clk" ∈ mc.inputs.map (·.name) ∧
  "rst" ∈ mc.inputs.map (·.name) ∧
  (∀ x ∈ mc.outputs.map (·.name), x ∉ mc.inputs.map (·.name)) ∧
  (Tools.ShippingMachineCompose.argPorts mc).length =
    (bsC.filter fun b => b.2 != .domain).length

def CombPortFacts (mc : Sparkle.IR.AST.Module)
    (bsC : List (Lean.Name × Sparkle.Compiler.Elab.MixedGateBinder)) (outsC : List OutField) : Prop :=
  mc.outputs = outsC.map (fun o => ({ name := o.name, ty := o.ty } : Port)) ∧
  (mc.inputs.map (·.name)).Nodup ∧
  "clk" ∉ mc.inputs.map (·.name) ∧ "rst" ∉ mc.inputs.map (·.name) ∧
  (∀ x ∈ mc.outputs.map (·.name), x ∉ mc.inputs.map (·.name)) ∧
  (Tools.ShippingMachineCompose.argPorts mc).length =
    (bsC.filter fun b => b.2 != .domain).length

theorem dropZW_outputs (m : Sparkle.IR.AST.Module) :
    (Sparkle.IR.ZeroWidth.dropZeroWidthModule m).outputs = m.outputs := by
  unfold Sparkle.IR.ZeroWidth.dropZeroWidthModule
  split <;> rfl

theorem ppRel_ports {raw : Sparkle.IR.AST.Module} {dsg : Sparkle.IR.AST.Design}
    {out : Sparkle.IR.AST.Module} {dout : Sparkle.IR.AST.Design}
    (h : PPRel raw dsg out dout) :
    out.name = raw.name ∧ out.inputs = raw.inputs ∧ out.outputs = raw.outputs := by
  have hd : (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw).name = raw.name ∧
      (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw).inputs = raw.inputs ∧
      (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw).outputs = raw.outputs :=
    ⟨Tools.ShippingMachineDepthRun.dropZW_name raw, Tools.ShippingOutsExtractedParts.dropZW_inputs raw,
      dropZW_outputs raw⟩
  rcases h with ⟨ho, -⟩ | ⟨ho, -⟩
  · rw [ho]; exact hd
  · rw [ho]
    obtain ⟨h1, h2, h3⟩ := Sparkle.IR.RefineCheck.mergeChecked_ports
      (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)
    exact ⟨(Tools.ShippingMachineDepthRun.mergeChecked_name _).trans hd.1, h1.trans hd.2.1, h2.trans hd.2.2⟩

theorem ppRel_design_names {raw : Sparkle.IR.AST.Module} {dsg : Sparkle.IR.AST.Design}
    {out : Sparkle.IR.AST.Module} {dout : Sparkle.IR.AST.Design}
    (h : PPRel raw dsg out dout) :
    dout.topModule = dsg.topModule ∧ dout.modules.map (·.name) = dsg.modules.map (·.name) := by
  have key : ∀ (f : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module), (∀ x, (f x).name = x.name) →
      ∀ (l : List Sparkle.IR.AST.Module),
      (l.map fun x => if x.name == raw.name then f x else x).map (·.name) = l.map (·.name) := by
    intro f hf l
    rw [List.map_map]
    apply List.map_congr_left
    intro x _
    simp only [Function.comp]
    split
    · exact hf x
    · rfl
  have hz : ∀ x, (Sparkle.IR.ZeroWidth.dropZeroWidthModule x).name = x.name :=
    Tools.ShippingMachineDepthRun.dropZW_name
  have hm : ∀ x, (Sparkle.IR.RefineCheck.mergeChecked x).name = x.name :=
    Tools.ShippingMachineDepthRun.mergeChecked_name
  rcases h with ⟨-, hd⟩ | ⟨-, hd⟩
  · subst hd
    exact ⟨rfl, key _ hz _⟩
  · subst hd
    refine ⟨rfl, ?_⟩
    dsimp only
    rw [key _ hm, key _ hz]

theorem ppRel_seqPortFacts {raw : Sparkle.IR.AST.Module} {dsg : Sparkle.IR.AST.Design}
    {out : Sparkle.IR.AST.Module} {dout : Sparkle.IR.AST.Design}
    {bsC : List (Lean.Name × Sparkle.Compiler.Elab.MixedGateBinder)} {outsC : List OutField}
    (h : PPRel raw dsg out dout) (hs : SeqPortFacts raw bsC outsC) : SeqPortFacts out bsC outsC := by
  obtain ⟨-, hi, ho⟩ := ppRel_ports h
  unfold SeqPortFacts Tools.ShippingMachineCompose.argPorts at hs ⊢
  rw [hi, ho]
  exact hs

theorem ppRel_combPortFacts {raw : Sparkle.IR.AST.Module} {dsg : Sparkle.IR.AST.Design}
    {out : Sparkle.IR.AST.Module} {dout : Sparkle.IR.AST.Design}
    {bsC : List (Lean.Name × Sparkle.Compiler.Elab.MixedGateBinder)} {outsC : List OutField}
    (h : PPRel raw dsg out dout) (hs : CombPortFacts raw bsC outsC) : CombPortFacts out bsC outsC := by
  obtain ⟨-, hi, ho⟩ := ppRel_ports h
  unfold CombPortFacts Tools.ShippingMachineCompose.argPorts at hs ⊢
  rw [hi, ho]
  exact hs

theorem ppRel_childRunN_portFacts {raw : Sparkle.IR.AST.Module} {dsg : Sparkle.IR.AST.Design}
    {out : Sparkle.IR.AST.Module} {dout : Sparkle.IR.AST.Design}
    {children : String → Option (Sparkle.IR.AST.Module × WEnv)} {dsn : Design} {n : Nat}
    {bsC : List (Lean.Name × Sparkle.Compiler.Elab.MixedGateBinder)} {outsC : List OutField}
    {S : (Nat → List Nat) → List (Nat → Nat)}
    (h : PPRel raw dsg out dout) (hr : ChildRunN children dsn n raw bsC outsC S) :
    SeqPortFacts out bsC outsC ∨ CombPortFacts out bsC outsC := by
  rcases hr with ⟨a1, a2, a3, a4, a5, a6, -⟩ | ⟨a1, a2, a3, a4, a5, a6, -⟩
  · exact Or.inl (ppRel_seqPortFacts h ⟨a1, a2, a3, a4, a5, a6⟩)
  · exact Or.inr (ppRel_combPortFacts h ⟨a1, a2, a3, a4, a5, a6⟩)

end Tools.ShippingGen4FbPP
