import Tools.ShippingCloseLetsSplit

/-! # `MachineCloses`, split at the two closings

The machine synthesis falls back in two places: `closeLets` refuses the
harness' transition, or — for a shape with calls — the closing of the calls
(`closeInstsM` / `closeInstsGM`) returns nothing. `MachineCloses` is exactly
"neither happens":

* `LetsClose`: `closeLets` accepts the transition of every run of the harness;
* `CallsClose`: every run of the calls' closing, after such a run, returns a
  module.

`LetsClose` is derived from the shape for shapes WITH calls too
(`Tools/ShippingMachineCloses.lean`); `CallsClose` is not derived. -/
namespace Tools.ShippingClosesSplit
open Lean Meta Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- `closeLets` accepts the transition of every run of the harness. -/
def LetsClose (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
    (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State) (declName : Name)
    (shape : MachineShape) : Prop :=
  ∀ {tenv : Lean.Environment}, ∀ (logProf : String → IO Unit) w t d w',
    RunsTo (synthesizeMixedCertified (fun e hint top named => translateExprToWire tenv e hint top named)
      logProf declName shape.binders shape.body) mctx mref cctx cref w (t, d) w' →
    (closeLets shape.layout.lets t).isSome = true

/-- The closing of the calls, as the machine synthesis runs it. -/
def closeCalls (shape : MachineShape) (t t' : Sparkle.IR.AST.Module) (d : Sparkle.IR.AST.Design) :
    MetaM (Option (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)) :=
  if shape.instFields.isEmpty then closeInstsM shape t (closeMachine shape.layout t') d
  else closeInstsGM shape t (closeMachine shape.layout t') d

/-- After a run of the harness whose transition `closeLets` accepts, every
run of the calls' closing returns a module. -/
def CallsClose (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
    (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State) (declName : Name)
    (shape : MachineShape) : Prop :=
  ∀ {tenv : Lean.Environment}, ∀ (logProf : String → IO Unit) w t d w1 t',
    RunsTo (synthesizeMixedCertified (fun e hint top named => translateExprToWire tenv e hint top named)
      logProf declName shape.binders shape.body) mctx mref cctx cref w (t, d) w1 →
    closeLets shape.layout.lets t = some t' →
    ∀ r w', RunsTo (closeCalls shape t t' d) mctx mref cctx cref w1 r w' → r ≠ none

/-- **`MachineCloses` is `LetsClose` and, with calls, `CallsClose`.** -/
theorem machineCloses_iff {declName : Name} {shape : MachineShape} :
    MachineCloses mctx mref cctx cref declName shape ↔
      LetsClose mctx mref cctx cref declName shape ∧
        (shape.insts ≠ [] → CallsClose mctx mref cctx cref declName shape) := by
  constructor
  · intro hc
    refine ⟨?_, ?_⟩
    · intro tenv logProf w t d w' hr
      cases hcl : closeLets shape.layout.lets t with
      | some t' => rfl
      | none =>
        have hrun : RunsTo (synthesizeMachineCertified
            (fun e hint top named => translateExprToWire tenv e hint top named) logProf declName shape)
            mctx mref cctx cref w none w' := by
          unfold synthesizeMachineCertified
          refine Tools.ShippingReflectCtx.RunsTo.bind_intro hr ?_
          simp only [hcl]
          rfl
        exact absurd rfl (hc logProf w none w' hrun)
    · intro hne tenv logProf w t d w1 t' hr hcl r w' hcalls
      refine hc (tenv := tenv) logProf w r w' ?_
      unfold synthesizeMachineCertified
      refine Tools.ShippingReflectCtx.RunsTo.bind_intro hr ?_
      simp only [hcl]
      split
      · rename_i heq
        exact absurd heq hne
      · exact hcalls
  · rintro ⟨hl, hcalls⟩ tenv logProf w r w' hr
    unfold synthesizeMachineCertified at hr
    obtain ⟨⟨t, d⟩, w1, h1, hr⟩ := RunsTo.bind hr
    dsimp only at hr
    obtain ⟨t', ht'⟩ := Option.isSome_iff_exists.mp (hl logProf w t d w1 h1)
    rw [ht'] at hr
    dsimp only at hr
    split at hr
    · have := RunsTo.pure_eq hr
      rw [this]
      exact Option.some_ne_none _
    · rename_i heq
      exact hcalls (by rw [heq]; exact List.cons_ne_nil _ _) logProf w t d w1 t' h1 ht' r w' hr

/-- Without calls, `LetsClose` is all of it. -/
theorem machineCloses_of_letsClose {declName : Name} {shape : MachineShape}
    (hi : shape.insts = []) (h : LetsClose mctx mref cctx cref declName shape) :
    MachineCloses mctx mref cctx cref declName shape :=
  machineCloses_iff.mpr ⟨h, fun hne => absurd hi hne⟩

end Tools.ShippingClosesSplit
