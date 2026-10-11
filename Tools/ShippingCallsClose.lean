import Tools.ShippingChildRun
import Tools.ShippingClosesSplit

/-! # The calls' closing, from an invariant world

`MachineCloses` asks every run of the machine synthesis, from EVERY world and
with EVERY logger, to return a module. For a shape with calls that cannot be
derived: the closing reads the child-synthesis reference
(`sparkleChildSynth`), and returns nothing where it is not installed. What a
real compile gives is a world satisfying the child-cache invariant (`InvV`),
and the compiler's own logger (`profLogIO`).

`MachineClosesAt` (`Tools/ShippingChildRun.lean`) is the statement at such worlds. Here it is reduced to a
statement about the PURE functions `closeInsts` / `closeInstsG`:

* `closeInstsM_run` / `closeInstsGM_run`: from an invariant world, a run of
  the closing returns `closeInsts … children …` for children that are real
  compiles (`ChildrenReal`) — whatever the result, a module or nothing;
* `machineClosesAt_of_pure`: `LetsClose` and `CallsPure` (the pure closing
  succeeds on every list of real children) give `MachineClosesAt`.

`CallsPure` is NOT proved here. The endpoints still ask `MachineCloses`. -/
namespace Tools.ShippingChildInv
open Lean Meta
open Tools.ShippingEntrySoundness
open Tools.ShippingMachineEntry
open Sparkle.Compiler.Elab
open Tools.ShippingClosesSplit

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- **A run of the one-output closing, from an invariant world**: the pure
closing of real children — a module or nothing. -/
theorem closeInstsM_run (L : RefLaws mref cref) (hB : BodyRel L)
    {shape t m₀ d₀ r} {w w'} (hw : InvV L w)
    (hr : RunsTo (closeInstsM shape t m₀ d₀) mctx mref cctx cref w r w') :
    ∃ children, r = Sparkle.IR.Machine.closeInsts (machNIn shape) shape.insts.length
        shape.layout.slots.length (t.inputs.map (·.name)) (shape.insts.map (·.2.1))
        children (m₀, d₀) ∧
      ChildrenReal mref cref shape children ∧ InvV L w' := by
  unfold closeInstsM at hr
  obtain ⟨synth?, w1, hget, hr⟩ := RunsTo.bind hr
  obtain ⟨rfl, hw1⟩ := synthRead L hw hget
  dsimp only at hr
  obtain ⟨children, w2, hch, hr⟩ := RunsTo.bind hr
  obtain ⟨heq, rfl⟩ := RunsTo.pure_world hr
  obtain ⟨hlen, hk, hw2⟩ := mapM_hoare _ (InvV L)
    (fun (x : Name × List Nat × MixedGateBinder) y =>
      Sparkle.Compiler.MachMemory.memChild? x.1 = some y ∨ RealChild mref cref x.1 y)
    (fun x w y w' hp hy => by
      obtain ⟨hrc, hp'⟩ := synthesizeChild_inv L hB hp hy
      exact ⟨Or.inr hrc, hp'⟩)
    shape.insts children hw1 hch
  exact ⟨children, heq, ⟨hlen, hk⟩, hw2⟩

/-- **A run of the general closing, from an invariant world.** -/
theorem closeInstsGM_run (L : RefLaws mref cref) (hB : BodyRel L)
    {shape t m₀ d₀ r} {w w'} (hw : InvV L w)
    (hr : RunsTo (closeInstsGM shape t m₀ d₀) mctx mref cctx cref w r w') :
    ∃ children, r = Sparkle.IR.Machine.closeInstsG (machNIn shape) shape.insts.length
        shape.layout.slots.length (t.inputs.map (·.name)) (shape.insts.map (·.2.1))
        shape.instFields children (m₀, d₀) ∧ MemChildren shape children ∧
      ChildrenReal mref cref shape children ∧ InvV L w' := by
  unfold closeInstsGM at hr
  obtain ⟨synth?, w1, hget, hr⟩ := RunsTo.bind hr
  obtain ⟨rfl, hw1⟩ := synthRead L hw hget
  dsimp only at hr
  obtain ⟨children, w2, hch, hr⟩ := RunsTo.bind hr
  obtain ⟨heq, rfl⟩ := RunsTo.pure_world hr
  obtain ⟨hlen, hk, hw2⟩ := mapM_hoare _ (InvV L)
    (fun (x : Name × List Nat × MixedGateBinder) y =>
      (∀ md, Sparkle.Compiler.MachMemory.memChild? x.1 = some md → y = md) ∧
      (Sparkle.Compiler.MachMemory.memChild? x.1 = some y ∨ RealChild mref cref x.1 y))
    (fun x w y w' hp hy => by
      obtain ⟨c, b, k'⟩ := x
      dsimp only at hy ⊢
      cases hmc : Sparkle.Compiler.MachMemory.memChild? c with
      | some md =>
        rw [hmc] at hy
        obtain ⟨rfl, rfl⟩ := RunsTo.pure_world hy
        exact ⟨⟨fun md' h => by cases h; rfl, Or.inl rfl⟩, hp⟩
      | none =>
        rw [hmc] at hy
        obtain ⟨hrc, hp'⟩ := synthesizeChild_inv L hB hp hy
        exact ⟨⟨fun md' h => (by cases h), Or.inr hrc⟩, hp'⟩)
    shape.insts children hw1 hch
  refine ⟨children, heq, ?_, ⟨hlen, fun k hkl => ?_⟩, hw2⟩
  · intro k c hc md hmd
    have hkl : k < shape.insts.length := by
      have := (List.getElem?_eq_some_iff.mp hc).1; simpa using this
    obtain ⟨y, hky, hm, _⟩ := hk k hkl
    have hck : (shape.insts[k]).1 = c := by
      rw [List.getElem?_map, List.getElem?_eq_getElem hkl] at hc
      simpa using hc
    rw [← hck] at hmd
    rw [hm md hmd] at hky
    exact hky
  · obtain ⟨y, hky, _, hor⟩ := hk k hkl
    exact ⟨y, hky, hor⟩

/-- **The pure closing succeeds on real children**: for a transition the
harness returned and `closeLets` accepted, and children that are real
compiles of the calls' declarations. A statement about `closeInsts` /
`closeInstsG`, without a world. -/
def CallsPure (mref : ST.Ref IO.RealWorld Meta.State) (cref : ST.Ref IO.RealWorld Core.State)
    (declName : Name) (shape : MachineShape) : Prop :=
  ∀ (b : Bool) t d₀ t' children,
    MReturns (synthesizeMixedCertified
      (fun e hint top named => translateExprToWire e hint top named) (profLogIO b) declName
      shape.binders shape.body) (t, d₀) →
    Sparkle.IR.Machine.closeLets shape.layout.lets t = some t' →
    ChildrenReal mref cref shape children →
    (shape.instFields = [] →
      (Sparkle.IR.Machine.closeInsts (machNIn shape) shape.insts.length
        shape.layout.slots.length (t.inputs.map (·.name)) (shape.insts.map (·.2.1)) children
        (Sparkle.IR.Machine.closeMachine shape.layout t', d₀)).isSome = true) ∧
    (shape.instFields ≠ [] → MemChildren shape children →
      (Sparkle.IR.Machine.closeInstsG (machNIn shape) shape.insts.length
        shape.layout.slots.length (t.inputs.map (·.name)) (shape.insts.map (·.2.1))
        shape.instFields children
        (Sparkle.IR.Machine.closeMachine shape.layout t', d₀)).isSome = true)

/-- **`MachineClosesAt` from `LetsClose` and `CallsPure`** — under the generic
runtime laws alone. -/
theorem machineClosesAt_of_pure {declName : Name} {shape : MachineShape}
    (hl : LetsClose mctx mref cctx cref declName shape)
    (hp : CallsPure mref cref declName shape) :
    MachineClosesAt mctx mref cctx cref declName shape := by
  rintro ⟨L⟩ b w r w' hw' hr
  have hw := invV_of_invW mctx cctx L hw'
  have hB := bodyRel L
  unfold synthesizeMachineCertified at hr
  obtain ⟨⟨t, d'⟩, w1, run, hr⟩ := RunsTo.bind hr
  have hw1 := invV_of_invW mctx cctx L (harness_inv L hB (harnessRel_of L (translateRel L)) (invW_of_invV L hw) run)
  dsimp only at hr
  obtain ⟨t', ht'⟩ := Option.isSome_iff_exists.mp (hl (profLogIO b) w t d' w1 run)
  rw [ht'] at hr
  dsimp only at hr
  split at hr
  · have := RunsTo.pure_eq hr
    rw [this]
    exact Option.some_ne_none _
  · split at hr
    · rename_i hf
      obtain ⟨children, rfl, hreal, _⟩ := closeInstsM_run L hB hw1 hr
      have := (hp b t d' t' children run.mreturns ht' hreal).1 (List.isEmpty_iff.mp hf)
      intro h
      rw [h] at this
      cases this
    · rename_i hf
      obtain ⟨children, rfl, hmem, hreal, _⟩ := closeInstsGM_run L hB hw1 hr
      have := (hp b t d' t' children run.mreturns ht' hreal).2
        (fun h => hf (List.isEmpty_iff.mpr h)) hmem
      intro h
      rw [h] at this
      cases this

end Tools.ShippingChildInv
