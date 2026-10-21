import Tools.ShippingChildRunAKids
import Tools.ShippingChildRunAMain
import Tools.ShippingChildComposeC
import Tools.ShippingCallsClose
-- BUILT (unit CA): ca4 exit 0 (Tools.ShippingCallsCloseA); axioms standard (propext, Classical.choice, Quot.sound).
-- No `sorry`, no `axiom`, no `native_decide`, no new law / field.

/-! # Unit CA: `MachineClosesAtA` from `LetsClose` and `CallsPureA` (new boundary)

PROVED (relative to `O`, `hA`, the named premises):
* `closeInstsM_runC` / `closeInstsGM_runC`: a returning run of the closing from a `JQC O D` world
  (`BodyStepC O`) returns the PURE `closeInsts` / `closeInstsG` of `ChildrenRealA`-children —
  for ANY returned value `r` (`none` included; the `some` hypothesis of `closeInstsM_realC` /
  `closeInstsGM_realC` is dropped);
* `machineClosesAtA_of_pure`: `LetsClose` + `CallsPureA` + `BodyStepC O` + `htr` give `MachineClosesAtA`;
* `machineClosesAtA_of_tele`: the same with `BodyStepC`, `htr` built from `T`
  (premises: `O`, `hA`, `T`, `LetsClose`, `CallsPureA`).

PREMISES: `CallsPureA` (a pure statement about `closeInsts`/`closeInstsG`, no world) and
`LetsClose` are NOT proved here. `ChildrenRealA` is a HISTORY of past synthesis results, not
semantic correctness in the current environment; nothing here is a runtime-fit proof. -/

namespace Tools.ShippingCallsCloseA
open Lean Meta
open Tools.ShippingEntrySoundness
open Tools.ShippingMachineEntry
open Sparkle.Compiler.Elab
open Tools.ShippingClosesSplit
open Tools.ShippingChildInv
open Tools.ShippingChildInvA
open Tools.ShippingChildDepthC
open Tools.ShippingChildFresh
open Tools.ShippingChildBndInit
open Tools.ShippingChildBndCore
open Tools.ShippingChildVCA
open Tools.ShippingChildTranslateA
open Tools.ShippingChildCacheA
open Tools.ShippingChildFrontCP
open Tools.ShippingChildRunA
open Tools.ShippingChildRunAKids

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- **`CallsPure` on the new boundary**: `ChildrenReal` ↦ `ChildrenRealA O`, otherwise verbatim. -/
def CallsPureA (O : RefLawsAOps MkRefd mref cref) (declName : Name) (shape : MachineShape) : Prop :=
  ∀ {tenv : Lean.Environment}, ∀ (b : Bool) t d₀ t' children,
    MReturns (synthesizeMixedCertified
      (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b) declName
      shape.binders shape.body) (t, d₀) →
    Sparkle.IR.Machine.closeLets shape.layout.lets t = some t' →
    ChildrenRealA O shape children →
    (shape.instFields = [] →
      (Sparkle.IR.Machine.closeInsts (machNIn shape) shape.insts.length
        shape.layout.slots.length (t.inputs.map (·.name)) (shape.insts.map (·.2.1)) children
        (Sparkle.IR.Machine.closeMachine shape.layout t', d₀)).isSome = true) ∧
    (shape.instFields ≠ [] → MemChildren shape children →
      (Sparkle.IR.Machine.closeInstsG (machNIn shape) shape.insts.length
        shape.layout.slots.length (t.inputs.map (·.name)) (shape.insts.map (·.2.1))
        shape.instFields children
        (Sparkle.IR.Machine.closeMachine shape.layout t', d₀)).isSome = true)

/-- **A run of the one-output closing from a `JQC O D` world, whatever it returns.** -/
theorem closeInstsM_runC (O : RefLawsAOps MkRefd mref cref) (hB : BodyStepC O)
    (hA : AdmCtx O.quiet mctx cctx) {D : Nat}
    {shape : MachineShape} {t m₀ : Sparkle.IR.AST.Module} {d₀ : Sparkle.IR.AST.Design}
    {r : Option (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)} {w w' : Void IO.RealWorld}
    (hw : JQC O D w)
    (hr : RunsTo (closeInstsM shape t m₀ d₀) mctx mref cctx cref w r w') :
    ∃ children, r = Sparkle.IR.Machine.closeInsts (machNIn shape) shape.insts.length
        shape.layout.slots.length (t.inputs.map (·.name)) (shape.insts.map (·.2.1))
        children (m₀, d₀) ∧
      ChildrenRealA O shape children ∧ JQC O D w' := by
  unfold closeInstsM at hr
  obtain ⟨synth?, w1, hget, hr⟩ := RunsTo.bind hr
  obtain ⟨hw1, rfl⟩ := triple_runs (tripleC_synthRead O hA D) hw hget
  dsimp only at hr
  obtain ⟨children, w2, hch, hr⟩ := RunsTo.bind hr
  obtain ⟨heq, rfl⟩ := RunsTo.pure_world hr
  obtain ⟨hlen, hk, hw2⟩ := Tools.ShippingChildInv.mapM_hoare _ (JQC O D)
    (fun (x : Name × List Nat × MixedGateBinder) y => RealChildA O x.1 y)
    (fun x w y w' hp hy => synthesizeChild_realC O hB hA hp hy)
    shape.insts children hw1 hch
  exact ⟨children, heq, ⟨hlen, fun k hk' => by
    obtain ⟨y, hy, hre⟩ := hk k hk'
    exact ⟨y, hy, Or.inr hre⟩⟩, hw2⟩

/-- **A run of the general closing from a `JQC O D` world, whatever it returns.** -/
theorem closeInstsGM_runC (O : RefLawsAOps MkRefd mref cref) (hB : BodyStepC O)
    (hA : AdmCtx O.quiet mctx cctx) {D : Nat}
    {shape : MachineShape} {t m₀ : Sparkle.IR.AST.Module} {d₀ : Sparkle.IR.AST.Design}
    {r : Option (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)} {w w' : Void IO.RealWorld}
    (hw : JQC O D w)
    (hr : RunsTo (closeInstsGM shape t m₀ d₀) mctx mref cctx cref w r w') :
    ∃ children, r = Sparkle.IR.Machine.closeInstsG (machNIn shape) shape.insts.length
        shape.layout.slots.length (t.inputs.map (·.name)) (shape.insts.map (·.2.1))
        shape.instFields children (m₀, d₀) ∧ MemChildren shape children ∧
      ChildrenRealA O shape children ∧ JQC O D w' := by
  unfold closeInstsGM at hr
  obtain ⟨synth?, w1, hget, hr⟩ := RunsTo.bind hr
  obtain ⟨hw1, rfl⟩ := triple_runs (tripleC_synthRead O hA D) hw hget
  dsimp only at hr
  obtain ⟨children, w2, hch, hr⟩ := RunsTo.bind hr
  obtain ⟨heq, rfl⟩ := RunsTo.pure_world hr
  obtain ⟨hlen, hk, hw2⟩ := Tools.ShippingChildInv.mapM_hoare _ (JQC O D)
    (fun (x : Name × Sparkle.Compiler.MachInstOrigin.InstOrigin) y =>
      (∀ md, x.2.child? = some md → y = md) ∧
      (x.2.child? = some y ∨ RealChildA O x.1 y))
    (fun x w y w' hp hy => by
      obtain ⟨c, o⟩ := x
      dsimp only at hy ⊢
      cases hmc : Sparkle.Compiler.MachInstOrigin.InstOrigin.child? o with
      | some md =>
        rw [hmc] at hy
        obtain ⟨rfl, rfl⟩ := RunsTo.pure_world hy
        exact ⟨⟨fun md' h => by cases h; rfl, Or.inl rfl⟩, hp⟩
      | none =>
        rw [hmc] at hy
        obtain ⟨hrc, hp'⟩ := synthesizeChild_realC O hB hA hp hy
        exact ⟨⟨fun md' h => (by cases h), Or.inr hrc⟩, hp'⟩)
    shape.instTagged children hw1 hch
  have hlenI : children.length = shape.insts.length := by
    rw [hlen]; exact instTagged_length' shape
  refine ⟨children, heq, ?_, ⟨hlenI, fun k hkl => ?_⟩, hw2⟩
  · intro k hkl md hmd
    obtain ⟨hkT, he⟩ := instTagged_getAt shape hkl
    obtain ⟨y, hky, hm, _⟩ := hk k hkT
    rw [he] at hm
    rw [hm md hmd] at hky
    exact hky
  · obtain ⟨hkT, he⟩ := instTagged_getAt shape hkl
    obtain ⟨y, hky, _, hor⟩ := hk k hkT
    rw [he] at hor
    exact ⟨y, hky, hor⟩

/-- **`MachineClosesAtA` from `LetsClose` and `CallsPureA`** (ported from `machineClosesAt_of_pure`,
without `RefLaws`). Premises: `BodyStepC O`, `htr` (restricted translator keeps `JQC O n`). -/
theorem machineClosesAtA_of_pure (O : RefLawsAOps MkRefd mref cref) (hB : BodyStepC O)
    (hA : AdmCtx O.quiet mctx cctx) {declName : Name} {shape : MachineShape}
    (htr : ∀ (tenv : Lean.Environment) (D : Nat) e hint top named,
      KeepsCP mctx mref cctx cref (JQC O (D + 1)) (translateExprToWire tenv e hint top named))
    (hl : LetsClose mctx mref cctx cref declName shape)
    (hp : CallsPureA O declName shape) :
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx declName shape := by
  intro tenv b n w r w' hw hn hr
  obtain ⟨D, rfl⟩ : ∃ D, n = D + 1 := ⟨n - 1, by omega⟩
  unfold synthesizeMachineCertified at hr
  obtain ⟨⟨t, d'⟩, w1, run, hr⟩ := RunsTo.bind hr
  have hw1 := triple_runs (keeps_iff.mp (mixed_keepsAP O hA (stableA_JQC O (D + 1)) _ b declName
    shape.binders shape.body (htr tenv D))) hw run
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
      obtain ⟨children, rfl, hreal, _⟩ := closeInstsM_runC O hB hA hw1 hr
      have := (hp b t d' t' children run.mreturns ht' hreal).1 (List.isEmpty_iff.mp hf)
      intro h
      rw [h] at this
      cases this
    · rename_i hf
      obtain ⟨children, rfl, hmem, hreal, _⟩ := closeInstsGM_runC O hB hA hw1 hr
      have := (hp b t d' t' children run.mreturns ht' hreal).2
        (fun h => hf (List.isEmpty_iff.mpr h)) hmem
      intro h
      rw [h] at this
      cases this

/-- **`MachineClosesAtA` from `T`, `LetsClose`, `CallsPureA`** (`BodyStepC`, `htr` built from `T`). -/
theorem machineClosesAtA_of_tele (O : RefLawsAOps MkRefd mref cref)
    (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {declName : Name} {shape : MachineShape}
    (hl : LetsClose mctx mref cctx cref declName shape)
    (hp : CallsPureA O declName shape) :
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx declName shape :=
  machineClosesAtA_of_pure O (Tools.ShippingChildComposeC.bodyStepC_of_tele O T) hA
    (fun tenv D => Tools.ShippingChildRunAMain.htr_of_tele O hA T D tenv) hl hp

end Tools.ShippingCallsCloseA

#print axioms Tools.ShippingCallsCloseA.machineClosesAtA_of_tele
