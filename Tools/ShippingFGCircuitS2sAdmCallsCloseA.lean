import Tools.ShippingCallsCloseA
import Tools.ShippingFGCircuitS2sAdmLawsX
import Tools.ShippingFGCircuitS2sAdmS2hHist
import Tools.ShippingFGCircuitS2sAdmS2hHist2
import Tools.ShippingFGCircuitS2sAdmChildCacheA
import Tools.ShippingFGCircuitS2sAdmChildCanonKeyA
import Tools.ShippingFGCircuitS2sAdmChildComposeA
import Tools.ShippingFGCircuitS2sAdmChildComposeC
import Tools.ShippingFGCircuitS2sAdmChildCoreC
import Tools.ShippingFGCircuitS2sAdmChildDepthA
import Tools.ShippingFGCircuitS2sAdmChildDepthC
import Tools.ShippingFGCircuitS2sAdmChildFallbackA
import Tools.ShippingFGCircuitS2sAdmChildFrontA
import Tools.ShippingFGCircuitS2sAdmChildFrontCP
import Tools.ShippingFGCircuitS2sAdmChildInvA
import Tools.ShippingFGCircuitS2sAdmChildLegacyCachedA
import Tools.ShippingFGCircuitS2sAdmChildLegacyHandlersA
import Tools.ShippingFGCircuitS2sAdmChildLegacyHelpersA
import Tools.ShippingFGCircuitS2sAdmChildLegacyImplA
import Tools.ShippingFGCircuitS2sAdmChildLegacyTailA
import Tools.ShippingFGCircuitS2sAdmChildMainA
import Tools.ShippingFGCircuitS2sAdmChildPathA
import Tools.ShippingFGCircuitS2sAdmChildPinC
import Tools.ShippingFGCircuitS2sAdmChildProjFieldA
import Tools.ShippingFGCircuitS2sAdmChildRunA
import Tools.ShippingFGCircuitS2sAdmChildRunAKids
import Tools.ShippingFGCircuitS2sAdmChildRunAMain
import Tools.ShippingFGCircuitS2sAdmChildTeleCP
import Tools.ShippingFGCircuitS2sAdmChildTeleLocalA
import Tools.ShippingFGCircuitS2sAdmChildTeleMainA
import Tools.ShippingFGCircuitS2sAdmChildTranslateA
import Tools.ShippingFGCircuitS2sAdmChildTranslatePathA
import Tools.ShippingFGCircuitS2sAdmChildVCA
import Tools.ShippingFGCircuitS2sAdmChildVertA
import Tools.ShippingFGCircuitS2sAdmChildWalkA
import Tools.ShippingFGCircuitS2sAdmKWalk
import Tools.ShippingChildRunAKids
import Tools.ShippingChildComposeC
import Tools.ShippingFGCircuitS2sAdmChildPinC
-- FG circuit pilot S2s4: SELECTIVE port of ShippingCallsCloseA.lean onto the context-predicate bundles (only the declarations that mention RefLawsAOps/AdmCtx/Laws/... or an already-ported name; the rest is taken from the imported original); rename-only script scripts/s2s_port2.py (suffix X, `AdmCtx O.quiet` -> `O.adm`). No sorry/axiom/native_decide/TRUSTED/law.
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
`LetsClose` are UNRESOLVED SUFFICIENT CONDITIONS for `MachineClosesAtA`: NOT proved here in general. `ChildrenRealA` is a HISTORY of past synthesis results, not
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

/-- **`CallsPure` on the new boundary**: `ChildrenReal` ↦ `ChildrenRealAX O`, otherwise verbatim. -/
def CallsPureAX (O : RefLawsAOpsX MkRefd mref cref) (declName : Name) (shape : MachineShape) : Prop :=
  ∀ {tenv : Lean.Environment}, ∀ (b : Bool) t d₀ t' children,
    MReturns (synthesizeMixedCertified
      (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b) declName
      shape.binders shape.body) (t, d₀) →
    Sparkle.IR.Machine.closeLets shape.layout.lets t = some t' →
    ChildrenRealAX O shape children →
    (shape.instFields = [] →
      (Sparkle.IR.Machine.closeInsts (machNIn shape) shape.insts.length
        shape.layout.slots.length (t.inputs.map (·.name)) (shape.insts.map (·.2.1)) children
        (Sparkle.IR.Machine.closeMachine shape.layout t', d₀)).isSome = true) ∧
    (shape.instFields ≠ [] → MemChildren shape children →
      (Sparkle.IR.Machine.closeInstsG (machNIn shape) shape.insts.length
        shape.layout.slots.length (t.inputs.map (·.name)) (shape.insts.map (·.2.1))
        shape.instFields children
        (Sparkle.IR.Machine.closeMachine shape.layout t', d₀)).isSome = true)


/-- **A run of the one-output closing from a `JQCX O D` world, whatever it returns.** -/
theorem closeInstsM_runCX (O : RefLawsAOpsX MkRefd mref cref) (hB : BodyStepCX O)
    (hA : O.adm mctx cctx) {D : Nat}
    {shape : MachineShape} {t m₀ : Sparkle.IR.AST.Module} {d₀ : Sparkle.IR.AST.Design}
    {r : Option (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)} {w w' : Void IO.RealWorld}
    (hw : JQCX O D w)
    (hr : RunsTo (closeInstsM shape t m₀ d₀) mctx mref cctx cref w r w') :
    ∃ children, r = Sparkle.IR.Machine.closeInsts (machNIn shape) shape.insts.length
        shape.layout.slots.length (t.inputs.map (·.name)) (shape.insts.map (·.2.1))
        children (m₀, d₀) ∧
      ChildrenRealAX O shape children ∧ JQCX O D w' := by
  unfold closeInstsM at hr
  obtain ⟨synth?, w1, hgetX, hr⟩ := RunsTo.bind hr
  obtain ⟨hw1, rfl⟩ := triple_runsX (tripleC_synthReadX O hA D) hw hgetX
  dsimp only at hr
  obtain ⟨children, w2, hch, hr⟩ := RunsTo.bind hr
  obtain ⟨heq, rfl⟩ := RunsTo.pure_world hr
  obtain ⟨hlen, hk, hw2⟩ := Tools.ShippingChildInv.mapM_hoare _ (JQCX O D)
    (fun (x : Name × List Nat × MixedGateBinder) y => RealChildAX O x.1 y)
    (fun x w y w' hp hy => synthesizeChild_realCX O hB hA hp hy)
    shape.insts children hw1 hch
  exact ⟨children, heq, ⟨hlen, fun k hk' => by
    obtain ⟨y, hy, hre⟩ := hk k hk'
    exact ⟨y, hy, Or.inr hre⟩⟩, hw2⟩


/-- **A run of the general closing from a `JQCX O D` world, whatever it returns.** -/
theorem closeInstsGM_runCX (O : RefLawsAOpsX MkRefd mref cref) (hB : BodyStepCX O)
    (hA : O.adm mctx cctx) {D : Nat}
    {shape : MachineShape} {t m₀ : Sparkle.IR.AST.Module} {d₀ : Sparkle.IR.AST.Design}
    {r : Option (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)} {w w' : Void IO.RealWorld}
    (hw : JQCX O D w)
    (hr : RunsTo (closeInstsGM shape t m₀ d₀) mctx mref cctx cref w r w') :
    ∃ children, r = Sparkle.IR.Machine.closeInstsG (machNIn shape) shape.insts.length
        shape.layout.slots.length (t.inputs.map (·.name)) (shape.insts.map (·.2.1))
        shape.instFields children (m₀, d₀) ∧ MemChildren shape children ∧
      ChildrenRealAX O shape children ∧ JQCX O D w' := by
  unfold closeInstsGM at hr
  obtain ⟨synth?, w1, hgetX, hr⟩ := RunsTo.bind hr
  obtain ⟨hw1, rfl⟩ := triple_runsX (tripleC_synthReadX O hA D) hw hgetX
  dsimp only at hr
  obtain ⟨children, w2, hch, hr⟩ := RunsTo.bind hr
  obtain ⟨heq, rfl⟩ := RunsTo.pure_world hr
  obtain ⟨hlen, hk, hw2⟩ := Tools.ShippingChildInv.mapM_hoare _ (JQCX O D)
    (fun (x : Name × Sparkle.Compiler.MachInstOrigin.InstOrigin) y =>
      (∀ md, x.2.child? = some md → y = md) ∧
      (x.2.child? = some y ∨ RealChildAX O x.1 y))
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
        obtain ⟨hrc, hp'⟩ := synthesizeChild_realCX O hB hA hp hy
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


/-- **`MachineClosesAtAX` from `LetsClose` and `CallsPureAX`** (ported from `machineClosesAt_of_pure`,
without `RefLaws`). Premises: `BodyStepCX O`, `htr` (restricted translator keeps `JQCX O n`). -/
theorem machineClosesAtA_of_pureX (O : RefLawsAOpsX MkRefd mref cref) (hB : BodyStepCX O)
    (hA : O.adm mctx cctx) {declName : Name} {shape : MachineShape}
    (htr : ∀ (tenv : Lean.Environment) (D : Nat) e hint top named,
      KeepsCP mctx mref cctx cref (JQCX O (D + 1)) (translateExprToWire tenv e hint top named))
    (hl : LetsClose mctx mref cctx cref declName shape)
    (hp : CallsPureAX O declName shape) :
    MachineClosesAtAX (mref := mref) (cref := cref) O mctx cctx declName shape := by
  intro tenv b n w r w' hw hn hr
  obtain ⟨D, rfl⟩ : ∃ D, n = D + 1 := ⟨n - 1, by omega⟩
  unfold synthesizeMachineCertified at hr
  obtain ⟨⟨t, d'⟩, w1, run, hr⟩ := RunsTo.bind hr
  have hw1 := triple_runsX (keeps_iff.mp (mixed_keepsAPX O hA (stableA_JQCX O (D + 1)) _ b declName
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
      obtain ⟨children, rfl, hreal, _⟩ := closeInstsM_runCX O hB hA hw1 hr
      have := (hp b t d' t' children run.mreturns ht' hreal).1 (List.isEmpty_iff.mp hf)
      intro h
      rw [h] at this
      cases this
    · rename_i hf
      obtain ⟨children, rfl, hmem, hreal, _⟩ := closeInstsGM_runCX O hB hA hw1 hr
      have := (hp b t d' t' children run.mreturns ht' hreal).2
        (fun h => hf (List.isEmpty_iff.mpr h)) hmem
      intro h
      rw [h] at this
      cases this


/-- **`MachineClosesAtAX` from `T`, `LetsClose`, `CallsPureAX`** (`BodyStepCX`, `htr` built from `T`). -/
theorem machineClosesAtA_of_teleX (O : RefLawsAOpsX MkRefd mref cref)
    (T : RefLawsATeleX O.quiet O.adm mref cref) (hA : O.adm mctx cctx)
    {declName : Name} {shape : MachineShape}
    (hl : LetsClose mctx mref cctx cref declName shape)
    (hp : CallsPureAX O declName shape) :
    MachineClosesAtAX (mref := mref) (cref := cref) O mctx cctx declName shape :=
  machineClosesAtA_of_pureX O (Tools.ShippingChildComposeC.bodyStepC_of_teleX O T) hA
    (fun tenv D => Tools.ShippingChildRunAMain.htr_of_teleX O hA T D tenv) hl hp

end Tools.ShippingCallsCloseA

#print axioms Tools.ShippingCallsCloseA.machineClosesAtA_of_teleX

