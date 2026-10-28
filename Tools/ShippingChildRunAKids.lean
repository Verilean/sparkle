import Tools.ShippingChildRunA
import Tools.ShippingChildDepthC
import Tools.ShippingChildFrontCP
import Tools.ShippingChildRun
-- BUILT (unit G, par/u-g): g11 exit 0 (Tools.ShippingChildRunAKids); audit g13 exit 0 (Tests.Compiler.ChildVertAuditTest: no RefLaws/RefLawsCore/toAOps/toA in the closures; axioms standard).
-- No `sorry`, no `axiom`, no `native_decide`, no new law / field. Law witness `O : RefLawsAOps MkRefd mref cref`
-- at `hA : AdmCtx O.quiet mctx cctx`. `Tools.ShippingChildRun` is imported ONLY for the law-free
-- `mapM_hoare`; nothing of the old `RefLaws`/`InvV`/`ChildBnd` chain is used (audit checks the closure).
-- Writing-time guesses (marked `-- guess: Hn`): copies of the BUILT old `closeInstsGM_inv`,
-- `synthesizeMachineCertified_inv`, `machine_children_realA` (ShippingChildRun.lean:262-500) with
-- `InvV L` ↦ `JQC O D`, `synthesizeChild_inv` ↦ `synthesizeChild_realC`, `RealChild` ↦ `RealChildA`.

/-! # Row L6: the children of a real core run are `RealChildA`s (new boundary)

PROVED (relative to `O`, `hA`, the named premises of each statement):
* `closeInstsGM_realC`: the general closing's children, call by call (origin-built or `RealChildA`),
  from `BodyStepC O` (the one-output closing is `Tools.ShippingChildDepthC.closeInstsM_realC`);
* `synthesizeMachineCertified_runsA`: a returning run of `synthesizeMachineCertified` from a `JQC O n`
  world — harness (premise `htr`: the RESTRICTED translator keeps `JQC O n`, via `mixed_keepsAP`),
  `closeLets`, closing — has `ChildrenRealA` children;
* `machine_children_realA'`: the same for a returning run of the CORE entry from a `JQ O.quiet D` world
  (+ cache half when `D ≠ 0`), through `machine_run_of_coreA`.

PREMISES (hypotheses, named): `BodyStepC O` (ComposeC `bodyStepC_of_tele` proves it from `T`);
`htr` (the restricted translator keeps `JQC O (D + 1)`; ComposeC builds it per step from the handlers);
`MachineClosesAtA` (the machine synthesis does not fall back — the analogue of the old `MachineClosesAt`).
`ChildrenRealA` is a HISTORY of past synthesis results, not semantic correctness in the current
environment, and `JQC` is not freshness. Nothing here is RTL semantic preservation or a runtime-fit proof. -/

namespace Tools.ShippingChildRunAKids
open Lean Meta
open Tools.ShippingEntrySoundness
open Tools.ShippingMachineEntry
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv
open Tools.ShippingChildBndInit
open Tools.ShippingChildBndCore
open Tools.ShippingChildInvA
open Tools.ShippingChildFresh
open Tools.ShippingChildVCA
open Tools.ShippingChildTranslateA
open Tools.ShippingChildCacheA
open Tools.ShippingChildDepthC
open Tools.ShippingChildFrontCP
open Tools.ShippingChildRunA

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- The new `ChildrenReal`: every child is the origin-built module or a `RealChildA` of the call. -/
def ChildrenRealA (O : RefLawsAOps MkRefd mref cref) (shape : MachineShape)
    (children : List Res) : Prop :=
  children.length = shape.insts.length ∧
  ∀ k (hk : k < shape.insts.length), ∃ y, children[k]? = some y ∧
    ((shape.instOrigins.getD k .ord).child? = some y ∨
      RealChildA O (shape.insts[k]).1 y)

/-- **The general closing's children, world by world** (`closeInstsGM_inv` on the new boundary). -/
theorem closeInstsGM_realC (O : RefLawsAOps MkRefd mref cref) (hB : BodyStepC O)
    (hA : AdmCtx O.quiet mctx cctx) {D : Nat}
    {shape : MachineShape} {t m₀ : Sparkle.IR.AST.Module} {d₀ : Sparkle.IR.AST.Design}
    {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design} {w w' : Void IO.RealWorld}
    (hw : JQC O D w)
    (hr : RunsTo (closeInstsGM shape t m₀ d₀) mctx mref cctx cref w (some (m, d)) w') :
    ∃ children, Sparkle.IR.Machine.closeInstsG (machNIn shape) shape.insts.length
        shape.layout.slots.length (t.inputs.map (·.name)) (shape.insts.map (·.2.1))
        shape.instFields children (m₀, d₀) = some (m, d) ∧ MemChildren shape children ∧
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
    shape.instTagged children hw1 hch  -- guess: H1
  have hlenI : children.length = shape.insts.length := by
    rw [hlen]; exact instTagged_length' shape
  refine ⟨children, heq.symm, ?_, ⟨hlenI, fun k hkl => ?_⟩, hw2⟩
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

/-- **The machine synthesis, with its children, from a `JQC O n` world.** The harness keeps `JQC O n`
(`mixed_keepsAP`, premise `htr`: the restricted translator keeps it); the closings' children are
`ChildrenRealA`. -/
theorem synthesizeMachineCertified_runsA (O : RefLawsAOps MkRefd mref cref) (hB : BodyStepC O)
    (hA : AdmCtx O.quiet mctx cctx) {n : Nat} {tenv : Lean.Environment}
    (htr : ∀ e hint top named, KeepsCP mctx mref cctx cref (JQC O n)
      (translateExprToWire tenv e hint top named))
    {b : Bool} {declName shape m d} {w w'} (hw : JQC O n w)
    (hr : RunsTo (synthesizeMachineCertified
      (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b) declName shape)
      mctx mref cctx cref w (some (m, d)) w') :
    ∃ t t' d₀, MReturns (synthesizeMixedCertified
        (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b) declName
        shape.binders shape.body) (t, d₀) ∧
      Sparkle.IR.Machine.closeLets shape.layout.lets t = some t' ∧
      ((shape.insts = [] ∧ m = Sparkle.IR.Machine.closeMachine shape.layout t' ∧ d = d₀) ∨
       (shape.insts ≠ [] ∧ ∃ children,
          CloseCalls shape t (Sparkle.IR.Machine.closeMachine shape.layout t') d₀ children m d ∧
          ChildrenRealA O shape children)) := by
  unfold synthesizeMachineCertified at hr
  obtain ⟨⟨t, d'⟩, w1, run, hr⟩ := RunsTo.bind hr
  have hw1 := triple_runs (keeps_iff.mp (mixed_keepsAP O hA (stableA_JQC O n) _ b declName
    shape.binders shape.body htr)) hw run
  dsimp only at hr
  split at hr
  · rename_i t' hcl
    split at hr
    · rename_i hi
      have eq := RunsTo.pure_eq hr
      simp only [Option.some.injEq, Prod.mk.injEq] at eq
      obtain ⟨hm, hd⟩ := eq
      exact ⟨t, t', d', run.mreturns, hcl, Or.inl ⟨hi, hm, hd⟩⟩
    · rename_i hi
      have hne : shape.insts ≠ [] := by rw [hi]; exact List.cons_ne_nil _ _
      split at hr
      · rename_i hf
        obtain ⟨children, hc, hlen, hreal, _⟩ := closeInstsM_realC O hB hA hw1 hr
        exact ⟨t, t', d', run.mreturns, hcl, Or.inr ⟨hne, children,
          Or.inl ⟨List.isEmpty_iff.mp hf, hc⟩,
          ⟨hlen, fun k hk => by
            obtain ⟨y, hy, hre⟩ := hreal k hk
            exact ⟨y, hy, Or.inr hre⟩⟩⟩⟩
      · rename_i hf
        obtain ⟨children, hc, hmc, hreal, _⟩ := closeInstsGM_realC O hB hA hw1 hr
        exact ⟨t, t', d', run.mreturns, hcl, Or.inr ⟨hne, children,
          Or.inr ⟨fun h => hf (List.isEmpty_iff.mpr h), hc, hmc⟩, hreal⟩⟩
  · have eq := RunsTo.pure_eq hr
    cases eq

/-- **The machine synthesis does not fall back — where a real compile runs it** (PREMISE; analogue
of the old `MachineClosesAt`): from a `JQC O n` world at depth `n ≥ 1`, with the compiler's own
logger, the run does not return `none`. -/
def MachineClosesAtA (O : RefLawsAOps MkRefd mref cref) (mctx : Meta.Context)
    (cctx : Core.Context) (declName : Name) (shape : MachineShape) : Prop :=
  ∀ {tenv : Lean.Environment}, ∀ (b : Bool) (n : Nat) w r w', JQC O n w → 1 ≤ n →
    RunsTo (synthesizeMachineCertified
      (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b) declName shape)
      mctx mref cctx cref w r w' → r ≠ none

/-- **The children of a real compile, from the run's start world** (new boundary; analogue of
`machine_children_realA`). Premises: `BodyStepC O`, the translator `htr` at `JQC O (D + 1)`, and
`MachineClosesAtA`. -/
theorem machine_children_realA' (O : RefLawsAOps MkRefd mref cref) (hB : BodyStepC O)
    (hA : AdmCtx O.quiet mctx cctx) {declName : Name} {shape : MachineShape} {D : Nat}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, d) w')
    (entry : MachineDefines mctx mref cctx cref declName shape)
    (htr : ∀ (tenv : Lean.Environment) e hint top named, KeepsCP mctx mref cctx cref (JQC O (D + 1))
      (translateExprToWire tenv e hint top named))
    (closes : MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx declName shape)
    (hw : JQ O.quiet D w) (hc : D = 0 ∨ CacheInvA O (cv w)) (hi : shape.insts ≠ []) :
    ∃ t t' d₀ children,
      Sparkle.IR.Machine.closeLets shape.layout.lets t = some t' ∧
      CloseCalls shape t (Sparkle.IR.Machine.closeMachine shape.layout t') d₀ children m d ∧
      ChildrenRealA O shape children := by
  obtain ⟨tenv, b, r, w9, w10, hrun, hw9, hres⟩ := machine_run_of_coreA O hA hr entry hw hc
  have hne := closes b (D + 1) w9 r w10 hw9 (by omega) hrun
  cases r with
  | none => exact absurd rfl hne
  | some res =>
    have := hres res rfl
    subst this
    obtain ⟨t, t', d₀, _, hcl, hmt⟩ :=
      synthesizeMachineCertified_runsA O hB hA (htr tenv) hw9 hrun
    rcases hmt with ⟨h0, _, _⟩ | ⟨_, children, hcc, hreal⟩
    · exact absurd h0 hi
    · exact ⟨t, t', d₀, children, hcl, hcc, hreal⟩

end Tools.ShippingChildRunAKids
