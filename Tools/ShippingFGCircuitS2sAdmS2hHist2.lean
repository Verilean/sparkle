import Tools.ShippingChildRunAKids
import Tools.ShippingChildComposeC
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
import Tools.ShippingFGCircuitS2sAdmChildProjFieldA
import Tools.ShippingFGCircuitS2sAdmChildRunA
import Tools.ShippingFGCircuitS2sAdmChildRunAKids
import Tools.ShippingFGCircuitS2sAdmChildTeleCP
import Tools.ShippingFGCircuitS2sAdmChildTeleLocalA
import Tools.ShippingFGCircuitS2sAdmChildTranslateA
import Tools.ShippingFGCircuitS2sAdmChildTranslatePathA
import Tools.ShippingFGCircuitS2sAdmChildVCA
import Tools.ShippingFGCircuitS2sAdmChildVertA
import Tools.ShippingFGCircuitS2sAdmChildWalkA
import Tools.ShippingFGCircuitS2sAdmKWalk
import Tools.ShippingFGCircuitS2sAdmS2hHist
import Tools.ShippingFGCircuitS2hHist2
-- FG circuit pilot S2s4: REGENERATED port of Tools.ShippingFGCircuitS2hHist2 onto the context-predicate bundles (RefLawsAOpsX / RefLawsATeleX); rename-only script (names + suffix X, `AdmCtx O.quiet` -> `O.adm`). No sorry/axiom/native_decide/TRUSTED/law.
set_option autoImplicit false
-- FG circuit pilot S2h (part 2): the depth induction, the body, the closing and `MachineClosesAtHX` at the history invariant `JQHX`. Copies of ShippingChildDepthC / ShippingChildComposeC / ShippingCallsCloseA / ShippingCallsGateA with `JQCX` ↦ `JQHX O E`, `RealChildAX` ↦ `RealChildEX O E`; the miss premise `MissEX` is threaded to the one place the cache is written (`synthesizeChild_tripleHX`). No `sorry`, no `axiom`, no `native_decide`, no TRUSTED, no new law. Results: docs/FG-CIRCUIT-PILOT.md §34.

namespace Tools.ShippingFGCircuitS2hHist
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData Tools.ShippingMachineCloses
open Tools.ShippingMixedEntrySoundness
open Tools.ShippingCallsShape Tools.ShippingCallsRun Tools.ShippingCallsAssembly
open Tools.ShippingGateChildComb Tools.ShippingChildInv Tools.ShippingRankRun
open Tools.ShippingInlineSoundness (EntryDefines)
open Tools.ShippingCallsGate
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Tools.ShippingClosesSplit
open Tools.ShippingChildBndInit Tools.ShippingChildBndCore
open Tools.ShippingChildInvA Tools.ShippingChildVCA Tools.ShippingChildDepthC
open Tools.ShippingChildFresh Tools.ShippingChildCacheA Tools.ShippingChildRunAKids
open Tools.ShippingChildCoreC Tools.ShippingChildRunA
open Tools.ShippingCallsCloseA Tools.ShippingCallsGateA
open Tools.ShippingChildTranslateA Tools.ShippingChildFrontCP Tools.ShippingChildFallbackA
open Tools.ShippingChildComposeC Tools.ShippingChildRunAMain

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-! ## the depth induction at `JQHX` -/

def ChildKeepsHX (O : RefLawsAOpsX MkRefd mref cref) (E : StartEv) (D : Nat) : Prop :=
  ∀ (mctx : Meta.Context) (cctx : Core.Context), O.adm mctx cctx →
    ∀ c, Keeps mctx mref cctx cref (JQHX O E D) (synthesizeChild c)

def BodyKeepsHX (O : RefLawsAOpsX MkRefd mref cref) (E : StartEv) (D : Nat) : Prop :=
  ∀ (mctx : Meta.Context) (cctx : Core.Context), O.adm mctx cctx →
    ∀ (declName : Name) (tenv : Lean.Environment) (b : Bool) (ci : ConstantInfo)
      (isInst : Lean.Expr → Bool),
    Keeps mctx mref cctx cref (JQHX O E D)
      (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b)
        declName [] false true ci isInst)

def BodyStepHX (O : RefLawsAOpsX MkRefd mref cref) (E : StartEv) : Prop :=
  ∀ D, 1 ≤ D → ChildKeepsHX O E D → BodyKeepsHX O E D

/-- one step: the child entry at `D ≥ 1` from the body at `D + 1` (the miss premise is used here, in `synthesizeChild_tripleH'X`) -/
theorem childKeepsH_of_bodyX (O : RefLawsAOpsX MkRefd mref cref) {E : StartEv} (hmiss : MissEX O E) (D : Nat)
    (hD : 1 ≤ D) (hB : D < sparkleSynthDepthLimit → BodyKeepsHX O E (D + 1)) : ChildKeepsHX O E D := by
  intro mctx cctx hA c
  rw [keeps_iff]
  refine Triple.conseq (synthesizeChild_tripleH'X O hA hD hmiss (n := c) ?_)
    (fun _ h => h) (fun _ _ h => h.2) (fun _ _ h => h)
  intro tenv hl b ci isInst
  exact hB hl mctx cctx hA c tenv b ci isInst

theorem childKeepsH_allX (O : RefLawsAOpsX MkRefd mref cref) {E : StartEv} (hmiss : MissEX O E) (hB : BodyStepHX O E) :
    ∀ D, 1 ≤ D → ChildKeepsHX O E D := by
  have key : ∀ k D, sparkleSynthDepthLimit - D = k → 1 ≤ D → ChildKeepsHX O E D := by
    intro k
    induction k with
    | zero =>
      intro D hk hD
      exact childKeepsH_of_bodyX O hmiss D hD (fun hl => absurd hl (by omega))
    | succ k ih =>
      intro D hk hD
      exact childKeepsH_of_bodyX O hmiss D hD
        (fun _ => hB (D + 1) (by omega) (ih (D + 1) (by omega) (by omega)))
  intro D hD
  exact key _ D rfl hD

theorem tripleH_synthReadX (O : RefLawsAOpsX MkRefd mref cref) {E : StartEv} (hA : O.adm mctx cctx)
    (D : Nat) :
    Triple mctx mref cctx cref (JQHX O E D) (sparkleChildSynth.get : MetaM _)
      (fun s w => JQHX O E D w ∧ s = some synthesizeChild)
      (fun e w => JQHX O E D w ∧ OkExc e) := by
  intro w hw
  have hK := keeps_iff.mp (keepsA_framedX O hA (stableA_JQHX O E D) FramedA.synthGet) w hw
  cases hm : (sparkleChildSynth.get : MetaM _) mctx mref cctx cref w with
  | ok a w1 =>
    rw [hm] at hK
    exact ⟨hK, (runsTo_get_readOf _ hm).trans hw.1.2.1⟩
  | error e w1 => rw [hm] at hK; exact hK

theorem childEntryA_of_childKeepsHX (O : RefLawsAOpsX MkRefd mref cref) {E : StartEv} (D : Nat)
    (hC : ChildKeepsHX O E D) : ChildEntryAX O (JQHX O E D) := by
  intro mctx cctx hA c
  rw [keeps_iff]
  unfold childSynthEntry
  refine Triple.bindQ (tripleH_synthReadX O hA D) ?_
  intro s hs
  subst hs
  exact keeps_iff.mp (hC mctx cctx hA c)

theorem hbodyH_of_stepX (O : RefLawsAOpsX MkRefd mref cref) {E : StartEv} (hB : BodyStepHX O E) (hmiss : MissEX O E)
    (hA : O.adm mctx cctx) (D : Nat) (c : Name) :
    ∀ {tenv : Lean.Environment}, D < sparkleSynthDepthLimit → ∀ (b : Bool) ci isInst,
      Keeps mctx mref cctx cref (JQHX O E (D + 1))
        (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b)
          c [] false true ci isInst) :=
  fun {tenv} _ b ci isInst =>
    hB (D + 1) (by omega) (childKeepsH_allX O hmiss hB (D + 1) (by omega)) mctx cctx hA c tenv b ci isInst

/-! ## the body at `JQHX` from the telescope laws (the handlers are generic in the stable invariant) -/

theorem translate_keepsH_of_teleX (O : RefLawsAOpsX MkRefd mref cref) {E : StartEv}
    (T : RefLawsATeleX O.quiet O.adm mref cref) (D : Nat) (hC : ChildKeepsHX O E D) (tenv : Lean.Environment) :
    RecAX O (JQHX O E D) (fun e h t n => translateExprToWire tenv e h t n) :=
  have hS := stableA_JQHX O E D
  have hchild : ChildEntryAX O (JQHX O E D) := childEntryA_of_childKeepsHX O D hC
  have hcanon : CanonKeyAX O (JQHX O E D) := Tools.ShippingChildCanonKeyA.canonKeyAX O hS
  have hImpl : LegacyImplAX O (JQHX O E D) :=
    Tools.ShippingChildLegacyImplA.legacyImplA_of_teleX O hS T hcanon hchild
  translate_keepsAX O hS tenv hImpl
    (Tools.ShippingChildLegacyCachedA.legacyCachedA_of_implX O hS hImpl) hcanon
    (Tools.ShippingChildProjFieldA.projFieldNameAX O T hS) hchild

theorem bodyKeepsH_of_teleX (O : RefLawsAOpsX MkRefd mref cref) {E : StartEv}
    (T : RefLawsATeleX O.quiet O.adm mref cref) (D : Nat) (hC : ChildKeepsHX O E D) : BodyKeepsHX O E D :=
  have hS := stableA_JQHX O E D
  have hchild : ChildEntryAX O (JQHX O E D) := childEntryA_of_childKeepsHX O D hC
  have hcanon : CanonKeyAX O (JQHX O E D) := Tools.ShippingChildCanonKeyA.canonKeyAX O hS
  have hImpl : LegacyImplAX O (JQHX O E D) :=
    Tools.ShippingChildLegacyImplA.legacyImplA_of_teleX O hS T hcanon hchild
  fun mctx cctx hA declName tenv b ci isInst =>
    fromConst_frontends_of_handlersX O hA hS hImpl
      (Tools.ShippingChildLegacyCachedA.legacyCachedA_of_implX O hS hImpl) hcanon
      (Tools.ShippingChildProjFieldA.projFieldNameAX O T hS) hC (fun _ h => h.1.2.1)
      tenv b declName ci isInst
      (fun _ _ => Tools.ShippingChildLegacyTailA.legacyTailA_genericX O T hS hA _
        (translate_keepsH_of_teleX O T D hC tenv) b declName ci isInst)

theorem bodyStepH_of_teleX (O : RefLawsAOpsX MkRefd mref cref) {E : StartEv} (T : RefLawsATeleX O.quiet O.adm mref cref) :
    BodyStepHX O E :=
  fun D _ hC => bodyKeepsH_of_teleX O T D hC

theorem childKeepsH_all_of_teleX (O : RefLawsAOpsX MkRefd mref cref) {E : StartEv}
    (T : RefLawsATeleX O.quiet O.adm mref cref) (hmiss : MissEX O E) :
    ∀ D, 1 ≤ D → ChildKeepsHX O E D :=
  childKeepsH_allX O hmiss (bodyStepH_of_teleX O T)

/-- the restricted translator keeps `JQHX O E (D + 1)` -/
theorem htrH_of_teleX (O : RefLawsAOpsX MkRefd mref cref) {E : StartEv} (hA : O.adm mctx cctx)
    (T : RefLawsATeleX O.quiet O.adm mref cref) (hmiss : MissEX O E) (D : Nat) :
    ∀ (tenv : Lean.Environment) e hint top named, KeepsCP mctx mref cctx cref (JQHX O E (D + 1))
      (translateExprToWire tenv e hint top named) :=
  fun tenv e hint top named =>
    translate_keepsH_of_teleX O T (D + 1)
      (childKeepsH_all_of_teleX O T hmiss (D + 1) (by omega)) tenv mctx cctx hA e hint top named

/-! ## the closing of the machine: its children are `RealChildEX` -/

/-- the children of a closing, each a `RealChildEX` of the call (or the origin-built module) -/
def ChildrenRealEX (O : RefLawsAOpsX MkRefd mref cref) (E : StartEv) (shape : MachineShape)
    (children : List Res) : Prop :=
  children.length = shape.insts.length ∧
  ∀ k (hk : k < shape.insts.length), ∃ y, children[k]? = some y ∧
    ((shape.instOrigins.getD k .ord).child? = some y ∨
      RealChildEX O E (shape.insts[k]).1 y)

def CallsPureEX (O : RefLawsAOpsX MkRefd mref cref) (E : StartEv) (declName : Name) (shape : MachineShape) : Prop :=
  ∀ {tenv : Lean.Environment}, ∀ (b : Bool) t d₀ t' children,
    MReturns (synthesizeMixedCertified
      (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b) declName
      shape.binders shape.body) (t, d₀) →
    Sparkle.IR.Machine.closeLets shape.layout.lets t = some t' →
    ChildrenRealEX O E shape children →
    (shape.instFields = [] →
      (Sparkle.IR.Machine.closeInsts (machNIn shape) shape.insts.length
        shape.layout.slots.length (t.inputs.map (·.name)) (shape.insts.map (·.2.1)) children
        (Sparkle.IR.Machine.closeMachine shape.layout t', d₀)).isSome = true) ∧
    (shape.instFields ≠ [] → MemChildren shape children →
      (Sparkle.IR.Machine.closeInstsG (machNIn shape) shape.insts.length
        shape.layout.slots.length (t.inputs.map (·.name)) (shape.insts.map (·.2.1))
        shape.instFields children
        (Sparkle.IR.Machine.closeMachine shape.layout t', d₀)).isSome = true)

/-- **The machine synthesis does not fall back, from a history world** (as `MachineClosesAtAX`, at `JQHX O E n`) -/
def MachineClosesAtHX (O : RefLawsAOpsX MkRefd mref cref) (E : StartEv) (mctx : Meta.Context)
    (cctx : Core.Context) (declName : Name) (shape : MachineShape) : Prop :=
  ∀ {tenv : Lean.Environment}, ∀ (b : Bool) (n : Nat) w r w', JQHX O E n w → 1 ≤ n →
    RunsTo (synthesizeMachineCertified
      (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b) declName shape)
      mctx mref cctx cref w r w' → r ≠ none

/-- **A run of the one-output closing from a `JQHX O E D` world, whatever it returns.** -/
theorem closeInstsM_runHX (O : RefLawsAOpsX MkRefd mref cref) {E : StartEv} (hB : BodyStepHX O E) (hmiss : MissEX O E)
    (hA : O.adm mctx cctx) {D : Nat} (hD : 1 ≤ D)
    {shape : MachineShape} {t m₀ : Sparkle.IR.AST.Module} {d₀ : Sparkle.IR.AST.Design}
    {r : Option (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)} {w w' : Void IO.RealWorld}
    (hw : JQHX O E D w)
    (hr : RunsTo (closeInstsM shape t m₀ d₀) mctx mref cctx cref w r w') :
    ∃ children, r = Sparkle.IR.Machine.closeInsts (machNIn shape) shape.insts.length
        shape.layout.slots.length (t.inputs.map (·.name)) (shape.insts.map (·.2.1))
        children (m₀, d₀) ∧
      ChildrenRealEX O E shape children ∧ JQHX O E D w' := by
  unfold closeInstsM at hr
  obtain ⟨synth?, w1, hget, hr⟩ := RunsTo.bind hr
  obtain ⟨hw1, rfl⟩ := triple_runsX (tripleH_synthReadX O hA D) hw hget
  dsimp only at hr
  obtain ⟨children, w2, hch, hr⟩ := RunsTo.bind hr
  obtain ⟨heq, rfl⟩ := RunsTo.pure_world hr
  obtain ⟨hlen, hk, hw2⟩ := Tools.ShippingChildInv.mapM_hoare _ (JQHX O E D)
    (fun (x : Name × List Nat × MixedGateBinder) y => RealChildEX O E x.1 y)
    (fun x w y w' hp hy => synthesizeChild_realH'X O hA hD hmiss (hbodyH_of_stepX O hB hmiss hA D x.1) hp hy)
    shape.insts children hw1 hch
  exact ⟨children, heq, ⟨hlen, fun k hk' => by
    obtain ⟨y, hy, hre⟩ := hk k hk'
    exact ⟨y, hy, Or.inr hre⟩⟩, hw2⟩

/-- **A run of the general closing from a `JQHX O E D` world, whatever it returns.** -/
theorem closeInstsGM_runHX (O : RefLawsAOpsX MkRefd mref cref) {E : StartEv} (hB : BodyStepHX O E) (hmiss : MissEX O E)
    (hA : O.adm mctx cctx) {D : Nat} (hD : 1 ≤ D)
    {shape : MachineShape} {t m₀ : Sparkle.IR.AST.Module} {d₀ : Sparkle.IR.AST.Design}
    {r : Option (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)} {w w' : Void IO.RealWorld}
    (hw : JQHX O E D w)
    (hr : RunsTo (closeInstsGM shape t m₀ d₀) mctx mref cctx cref w r w') :
    ∃ children, r = Sparkle.IR.Machine.closeInstsG (machNIn shape) shape.insts.length
        shape.layout.slots.length (t.inputs.map (·.name)) (shape.insts.map (·.2.1))
        shape.instFields children (m₀, d₀) ∧ MemChildren shape children ∧
      ChildrenRealEX O E shape children ∧ JQHX O E D w' := by
  unfold closeInstsGM at hr
  obtain ⟨synth?, w1, hget, hr⟩ := RunsTo.bind hr
  obtain ⟨hw1, rfl⟩ := triple_runsX (tripleH_synthReadX O hA D) hw hget
  dsimp only at hr
  obtain ⟨children, w2, hch, hr⟩ := RunsTo.bind hr
  obtain ⟨heq, rfl⟩ := RunsTo.pure_world hr
  obtain ⟨hlen, hk, hw2⟩ := Tools.ShippingChildInv.mapM_hoare _ (JQHX O E D)
    (fun (x : Name × Sparkle.Compiler.MachInstOrigin.InstOrigin) y =>
      (∀ md, x.2.child? = some md → y = md) ∧
      (x.2.child? = some y ∨ RealChildEX O E x.1 y))
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
        obtain ⟨hrc, hp'⟩ := synthesizeChild_realH'X O hA hD hmiss (hbodyH_of_stepX O hB hmiss hA D c) hp hy
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


/-- **`MachineClosesAtAX` from `LetsClose` and `CallsPureA`** (ported from `machineClosesAt_of_pure`,
without `RefLaws`). Premises: `BodyStepHX O E`, `htr` (restricted translator keeps `JQHX O E n`). -/
theorem machineClosesAtH_of_pureX (O : RefLawsAOpsX MkRefd mref cref) {E : StartEv} (hB : BodyStepHX O E) (hmiss : MissEX O E)
    (hA : O.adm mctx cctx) {declName : Name} {shape : MachineShape}
    (htr : ∀ (tenv : Lean.Environment) (D : Nat) e hint top named,
      KeepsCP mctx mref cctx cref (JQHX O E (D + 1)) (translateExprToWire tenv e hint top named))
    (hl : LetsClose mctx mref cctx cref declName shape)
    (hp : CallsPureEX O E declName shape) :
    MachineClosesAtHX (mref := mref) (cref := cref) O E mctx cctx declName shape := by
  intro tenv b n w r w' hw hn hr
  obtain ⟨D, rfl⟩ : ∃ D, n = D + 1 := ⟨n - 1, by omega⟩
  unfold synthesizeMachineCertified at hr
  obtain ⟨⟨t, d'⟩, w1, run, hr⟩ := RunsTo.bind hr
  have hw1 := triple_runsX (keeps_iff.mp (mixed_keepsAPX O hA (stableA_JQHX O E (D + 1)) _ b declName
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
      obtain ⟨children, rfl, hreal, _⟩ := closeInstsM_runHX O hB hmiss hA (Nat.succ_le_succ (Nat.zero_le D)) hw1 hr
      have := (hp b t d' t' children run.mreturns ht' hreal).1 (List.isEmpty_iff.mp hf)
      intro h
      rw [h] at this
      cases this
    · rename_i hf
      obtain ⟨children, rfl, hmem, hreal, _⟩ := closeInstsGM_runHX O hB hmiss hA (Nat.succ_le_succ (Nat.zero_le D)) hw1 hr
      have := (hp b t d' t' children run.mreturns ht' hreal).2
        (fun h => hf (List.isEmpty_iff.mpr h)) hmem
      intro h
      rw [h] at this
      cases this


set_option maxHeartbeats 1000000 in
/-- **`CallsPureEX` for one-output calls of gate children with pairwise distinct callees.** -/
theorem callsPureE_of_gateKidsX (O : RefLawsAOpsX MkRefd mref cref) {E : StartEv} {declName : Name}
    (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hS : d.gateCallsOk nDecl = true)
    (nk : Nat → Nat)
    (hnomemO : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true)
    (hkid : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChildEX O E (d.shape.insts[k]).1 y → ChildIface (d.shape.insts[k]).1 (nk k) y.1 y.2)
    (hargsN : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      nk k = (d.shape.insts[k]).2.1.length)
    (hsep : ∀ c ∈ d.shape.insts.map (·.1), ∀ c' ∈ d.shape.insts.map (·.1),
      (Sparkle.IR.ModuleName.ofDecl c) = (Sparkle.IR.ModuleName.ofDecl c') → c = c')
    (hnodup : (d.shape.insts.map (·.1)).Nodup)
    (hparent : ∀ c ∈ d.shape.insts, (Sparkle.IR.ModuleName.ofDecl c.1) ≠ (Sparkle.IR.ModuleName.ofDecl declName))
    (hfresh : ∀ (k : Nat) (hk : k < d.shape.insts.length), ∀ o ∈ d.shape.layout.outs,
      o.name ≠ s!"inst{k}_{(Sparkle.IR.ModuleName.ofDecl (d.shape.insts[k]).1)}") :
    CallsPureEX O E declName d.shape := by
  have hf : d.shape.instFields = [] := by
    simp only [MachineData.gateCallsOk, Bool.and_eq_true, List.isEmpty_iff] at hS
    exact hS.2
  intro tenv b t d₀ t' children run hcl hreal
  refine ⟨fun _ => ?_, fun hne => absurd hf hne⟩
  obtain ⟨hlenC, hall⟩ := hreal
  have hfull : ∀ (k : Nat) (c : Res), children[k]? = some c → ∃ hk : k < d.shape.insts.length,
      ChildIface (d.shape.insts[k]).1 (nk k) c.1 c.2 := by
    intro k c hc
    have hk : k < d.shape.insts.length := by
      rw [← hlenC]
      exact (List.getElem?_eq_some_iff.mp hc).1
    obtain ⟨y, hy, hor⟩ := hall k hk
    rw [hc] at hy
    cases hy
    rcases hor with hmem | hre
    · rw [Tools.ShippingChildInv.notag_at hnomemO hk] at hmem
      cases hmem
    · exact ⟨hk, hkid k hk c hre⟩
  refine closeInsts_of_run d ok hbody hS run hcl hlenC ?_ ?_ ?_
  · intro k c hc
    obtain ⟨hk, full⟩ := hfull k c hc
    obtain ⟨fcomb, flen, fname, fdes⟩ := full
    refine ⟨fcomb, fdes, ?_, ?_⟩
    · intro args hargs
      obtain ⟨x, hx, rfl⟩ := inst_get hargs
      have hx' : d.shape.insts[k] = x := by
        have := List.getElem?_eq_getElem hk
        rw [hx] at this
        exact (Option.some.inj this).symm
      rw [flen, hargsN k hk, hx']
    · rw [fname]
      exact hparent _ (List.getElem_mem hk)
  · intro a ha c hc' hn
    obtain ⟨i, hi, hai⟩ := List.getElem_of_mem ha
    obtain ⟨j, hj, hcj⟩ := List.getElem_of_mem hc'
    obtain ⟨hki, fi⟩ := hfull i a (by rw [List.getElem?_eq_getElem hi, hai])
    obtain ⟨hkj, fj⟩ := hfull j c (by rw [List.getElem?_eq_getElem hj, hcj])
    rw [fi.2.2.1, fj.2.2.1] at hn
    have hni : (d.shape.insts.map (·.1))[i]? = some (d.shape.insts[i]).1 := by simp [hki]
    have hnj : (d.shape.insts.map (·.1))[j]? = some (d.shape.insts[j]).1 := by simp [hkj]
    have hcc := hsep _ (List.mem_of_getElem? hni) _ (List.mem_of_getElem? hnj) hn
    have hij : i = j := by
      refine Classical.byContradiction fun hne => ?_
      have hlen' : (d.shape.insts.map (·.1)).length = d.shape.insts.length := by simp
      have hpw := List.pairwise_iff_getElem.mp hnodup
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · exact hpw i j (by omega) (by omega) h (by simpa [hki, hkj] using hcc)
      · exact hpw j i (by omega) (by omega) h (by simpa [hki, hkj] using hcc.symm)
    subst hij
    rw [← hai, ← hcj]
  · intro k c hc o ho
    obtain ⟨hk, full⟩ := hfull k c hc
    rw [full.2.2.1]
    exact hfresh k hk o ho


theorem machineClosesAtH_of_teleX (O : RefLawsAOpsX MkRefd mref cref) {E : StartEv}
    (T : RefLawsATeleX O.quiet O.adm mref cref) (hmiss : MissEX O E) (hA : O.adm mctx cctx)
    {declName : Name} {shape : MachineShape}
    (hl : LetsClose mctx mref cctx cref declName shape)
    (hp : CallsPureEX O E declName shape) :
    MachineClosesAtHX (mref := mref) (cref := cref) O E mctx cctx declName shape :=
  machineClosesAtH_of_pureX O (bodyStepH_of_teleX O T) hmiss hA
    (fun tenv D => htrH_of_teleX O hA T hmiss D tenv) hl hp

/-- **`MachineClosesAtHX` for one-output calls of gate children with distinct callees**: the children are the history's `RealChildEX`s, so `hkid` is asked only of them -/
theorem machineClosesAtH_of_gateKidsX (O : RefLawsAOpsX MkRefd mref cref) {E : StartEv}
    (T : RefLawsATeleX O.quiet O.adm mref cref) (hmiss : MissEX O E) (hA : O.adm mctx cctx) {declName : Name}
    (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (halias : d.letsAliasOk = true)
    {nDecl : Nat} (hS : d.gateCallsOk nDecl = true)
    (nk : Nat → Nat)
    (hnomemO : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true)
    (hkid : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChildEX O E (d.shape.insts[k]).1 y → ChildIface (d.shape.insts[k]).1 (nk k) y.1 y.2)
    (hargsN : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      nk k = (d.shape.insts[k]).2.1.length)
    (hsep : ∀ c ∈ d.shape.insts.map (·.1), ∀ c' ∈ d.shape.insts.map (·.1),
      (Sparkle.IR.ModuleName.ofDecl c) = (Sparkle.IR.ModuleName.ofDecl c') → c = c')
    (hnodup : (d.shape.insts.map (·.1)).Nodup)
    (hparent : ∀ c ∈ d.shape.insts, (Sparkle.IR.ModuleName.ofDecl c.1) ≠ (Sparkle.IR.ModuleName.ofDecl declName))
    (hfresh : ∀ (k : Nat) (hk : k < d.shape.insts.length), ∀ o ∈ d.shape.layout.outs,
      o.name ≠ s!"inst{k}_{(Sparkle.IR.ModuleName.ofDecl (d.shape.insts[k]).1)}") :
    MachineClosesAtHX (mref := mref) (cref := cref) O E mctx cctx declName d.shape :=
  machineClosesAtH_of_teleX O T hmiss hA
    (letsClose_of_data d ok hbody halias mctx mref cctx cref)
    (callsPureE_of_gateKidsX O d ok hbody hS nk hnomemO hkid hargsN hsep hnodup hparent hfresh)

end Tools.ShippingFGCircuitS2hHist

#print axioms Tools.ShippingFGCircuitS2hHist.childKeepsH_all_of_teleX
#print axioms Tools.ShippingFGCircuitS2hHist.machineClosesAtH_of_gateKidsX
