import Tools.ShippingGen4FKidsLegacyTail
import Tools.ShippingGen4FKidsDepthInduct
import Tools.ShippingGen4FKidsLegacyArm
import Tools.ShippingGen4ParamEntry
import Tools.ShippingGen4KWalkDepthTop
import Tools.ShippingGen4FKidsEntryCore
import Tools.ShippingGen4FKidsDepthTop
-- (FKIDS_FREEZE §7.6): `addParameter` writes `module`, not `design`, so `StatePF` is all the walk keeps.
namespace Tools.ShippingGen4FKidsParams
open Tools.ShippingGen4FKidsDepthTop
open Lean Meta
open Tools.ShippingEntrySoundness
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv
open Tools.ShippingChildBndInit
open Tools.ShippingChildBndCore
open Tools.ShippingChildInvA
open Tools.ShippingChildFresh
open Tools.ShippingChildVCA
open Tools.ShippingChildTranslateA
open Tools.Assume.MemoFamily
open Tools.ShippingGen4KWalk
open Tools.ShippingGen4KWalkPrims
open Tools.ShippingGen4FKidsPrims
open Tools.ShippingGen4FKids
open Tools.ShippingGen4FKidsCalc
open Tools.ShippingGen4FKidsTac
open Tools.ShippingGen4FKidsEntry
open Tools.ShippingGen4FKidsHelpers
open Tools.ShippingGen4FKidsLegacyTail
open Tools.ShippingGen4FKidsProjField
open Tools.ShippingGen4KWalkDepth
open Tools.ShippingGen4FKidsDepth
open Tools.ShippingGen4FKidsTranslate
open Tools.ShippingGen4FKidsLegacyArm
open Tools.ShippingGen4FKidsEntryArms
open Tools.ShippingGen4ParamEntry
open Tools.ShippingGen4KWalkDiag
open Tools.ShippingGen4KWalkDepthTop
open Tools.ShippingGen4FKidsDepthEntry
open Tools.ShippingGen4KWalkEntry
open Tools.ShippingGen4KWalkEntryCore
open Tools.ShippingChildInv
open Sparkle.IR.Builder (CircuitState)

-- F-kids obligations (2)(3): the state invariant PQ on `module.parameters` (Nodup names, names bound by θ) through the whole symbolic top walk.
-- fkids7 route: GoodS now carries `parameters` EQUAL, so every leaf (emitLeaves, translator) keeps PQ for free; only `addParameter` is walked by hand.
-- No new premise, no axiom, no sorry.
variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- the parameter-list invariant: the names are distinct, and each is the name of a retained parameter in θ -/
def PQ (θ : List (String × Nat)) (ps : List Sparkle.IR.AST.Parameter) : Prop :=
  (ps.map (·.name)).Nodup ∧ ∀ p ∈ ps, p.name ∈ θ.map Prod.fst

theorem pq_nil (θ : List (String × Nat)) : PQ θ [] := ⟨List.nodup_nil, fun _ h => by simp at h⟩

theorem pq_reverse {θ : List (String × Nat)} {ps : List Sparkle.IR.AST.Parameter} (h : PQ θ ps) : PQ θ ps.reverse :=
  ⟨by rw [List.map_reverse]; exact List.pairwise_reverse.mpr (h.1.imp fun h => Ne.symm h), fun p hp => h.2 p (List.mem_reverse.mp hp)⟩

section KPDefs
variable (mctx mref cctx cref)

/-- the walk statement with the parameter invariant: from a `StatePF` state with `PQ θ` parameters, a returning run ends in such a state -/
def KP {α : Type} (θ : List (String × Nat)) (I : Void IO.RealWorld → Prop) (c : CompilerM α) : Prop :=
  ∀ (ctx : CompilerState), CtxOk ctx → ∀ st : CircuitState, StatePF st → PQ θ st.module.parameters →
    Triple mctx mref cctx cref I (c ctx st) (fun p w => I w ∧ StatePF p.2 ∧ PQ θ p.2.module.parameters)
      (fun e w => I w ∧ OkExc e)

end KPDefs

section KPRules
variable {I : Void IO.RealWorld → Prop} {θ : List (String × Nat)}

theorem KP.of_keeps {α : Type} {c : CompilerM α} (h : KeepsCS mctx mref cctx cref I c) : KP mctx mref cctx cref θ I c :=
  fun ctx hc st hs hq => Triple.conseq (h st ctx hc hs) (fun _ h => h)
    (fun p _ h => ⟨h.1, h.2.2.1, by rw [← h.2.2.2]; exact hq⟩) (fun _ _ h => h)

theorem KP.bind {α β : Type} {c : CompilerM α} {f : α → CompilerM β}
    (h1 : KeepsCS mctx mref cctx cref I c) (h2 : ∀ a, KP mctx mref cctx cref θ I (f a)) :
    KP mctx mref cctx cref θ I (c >>= f) := by
  intro ctx hc st hs hq
  refine Triple.bind (h1 st ctx hc hs) (fun p => ?_)
  obtain ⟨a, s⟩ := p
  intro w hw
  have hq' : PQ θ s.module.parameters := by rw [← hw.2.2.2]; exact hq
  exact (Triple.conseq (P' := fun w => I w ∧ StatePF s ∧ PQ θ s.module.parameters)
    (h2 a ctx hc s hw.2.2.1 hq') (fun w hw => hw.1)
    (fun p w hq => hq) (fun e w h => h)) w ⟨hw.1, hw.2.2.1, hq'⟩

theorem KP.bindKP {α β : Type} {c : CompilerM α} {f : α → CompilerM β}
    (h1 : KP mctx mref cctx cref θ I c) (h2 : ∀ a, KP mctx mref cctx cref θ I (f a)) :
    KP mctx mref cctx cref θ I (c >>= f) := by
  intro ctx hc st hs hq
  refine Triple.bind (h1 ctx hc st hs hq) (fun p => ?_)
  obtain ⟨a, s⟩ := p
  intro w hw
  exact (Triple.conseq (P' := fun w => I w ∧ StatePF s ∧ PQ θ s.module.parameters)
    (h2 a ctx hc s hw.2.1 hw.2.2) (fun w hw => hw.1)
    (fun p w hq => hq) (fun e w h => h)) w hw

theorem KP.bindNoRet {α β : Type} {c : CompilerM α} {f : α → CompilerM β}
    (h1 : ∀ st, NoRetS mctx mref cctx cref I st c) :
    KP mctx mref cctx cref θ I (c >>= f) := by
  intro ctx hc st hs hq
  refine Triple.bind (Q := fun _ _ => False) (h1 st ctx hc hs) (fun p w hf => hf.elim)

theorem KP.bindGet {β : Type} {f : CircuitState → CompilerM β}
    (h : ∀ st, StatePF st → PQ θ st.module.parameters → KP mctx mref cctx cref θ I (f st)) :
    KP mctx mref cctx cref θ I ((MonadState.get : CompilerM CircuitState) >>= f) :=
  fun ctx hc st hs hq => h st hs hq ctx hc st hs hq

theorem KP.set (s : CircuitState) (hs : StatePF s) (hq : PQ θ s.module.parameters) :
    KP mctx mref cctx cref θ I (set s : CompilerM PUnit) :=
  fun _ _ _ _ _ => Triple.pure (a := (PUnit.unit, s)) fun _ hw => ⟨hw, hs, hq⟩

theorem KP.ite {α : Type} {c : Prop} [Decidable c] {a b : CompilerM α}
    (ha : c → KP mctx mref cctx cref θ I a) (hb : ¬c → KP mctx mref cctx cref θ I b) :
    KP mctx mref cctx cref θ I (if c then a else b) := by
  by_cases hc : c
  · rw [if_pos hc]; exact ha hc
  · rw [if_neg hc]; exact hb hc

theorem KP.bindCtx {β : Type} {f : CompilerState → CompilerM β}
    (h : ∀ cs, CtxOk cs → KP mctx mref cctx cref θ I (f cs)) :
    KP mctx mref cctx cref θ I (CompilerM.getCompilerState >>= f) :=
  fun ctx hc st hs hq => h ctx hc ctx hc st hs hq

theorem KP.withReader {α : Type} {k : CompilerM α} (f : CompilerState → CompilerState)
    (hf : ∀ ctx, CtxOk ctx → CtxOk (f ctx)) (h : KP mctx mref cctx cref θ I k) :
    KP mctx mref cctx cref θ I (withReader f k) :=
  fun ctx hc st hs hq => h (f ctx) (hf ctx hc) st hs hq

end KPRules

section Walk
variable {O : RefLawsAOps MkRefd mref cref} (M : MemoFamily O) (hpp : PpMvKS O) {I : Void IO.RealWorld → Prop}
  (hS : StableK O.quiet I) {θ : List (String × Nat)}
include M hpp hS

theorem withVarMappingKP {α : Type} (fv : FVarId) (wn : String) {k : CompilerM α}
    (hk : KP mctx mref cctx cref θ I k) : KP mctx mref cctx cref θ I (CompilerM.withVarMapping fv wn k) := by
  unfold CompilerM.withVarMapping
  refine KP.bindCtx (fun old hold => ?_)
  refine KP.withReader _ ?_ hk
  intro _ _ r h
  exact hold r h

theorem withDimVarMappingKP {α : Type} (fv : FVarId) (d : Sparkle.IR.Type.DimExpr) {k : CompilerM α}
    (hk : KP mctx mref cctx cref θ I k) : KP mctx mref cctx cref θ I (CompilerM.withDimVarMapping fv d k) := by
  unfold CompilerM.withDimVarMapping
  refine KP.bindCtx (fun old hold => ?_)
  refine KP.withReader _ ?_ hk
  intro _ _ r h
  exact hold r h

theorem bindInputPortKP (hA : AdmCtx O.quiet mctx cctx) {α : Type} (fv : FVarId) (bn : String)
    (ty : Sparkle.IR.Type.HWType) (k : CompilerM α) (hk : KP mctx mref cctx cref θ I k) :
    KP mctx mref cctx cref θ I (bindInputPort fv bn ty k) := by
  unfold bindInputPort
  refine KP.bind (makeWirePS M hA hS _ _ _) (fun _ => ?_)
  refine KP.bind (addInputPS M hA hS _ _) (fun _ => ?_)
  exact withVarMappingKP M hpp hS _ _ hk

/-- `addParameter` of a name in θ: a duplicate is refused, so the new list is still `PQ θ`. -/
theorem addParameterKP (hA : AdmCtx O.quiet mctx cctx) (name : String) (d : Nat) (hn : name ∈ θ.map Prod.fst) :
    KP mctx mref cctx cref θ I (CompilerM.addParameter name d) := by
  unfold CompilerM.addParameter
  refine KP.bindGet (fun st hst hq => ?_)
  by_cases hc : (st.module.parameters.any (fun parameter => parameter.name == name)) = true
  · simp only [hc, if_true]
    exact KP.bindNoRet (fun st' => NoRetS.liftThrowError _ (keepsK_throwErrorS M hA hS _ (by okmsg)))
  · simp only [hc]
    have hnot : name ∉ st.module.parameters.map (·.name) := by
      intro hm
      apply hc
      rw [List.any_eq_true]
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hm
      exact ⟨p, hp, by simp⟩
    refine KP.set _ hst ?_
    show PQ θ ({ name := name, defaultValue := d } :: st.module.parameters)
    refine ⟨List.nodup_cons.mpr ⟨hnot, hq.1⟩, ?_⟩
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact hn
    · exact hq.2 p hp

/-- **The symbolic binder walk with the parameter invariant**: from a `StatePF` state with `PQ θ` parameters, a returning
`bindInputsLegacy θ …` ends in one, provided its continuation does. `addParameter` is reached only for a binder whose name is in θ. -/
theorem bindInputsLegacyKP (hA : AdmCtx O.quiet mctx cctx) (symbolicMode : Bool) (xs : Array Lean.Expr) (k : CompilerM String)
    (hk : KP mctx mref cctx cref θ I k) (i : Nat) :
    KP mctx mref cctx cref θ I (bindInputsLegacy θ symbolicMode xs i k) := by
  by_cases h : i < xs.size
  · have ih := bindInputsLegacyKP hA symbolicMode xs k hk (i + 1)
    unfold bindInputsLegacy
    rw [dif_pos h]
    refine KP.bind (KeepsCS.lift (keepsK_getDeclS M hpp hS hA _)) (fun decl => ?_)
    dsimp only
    split
    · rename_i dv hfind
      obtain ⟨pr, hpr, -⟩ := Option.map_eq_some_iff.mp hfind
      have hn : decl.userName.toString ∈ θ.map Prod.fst := by
        have h1 := List.find?_some hpr
        have h2 := List.mem_of_find?_eq_some hpr
        have h3 : pr.1 = decl.userName.toString := by simpa using h1
        exact List.mem_map.mpr ⟨pr, h2, h3⟩
      refine KP.bindKP (addParameterKP M hpp hS hA _ _ hn) (fun _ => ?_)
      exact withDimVarMappingKP M hpp hS _ _ ih
    · refine KP.bind (isSignalBinderTypeKS M hpp hS hA _) (fun isSignalArg => ?_)
      refine KP.ite (fun _ => ?_) (fun _ => ?_)
      · refine KP.bind (inferHWTypeFromSignalKS M hpp hS hA _) (fun hw => ?_)
        exact bindInputPortKP M hpp hS hA _ _ _ _ ih
      · refine KP.bind (KeepsCS.tryCatch (KeepsCS.bind (inferHWTypeFromSignalKS M hpp hS hA _)
          (fun _ => KeepsCS.pure _)) (fun _ _ => KeepsCS.pure _)) (fun isHW => ?_)
        refine KP.ite (fun _ => ?_) (fun _ => ih)
        refine KP.bind (inferHWTypeFromSignalKS M hpp hS hA _) (fun hw => ?_)
        exact bindInputPortKP M hpp hS hA _ _ _ _ ih
  · unfold bindInputsLegacy
    rw [dif_neg h]
    exact hk
termination_by xs.size - i
decreasing_by omega

end Walk

end Tools.ShippingGen4FKidsParams

#print axioms Tools.ShippingGen4FKidsParams.bindInputsLegacyKP
