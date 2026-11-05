import Tools.ShippingGen4FKidsLegacyTail
import Tools.ShippingGen4FKidsDepthInduct
-- F-kids DepthTop, part 1: the design-only walk (`KD`) of the symbolic binder walk `bindInputsLegacy` with `θ ≠ []`
-- (FKIDS_FREEZE §7.6): `addParameter` writes `module`, not `design`, so `StatePF` is all the walk keeps.
-- Takes `MemoFamily` and `PpMvKS` as hypotheses only; adds NO premise, NO axiom. No `sorry`.
namespace Tools.ShippingGen4FKidsDepthTop
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
open Sparkle.IR.Builder (CircuitState)

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

section KDDefs
variable (mctx mref cctx cref)

/-- the design-only walk statement: from every `StatePF` state, a returning run ends in a `StatePF` state (the `module` may change) -/
def KD {α : Type} (I : Void IO.RealWorld → Prop) (c : CompilerM α) : Prop :=
  ∀ (ctx : CompilerState), CtxOk ctx → ∀ st : CircuitState, StatePF st →
    Triple mctx mref cctx cref I (c ctx st) (fun p w => I w ∧ StatePF p.2) (fun e w => I w ∧ OkExc e)

end KDDefs

section KDRules
variable {I : Void IO.RealWorld → Prop}

theorem KD.of_keeps {α : Type} {c : CompilerM α} (h : KeepsCS mctx mref cctx cref I c) : KD mctx mref cctx cref I c :=
  fun ctx hc st hs => Triple.conseq (h st ctx hc hs) (fun _ h => h) (fun _ _ h => ⟨h.1, h.2.design.2⟩) (fun _ _ h => h)

theorem KD.bind {α β : Type} {c : CompilerM α} {f : α → CompilerM β}
    (h1 : KeepsCS mctx mref cctx cref I c) (h2 : ∀ a, KD mctx mref cctx cref I (f a)) :
    KD mctx mref cctx cref I (c >>= f) := by
  intro ctx hc st hs
  refine Triple.bind (h1 st ctx hc hs) (fun p => ?_)
  obtain ⟨a, s⟩ := p
  intro w hw
  exact (Triple.conseq (P' := fun w => I w ∧ StatePF s) (h2 a ctx hc s hw.2.design.2) (fun w hw => hw.1)
    (fun p w hq => hq) (fun e w h => h)) w ⟨hw.1, hw.2.design.2⟩

theorem KD.bindKD {α β : Type} {c : CompilerM α} {f : α → CompilerM β}
    (h1 : KD mctx mref cctx cref I c) (h2 : ∀ a, KD mctx mref cctx cref I (f a)) :
    KD mctx mref cctx cref I (c >>= f) := by
  intro ctx hc st hs
  refine Triple.bind (h1 ctx hc st hs) (fun p => ?_)
  obtain ⟨a, s⟩ := p
  intro w hw
  exact (Triple.conseq (P' := fun w => I w ∧ StatePF s) (h2 a ctx hc s hw.2) (fun w hw => hw.1)
    (fun p w hq => hq) (fun e w h => h)) w hw

theorem KD.bindGet {β : Type} {f : CircuitState → CompilerM β}
    (h : ∀ st, StatePF st → KD mctx mref cctx cref I (f st)) :
    KD mctx mref cctx cref I ((MonadState.get : CompilerM CircuitState) >>= f) :=
  fun ctx hc st hs => h st hs ctx hc st hs

theorem KD.pure {α : Type} (a : α) : KD mctx mref cctx cref I (Pure.pure a : CompilerM α) :=
  fun _ _ st hs => Triple.pure (a := (a, st)) fun _ hw => ⟨hw, hs⟩

theorem KD.set (s : CircuitState) (hs : StatePF s) : KD mctx mref cctx cref I (set s : CompilerM PUnit) :=
  fun _ _ _ _ => Triple.pure (a := (PUnit.unit, s)) fun _ hw => ⟨hw, hs⟩

theorem KD.ite {α : Type} {c : Prop} [Decidable c] {a b : CompilerM α}
    (ha : c → KD mctx mref cctx cref I a) (hb : ¬c → KD mctx mref cctx cref I b) :
    KD mctx mref cctx cref I (if c then a else b) := by
  by_cases hc : c
  · rw [if_pos hc]; exact ha hc
  · rw [if_neg hc]; exact hb hc

theorem KD.bindCtx {β : Type} {f : CompilerState → CompilerM β}
    (h : ∀ cs, CtxOk cs → KD mctx mref cctx cref I (f cs)) :
    KD mctx mref cctx cref I (CompilerM.getCompilerState >>= f) :=
  fun ctx hc st hs => h ctx hc ctx hc st hs

theorem KD.withReader {α : Type} {k : CompilerM α} (f : CompilerState → CompilerState)
    (hf : ∀ ctx, CtxOk ctx → CtxOk (f ctx)) (h : KD mctx mref cctx cref I k) :
    KD mctx mref cctx cref I (withReader f k) :=
  fun ctx hc st hs => h (f ctx) (hf ctx hc) st hs

end KDRules

section Walk
variable {O : RefLawsAOps MkRefd mref cref} (M : MemoFamily O) (hpp : PpMvKS O) {I : Void IO.RealWorld → Prop}
  (hS : StableK O.quiet I)
include M hpp hS

theorem withVarMappingKD {α : Type} (fv : FVarId) (wn : String) {k : CompilerM α}
    (hk : KD mctx mref cctx cref I k) : KD mctx mref cctx cref I (CompilerM.withVarMapping fv wn k) := by
  unfold CompilerM.withVarMapping
  refine KD.bindCtx (fun old hold => ?_)
  refine KD.withReader _ ?_ hk
  intro _ _ r h
  exact hold r h

theorem withDimVarMappingKD {α : Type} (fv : FVarId) (d : Sparkle.IR.Type.DimExpr) {k : CompilerM α}
    (hk : KD mctx mref cctx cref I k) : KD mctx mref cctx cref I (CompilerM.withDimVarMapping fv d k) := by
  unfold CompilerM.withDimVarMapping
  refine KD.bindCtx (fun old hold => ?_)
  refine KD.withReader _ ?_ hk
  intro _ _ r h
  exact hold r h

theorem bindInputPortKD (hA : AdmCtx O.quiet mctx cctx) {α : Type} (fv : FVarId) (bn : String)
    (ty : Sparkle.IR.Type.HWType) (k : CompilerM α) (hk : KD mctx mref cctx cref I k) :
    KD mctx mref cctx cref I (bindInputPort fv bn ty k) := by
  unfold bindInputPort
  refine KD.bind (makeWirePS M hA hS _ _ _) (fun _ => ?_)
  refine KD.bind (addInputPS M hA hS _ _) (fun _ => ?_)
  exact withVarMappingKD M hpp hS _ _ hk

/-- `addParameter` keeps `design` (it writes `module`), so it keeps `StatePF`; a duplicate is refused. -/
theorem addParameterKD (hA : AdmCtx O.quiet mctx cctx) (name : String) (d : Nat) :
    KD mctx mref cctx cref I (CompilerM.addParameter name d) := by
  unfold CompilerM.addParameter
  refine KD.bindGet (fun st hst => ?_)
  have hset : KD mctx mref cctx cref I (set (Sparkle.IR.Builder.CircuitM.addParameter name d st).2 : CompilerM PUnit) :=
    KD.set _ hst
  by_cases hc : (st.module.parameters.any (fun parameter => parameter.name == name)) = true
  · simp only [hc, if_true]
    exact KD.bind (KeepsCS.lift (keepsK_throwErrorS M hA hS _ (by okmsg))) (fun _ => hset)
  · simp only [hc]
    exact hset

/-- **The symbolic binder walk, design only** (`θ` arbitrary, `symbolicMode` arbitrary): from every `StatePF` state a returning
`bindInputsLegacy` ends in a `StatePF` state, provided its continuation `k` does (obligation (2)'s second property of this walk,
`M.parameters ⊆ θ`, is NOT proved here: the leaves of the K walk only carry `GoodS`). -/
theorem bindInputsLegacyKD (hA : AdmCtx O.quiet mctx cctx) (parameters : List (String × Nat))
    (symbolicMode : Bool) (xs : Array Lean.Expr) (k : CompilerM String)
    (hk : KD mctx mref cctx cref I k) (i : Nat) :
    KD mctx mref cctx cref I (bindInputsLegacy parameters symbolicMode xs i k) := by
  by_cases h : i < xs.size
  · have ih := bindInputsLegacyKD hA parameters symbolicMode xs k hk (i + 1)
    unfold bindInputsLegacy
    rw [dif_pos h]
    refine KD.bind (KeepsCS.lift (keepsK_getDeclS M hpp hS hA _)) (fun decl => ?_)
    dsimp only
    split
    · refine KD.bindKD (addParameterKD M hpp hS hA _ _) (fun _ => ?_)
      exact withDimVarMappingKD M hpp hS _ _ ih
    · refine KD.bind (isSignalBinderTypeKS M hpp hS hA _) (fun isSignalArg => ?_)
      refine KD.ite (fun _ => ?_) (fun _ => ?_)
      · refine KD.bind (inferHWTypeFromSignalKS M hpp hS hA _) (fun hw => ?_)
        exact bindInputPortKD M hpp hS hA _ _ _ _ ih
      · refine KD.bind (KeepsCS.tryCatch (KeepsCS.bind (inferHWTypeFromSignalKS M hpp hS hA _)
          (fun _ => KeepsCS.pure _)) (fun _ _ => KeepsCS.pure _)) (fun isHW => ?_)
        refine KD.ite (fun _ => ?_) (fun _ => ih)
        refine KD.bind (inferHWTypeFromSignalKS M hpp hS hA _) (fun hw => ?_)
        exact bindInputPortKD M hpp hS hA _ _ _ _ ih
  · unfold bindInputsLegacy
    rw [dif_neg h]
    exact hk
termination_by xs.size - i
decreasing_by omega

end Walk

end Tools.ShippingGen4FKidsDepthTop
