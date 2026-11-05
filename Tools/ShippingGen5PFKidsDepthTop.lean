-- Gen5 port of Tools.ShippingGen4FKidsDepthTop (scripts/gen4/PARAM_ASSEMBLY.md §Gen5): copy for the gen5 Elab; only the marked parts differ.
import Tools.ShippingGen4FKidsLegacyTail
import Tools.ShippingGen5PFKidsDepthInduct
import Tools.ShippingGen5PFKidsLegacyArm
import Tools.ShippingGen5PParamEntry
import Tools.ShippingGen5PKWalkDepthTop
import Tools.ShippingGen5PFKidsEntryCore
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

section Sym
variable {O : RefLawsAOps MkRefd mref cref} (M : MemoFamily O) (hA : AdmCtx O.quiet mctx cctx)
include M hA

/-- `finishSynth` in symbolic mode of a `StatePF` state: the returned design is the state's design. -/
theorem finishSynthSym {I : Void IO.RealWorld → Prop} (hS : StableK O.quiet I) (declName : Name)
    (θ : List (String × Nat)) (st : CircuitState) (hst : StatePF st) :
    Triple mctx mref cctx cref I (finishSynth declName θ true st)
      (fun r w => I w ∧ DesignPF r.2) (fun e w => I w ∧ OkExc e) := by
  unfold finishSynth
  simp only [↓reduceIte]
  split
  · refine Triple.bind (R := fun e w => I w ∧ OkExc e) (Q := fun _ w => I w)
      (keeps_iff.mp (keepsK_throwErrorS M hA hS _ (by okmsg))) (fun _ => ?_)
    refine Triple.bind (R := fun e w => I w ∧ OkExc e) (Q := fun _ w => I w) (keeps_iff.mp ?_) (fun _ => ?_)
    · swalkN [keepsK_throwErrorS M hA hS _ _, Keeps.forIn_list]
    · exact Triple.ite (fun _ => Triple.pure fun _ hw => ⟨hw, hst⟩)
        (fun _ => Triple.throw _ fun _ hw => ⟨hw, by okmsg⟩)
  · refine Triple.bind (R := fun e w => I w ∧ OkExc e) (Q := fun _ w => I w) (keeps_iff.mp ?_) (fun _ => ?_)
    · swalkN [keepsK_throwErrorS M hA hS _ _, Keeps.forIn_list]
    · exact Triple.ite (fun _ => Triple.pure fun _ hw => ⟨hw, hst⟩)
        (fun _ => Triple.throw _ fun _ hw => ⟨hw, by okmsg⟩)

/-- **The legacy arm at the symbolic top** (`symbolicMode = true`, retained parameters `θ`): the entry constant goes through the legacy
tail (all three front ends are off), no memo is read or written, and the returned design is `StatePF`. -/
theorem legacySym_windowDP (hlog : LogMvKS O) (D : Nat)
    (translate : TranslateFn) (b : Bool) (declName : Name) (θ : List (String × Nat)) (constInfo : ConstantInfo)
    (isInst : Lean.Expr → Bool)
    (htr : RecKS O (WPF O D) translate) :
    Triple mctx mref cctx cref (WPF O D)
      (synthesizeFromConst translate (profLogIO b) declName θ true true constInfo isInst)
      (fun r w => WPF O D w ∧ DesignPF r.2) (fun e w => WPF O D w ∧ OkExc e) := by
  have hS := stableK_KWD O PPF D
  have hpp : PpMvKS O := ppMvK_of M
  first | delta synthesizeFromConst | unfold synthesizeFromConst
  simp only [↓reduceIte, certifiedShape_off, mixedCertifiedShape_off, Bool.true_or, Bool.not_true,
    Bool.and_false, Bool.false_and, Bool.false_eq_true]
  refine triple_pure_bind_ofS ?_
  dsimp only
  refine triple_pure_bind_ofS ?_
  dsimp only
  refine Triple.bind (keeps_iff.mp (keepsK_profLogS M hA hS hlog b _)) ?_
  intro _
  cases constInfo with
  | defnInfo di =>
    dsimp only
    refine Triple.bind (keeps_iff.mp (keepsK_profLogS M hA hS hlog b _)) ?_
    intro _
    refine Triple.bind (keeps_iff.mp (keepsK_framedNM M hA hS FramedNM.monoMs)) ?_
    intro t0
    refine Triple.bind (keeps_iff.mp (keepsK_profLogS M hA hS hlog b _)) ?_
    intro _
    refine Triple.bind (keeps_iff.mp (openRecordInputs_keepsKS M hS hA _)) ?_
    intro body0
    refine Triple.bind (keeps_iff.mp (keepsK_framedNM M hA hS FramedNM.monoMs)) ?_
    intro t1
    refine Triple.bind (keeps_iff.mp (keepsK_profLogS M hA hS hlog b _)) ?_
    intro _
    refine M.tele.lamTelescopeT (WPF O D) (fun (r : Sparkle.IR.AST.Module × Sparkle.IR.AST.Design) w => WPF O D w ∧ DesignPF r.2)
      (WPF O D) hA (fun _ h => h.1.1) (fun _ _ h => h.1.1.1) (fun _ h => h.1.1)
      (stableK_KWD O PPF D).2
      (fun _ w w' h1 h2 h3 h4 hq hw => ⟨(stableK_KWD O PPF D).2 w w' h1 h2 h3 h4 hq hw.1, hw.2⟩)
      (stableK_KWD O PPF D).2 _ _ _ ?_
    intro mctx' cctx' xs innerBody hA'
    refine Triple.bind (keeps_iff.mp (keepsK_profLogS M hA' hS hlog b _)) ?_
    intro _
    refine Triple.bind (keeps_iff.mp ?_) ?_
    · swalkN [keepsK_framedNM M hA' hS (FramedNM.whnf _), keepsK_getDeclS M hpp hS hA',
        keepsK_throwErrorS M hA' hS _ _, Keeps.forIn_list, Keeps.forIn_array]
    intro _
    refine Triple.bind (keeps_iff.mp (splitReturnLeaves_keepsKS M hS hA' _ _)) ?_
    intro leaves
    refine Triple.bind (keeps_iff.mp (keepsK_framedNM M hA' hS FramedNM.monoMs)) ?_
    intro t2
    refine Triple.bind (keeps_iff.mp (keepsK_profLogS M hA' hS hlog b _)) ?_
    intro _
    refine Triple.bindQ (φ := MkRefd _) (tripleK_mkExprCacheS M hA' hS _) ?_
    intro cacheRef hr
    have hi := init_ok (Sparkle.IR.ModuleName.ofDecl declName)
    refine Triple.bindQ (P' := WPF O D) (φ := fun p => StatePF p.2) ?hh ?_
    case hh =>
      exact (bindInputsLegacyKD M hpp hS hA' θ true xs _
        (KD.of_keeps (emitLeavesKPS M hA' hS hlog translate b cacheRef hr (htr mctx' cctx' hA') _ _ _)) 0) _
        (ctxOk_entry true hr) _ hi.1
    rintro ⟨_, fs⟩ hg
    refine Triple.bindQ (P' := WPF O D) (φ := fun r => DesignPF r.2)
      (finishSynthSym M hA' hS declName θ fs hg) ?_
    intro result hres
    exact Triple.pure fun _ hw => ⟨hw, hres⟩
  | _ =>
    dsimp only
    exact tripleK_throwErr M hA hS _ (by okmsg)

/-- The child-cache reset `set v` from a world with an empty memo: depth kept, the cache is `v`. -/
theorem triple_childResetDPF (D : Nat) (v : Std.HashMap Name Res) {R : Exception → Void IO.RealWorld → Prop} :
    Triple mctx mref cctx cref (KWD O (fun m _ => m = {}) D) (sparkleChildCache.set v : MetaM Unit)
      (fun _ => KWD O (fun m c => m = {} ∧ c = v) D) R :=
  Triple.of_runs (refSet_runs _ _) fun w u w' hw h => by
    have hk := O.cacheSet hA v w u w' h hw.1.1
    have hm := M.frameCacheSet hA v w u w' h hw.1.1
    refine ⟨⟨O.cacheSetQ hA v w u w' h hw.1.1, hk.2.1.trans hw.1.2.1, ?_⟩, by rw [hk.2.2]; exact hw.2⟩
    rw [hm]
    exact ⟨hw.1.2.2, hk.1⟩

theorem entryTopSym_windowD (hlog : LogMvK O) (translate : Lean.Environment → TranslateFn) (declName : Name)
    (θ : List (String × Nat))
    (hbody : 0 < sparkleSynthDepthLimit → ∀ (b : Bool) (env : Lean.Environment) (ci : ConstantInfo)
        (isInst : Lean.Expr → Bool),
      Triple mctx mref cctx cref (WPF O 1)
        (synthesizeFromConst (translate env) (profLogIO b) declName θ true true ci isInst)
        (fun r w => WPF O 1 w ∧ DesignPF r.2) (fun e w => WPF O 1 w ∧ OkExc e)) :
    Triple mctx mref cctx cref (KWD O (fun _ _ => True) 0)
      (synthesizeCombinationalCoreWith translate declName θ true true)
      (fun (r : (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)) _ => DesignPF r.2) (fun e w => KW O (fun _ _ => True) w ∧ OkExc e) := by
  unfold synthesizeCombinationalCoreWith
  simp only [↓reduceIte]
  refine Triple.ite (fun _ => ?_) (fun _ => ?_)
  · refine Triple.bind (Q := fun _ _ => False)
      (Triple.conseq (tripleK_throwErr M hA (stableK_KWD O (fun _ _ => True) 0) _
        (by first | exact .str _ | exact .fmt _)) (fun _ h => h) (fun _ _ h => h) (fun _ _ h => ⟨h.1.1, h.2⟩)) ?_
    intro _ w hf
    exact hf.elim
  · refine Triple.bind (R := fun e w => KW O (fun _ _ => True) w ∧ OkExc e) (Q := fun _ w => KWD O (fun _ _ => True) 0 w)
      (Triple.conseq (keeps_iff.mp ?_) (fun _ h => h) (fun _ _ h => h) (fun _ _ h => ⟨h.1.1, h.2⟩)) ?_
    · swalkN [keepsK_throwErrorS M hA (stableK_KWD O (fun _ _ => True) 0) _ _, Keeps.forIn_list]
    intro _
    refine Triple.bind (R := fun e w => KW O (fun _ _ => True) w ∧ OkExc e) (Q := fun _ w => KWD O (fun _ _ => True) 0 w)
      (Triple.conseq (keeps_iff.mp (keepsK_framedNM M hA (stableK_KWD O (fun _ _ => True) 0) (FramedNM.ioEnv _)))
        (fun _ h => h) (fun _ _ h => h) (fun _ _ h => ⟨h.1.1, h.2⟩)) ?_
    intro prof
    refine Triple.bind (R := fun e w => KW O (fun _ _ => True) w ∧ OkExc e) (Q := fun _ w => KWD O (fun _ _ => True) 0 w)
      (Triple.conseq (keeps_iff.mp (keepsK_profLog M hA (stableK_KWD O (fun _ _ => True) 0) hlog prof.isSome _))
        (fun _ h => h) (fun _ _ h => h) (fun _ _ h => ⟨h.1.1, h.2⟩)) ?_
    intro _
    refine Triple.bindQ (φ := fun d => d = 0) (tripleK_depthGetD M hA (fun _ _ => True) 0) ?_
    intro d hd
    subst hd
    refine Triple.ite (fun _ => ?_) (fun hc => ?_)
    · refine Triple.bind (Q := fun _ _ => False)
        (Triple.conseq (tripleK_throwErr M hA (stableK_KWD O (fun _ _ => True) 0) _
          (by first | exact .str _ | exact .fmt _)) (fun _ h => h) (fun _ _ h => h) (fun _ _ h => ⟨h.1.1, h.2⟩)) ?_
      intro _ w hf
      exact hf.elim
    · have hlt : 0 < sparkleSynthDepthLimit := Nat.not_le.mp hc
      have h0 : (0 == 0) = true := rfl
      simp only [h0, ↓reduceIte]
      kpureT (fun _ _ => True); kpureT (fun _ _ => True); kpureT (fun _ _ => True); kpureT (fun _ _ => True)
      kpureT (fun _ _ => True); kpureT (fun _ _ => True); kpureT (fun _ _ => True)
      ksetT (fun _ _ => True); ksetT (fun _ _ => True); ksetT (fun _ _ => True)
      refine Triple.bind (R := fun e w => KW O (fun _ _ => True) w ∧ OkExc e) (Triple.conseq (R := fun _ _ => False) (triple_memoResetD M hA (fun _ _ => True) 0)
        (fun _ h => h) (fun _ _ h => h) (fun _ _ h => h.elim)) ?_
      intro _
      refine Triple.bind (R := fun e w => KW O (fun _ _ => True) w ∧ OkExc e) (Triple.conseq
        (triple_childResetDPF M hA 0 _ (R := fun _ _ => False))
        (fun _ h => h) (fun _ _ h => h) (fun _ _ h => h.elim)) ?_
      intro _
      ksetT (fun m c => m = {} ∧ c = {}); ksetT (fun m c => m = {} ∧ c = {}); ksetT (fun m c => m = {} ∧ c = {})
      ksetT (fun m c => m = {} ∧ c = {}); ksetT (fun m c => m = {} ∧ c = {}); ksetT (fun m c => m = {} ∧ c = {})
      ksetT (fun m c => m = {} ∧ c = {})
      refine Triple.bind (R := fun e w => KW O (fun _ _ => True) w ∧ OkExc e)
        (Triple.conseq (R := fun _ _ => False) (triple_depthSetD M hA PPF 0 1)
          (fun (w : Void IO.RealWorld) (h : KWD O (fun m c => m = {} ∧ c = {}) 0 w) =>
            ⟨⟨h.1.1, h.1.2.1, by rw [h.1.2.2.1, h.1.2.2.2]; exact ⟨memoKeysInChild_empty _, cachePF_empty, cachePF_empty⟩⟩, h.2⟩)
          (fun _ _ h => h) (fun _ _ h => h.elim)) ?_
      intro _
      have body : ∀ (m1 : Std.HashMap Lean.Name Lean.Expr) (m2 : Std.HashMap String Nat)
          (m3 m4 m5 : Std.HashMap String String) (m6 : Std.HashMap (UInt64 × String) String)
          (m7 : Std.HashMap String String),
          Triple mctx mref cctx cref (WPF O 1)
            (_root_.tryFinally
              (do
                let constInfo ← getConstInfo declName
                let env ← getEnv
                synthesizeFromConst (translate env) (profLogIO prof.isSome) declName θ true true
                  (entryConst true true θ constInfo (instancePredicate env) (userInliner env)
                    (structEnv env))
                  (instancePredicate env))
              (do
                ST.Ref.modify sparkleSynthDepth fun x => x - 1
                if (0 != 0) = true then do
                    ST.Ref.set sparkleFvarValueMap m1
                    ST.Ref.set sparkleWireWidthCache m2
                    ST.Ref.set sparkleLetWireCache m3
                    ST.Ref.set sparkleLoopWireCache m4
                    ST.Ref.set sparkleWireCanon m5
                    ST.Ref.set sparkleSubInstanceOutputs m6
                    ST.Ref.set sparkleSingleOutInstanceCache m7
                  else pure () : MetaM Unit))
            (fun (r : (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)) _ => DesignPF r.2) (fun e w => KW O (fun _ _ => True) w ∧ OkExc e) := by
        intro m1 m2 m3 m4 m5 m6 m7
        refine Triple.conseq (R := fun e w => KWD O PPF 0 w ∧ OkExc e) ?_ (fun _ h => h) (fun _ _ h => h)
          (fun _ _ h => ⟨kw_weak h.1.1, h.2⟩)
        refine tryFinallySplit2Q (Q1 := fun (r : (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)) w => WPF O 1 w ∧ DesignPF r.2) (Q2 := fun (r : (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)) _ => DesignPF r.2)
          (Me := WPF O 1) (Me' := KWD O PPF 0) (E := OkExc) ?_
          (fun a => Triple.conseq (Tools.ShippingGen4FKidsEntryCore.triple_constConj (DesignPF a.2) (fin_totalD M hA PPF 0 m1 m2 m3 m4 m5 m6 m7))
            (fun _ h => h) (fun _ _ h => h.2) (fun _ _ h => h))
          (fin_totalD M hA PPF 0 m1 m2 m3 m4 m5 m6 m7)
        · refine Triple.bind (keeps_iff.mp (keepsK_framedNM M hA (stableK_KWD O PPF 1)
            (FramedNM.constInfo _))) ?_
          intro ci
          refine Triple.bind (keeps_iff.mp (keepsK_framedNM M hA (stableK_KWD O PPF 1)
            FramedNM.env)) ?_
          intro env
          exact hbody hlt prof.isSome env _ _
      exact body _ _ _ _ _ _ _

end Sym

end Tools.ShippingGen4FKidsDepthTop

#print axioms Tools.ShippingGen4FKidsDepthTop.bindInputsLegacyKD
#print axioms Tools.ShippingGen4FKidsDepthTop.finishSynthSym
#print axioms Tools.ShippingGen4FKidsDepthTop.legacySym_windowDP
#print axioms Tools.ShippingGen4FKidsDepthTop.entryTopSym_windowD
