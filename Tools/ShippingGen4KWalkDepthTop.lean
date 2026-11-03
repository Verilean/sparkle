import Tools.ShippingGen4KWalkDepthInduct
-- NOT BUILT: S6 (top entry) of scripts/gen4/KWALK_PLAN.md (frozen in scripts/gen4/KWALK_S6_TOP_FREEZE.md): the OUTERMOST entry (depth 0, with the resets) for `KWD`:
-- `entryTop_windowD` takes the body `hbody` at `KWD K 1` (as `synthesizeChild_depthK` at D = 1 gives it), and `topEntry_K` closes it with the hypotheses of the induction only (`LogMvK`, `LegacyImplK`, `LegacyArmD`).
-- Takes `MemoFamily` (TRUSTED, approved) as a HYPOTHESIS `M`; adds NO premise, NO law, NO axiom. No `sorry`, no `axiom`, no `native_decide`. Ledger delta: FG -0 +0 / T1 -0 +0.
namespace Tools.ShippingGen4KWalkDepthTop
open Lean Meta
open Tools.ShippingEntrySoundness
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv
open Tools.ShippingChildBndInit
open Tools.ShippingChildBndCore
open Tools.ShippingChildInvA
open Tools.ShippingChildFresh
open Tools.ShippingChildVCA
open Tools.Assume.MemoFamily
open Tools.ShippingGen4KWalk
open Tools.ShippingGen4KWalkPrims
open Tools.Assume.FramedACases
open Tools.ShippingGen4KWalkTranslate
open Tools.ShippingGen4KWalkFallback
open Tools.ShippingGen4KWalkLegacyCached
open Tools.ShippingGen4KWalkEntry
open Tools.ShippingGen4KWalkEntryCore
open Tools.ShippingGen4KWalkDepth
open Tools.ShippingGen4KWalkDepthEntry
open Tools.ShippingGen4KWalkDepthInduct

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option hygiene false in
macro "ksetT " P:term : tactic => `(tactic|
  (refine Triple.bind (R := fun e w => KW O (fun _ _ => True) w ∧ OkExc e) (Triple.conseq
      (keeps_iff.mp (keepsK_framedNM M hA (stableK_KWD O $P 0) (FramedNM.sideSet _ ?s)))
      (fun _ h => h) (fun _ _ h => h) (fun _ _ h => ⟨kw_weak h.1.1, h.2⟩)) ?_
   case s => constructor
   intro _))
set_option hygiene false in
macro "kpureT " P:term : tactic => `(tactic|
  (refine Triple.bind (Triple.pure (Q := fun _ w => KWD O $P 0 w) (fun w hw => hw)) ?_; intro _))

section Top
variable {O : RefLawsAOps MkRefd mref cref} (M : MemoFamily O) (hA : AdmCtx O.quiet mctx cctx)
include M hA

/-- The memo reset `set {}` keeps the depth: `KWD P 0` to `KWD (memo empty) 0` (the small lemma that carries `dv = 0` through the part before the reset). -/
theorem triple_memoResetD (P : Std.HashMap Name Res → Std.HashMap Name Res → Prop) (D : Nat)
    {R : Exception → Void IO.RealWorld → Prop} :
    Triple mctx mref cctx cref (KWD O P D) (sparkleSubModuleCache.set {} : MetaM Unit)
      (fun _ => KWD O (fun m _ => m = {}) D) R :=
  Triple.of_runs (refSet_runs _ _) fun w u w' hw h => by
    obtain ⟨hq, hc, hs, hm⟩ := memoSet_ctx M hA {} h hw.1.1
    have hf := O.frame hA _ (framedA_of_memoAccess (MemoAccess.set {})) w hw.1.1
    rw [endW_of_runs h] at hf
    exact ⟨⟨hq, hs.trans hw.1.2.1, hm⟩, by rw [hf.2.2]; exact hw.2⟩

/-- The child-cache reset `set v` keeps the depth and a predicate that does not look at the child cache. -/
theorem triple_childResetD (P : Std.HashMap Name Res → Std.HashMap Name Res → Prop)
    (hP : ∀ m c c', P m c → P m c') (D : Nat) (v : Std.HashMap Name Res) {R : Exception → Void IO.RealWorld → Prop} :
    Triple mctx mref cctx cref (KWD O P D) (sparkleChildCache.set v : MetaM Unit) (fun _ => KWD O P D) R :=
  Triple.of_runs (refSet_runs _ _) fun w u w' hw h => by
    have hk := O.cacheSet hA v w u w' h hw.1.1
    have hm := M.frameCacheSet hA v w u w' h hw.1.1
    refine ⟨⟨O.cacheSetQ hA v w u w' h hw.1.1, hk.2.1.trans hw.1.2.1, ?_⟩, by rw [hk.2.2]; exact hw.2⟩
    rw [hm]
    exact hP _ _ _ hw.1.2.2

/-- **The entry for an outermost run** (`depth = 0`), the body at `KWD K 1`: the resets empty the memo, the rest is `entryNested_windowD` at `D = 0`.
Success: K_declName (and depth 0 again). Failure: only quietness and the synthesis ref. -/
theorem entryTop_windowD (hlog : LogMvK O) (translate : Lean.Environment → TranslateFn) (declName : Name)
    (hbody : 0 < sparkleSynthDepthLimit → ∀ (b : Bool) (env : Lean.Environment) (ci : ConstantInfo)
        (isInst : Lean.Expr → Bool),
      Triple mctx mref cctx cref (KWD O MemoKeysInChild 1)
        (synthesizeFromConst (translate env) (profLogIO b) declName [] false true ci isInst)
        (fun _ => KWD O (MemoKeysExc declName) 1) (fun e w => KWD O MemoKeysInChild 1 w ∧ OkExc e)) :
    Triple mctx mref cctx cref (KWD O (fun _ _ => True) 0)
      (synthesizeCombinationalCoreWith translate declName [] false true)
      (fun _ => KWD O (MemoKeysExc declName) 0) (fun e w => KW O (fun _ _ => True) w ∧ OkExc e) := by
  unfold synthesizeCombinationalCoreWith
  simp only [Bool.false_eq_true, ↓reduceIte]
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
      (triple_childResetD M hA (fun m _ => m = {}) (fun _ _ _ h => h) 0 _ (R := fun _ _ => False))
      (fun _ h => h) (fun _ _ h => h) (fun _ _ h => h.elim)) ?_
    intro _
    ksetT (fun m _ => m = {}); ksetT (fun m _ => m = {}); ksetT (fun m _ => m = {}); ksetT (fun m _ => m = {})
    ksetT (fun m _ => m = {}); ksetT (fun m _ => m = {}); ksetT (fun m _ => m = {})
    refine Triple.bind (R := fun e w => KW O (fun _ _ => True) w ∧ OkExc e)
      (Triple.conseq (R := fun _ _ => False) (triple_depthSetD M hA MemoKeysInChild 0 1)
        (fun (w : Void IO.RealWorld) (h : KWD O (fun m _ => m = {}) 0 w) =>
          ⟨⟨h.1.1, h.1.2.1, by rw [h.1.2.2]; exact memoKeysInChild_empty _⟩, h.2⟩) (fun _ _ h => h)
        (fun _ _ h => h.elim)) ?_
    intro _
    have body : ∀ (m1 : Std.HashMap Lean.Name Lean.Expr) (m2 : Std.HashMap String Nat)
        (m3 m4 m5 : Std.HashMap String String) (m6 : Std.HashMap (UInt64 × String) String)
        (m7 : Std.HashMap String String),
        Triple mctx mref cctx cref (KWD O MemoKeysInChild 1)
          (_root_.tryFinally
            (do
              let constInfo ← getConstInfo declName
              let env ← getEnv
              synthesizeFromConst (translate env) (profLogIO prof.isSome) declName [] false true
                (entryConst true false [] constInfo (instancePredicate env) (userInliner env)
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
          (fun _ => KWD O (MemoKeysExc declName) 0) (fun e w => KW O (fun _ _ => True) w ∧ OkExc e) := by
      intro m1 m2 m3 m4 m5 m6 m7
      refine Triple.conseq (R := fun e w => KWD O MemoKeysInChild 0 w ∧ OkExc e) ?_ (fun _ h => h) (fun _ _ h => h)
        (fun _ _ h => ⟨kw_weak h.1.1, h.2⟩)
      refine tryFinallySplit2 (Mo := KWD O (MemoKeysExc declName) 1) (Me := KWD O MemoKeysInChild 1)
        (E := OkExc) ?_
        (fin_totalD M hA (MemoKeysExc declName) 0 m1 m2 m3 m4 m5 m6 m7)
        (fin_totalD M hA MemoKeysInChild 0 m1 m2 m3 m4 m5 m6 m7)
      refine Triple.bind (keeps_iff.mp (keepsK_framedNM M hA (stableK_KWD O MemoKeysInChild 1)
        (FramedNM.constInfo _))) ?_
      intro ci
      refine Triple.bind (keeps_iff.mp (keepsK_framedNM M hA (stableK_KWD O MemoKeysInChild 1)
        FramedNM.env)) ?_
      intro env
      exact hbody hlt prof.isSome env _ _
    exact body _ _ _ _ _ _ _

variable (hlog : LogMvK O)
  (hImpl : ∀ D, D ≠ 0 → LegacyImplK O (KWD O MemoKeysInChild D))
  (hleg : ∀ D, D ≠ 0 → LegacyArmD O D)
include hlog hImpl hleg

/-- **The outermost entry of the K walk**: from a quiet world with the synthesis ref (K not needed) at depth 0, `synthesizeCombinationalCoreWith` with the
real translator returns in K_declName (depth 0) and fails in quiet + the synthesis ref. Hypotheses: `LogMvK`, `LegacyImplK`, `LegacyArmD` only. -/
theorem topEntry_K (declName : Name) :
    Triple mctx mref cctx cref (KWD O (fun _ _ => True) 0)
      (synthesizeCombinationalCoreWith (fun env e h t n => translateExprToWire env e h t n) declName [] false true)
      (fun _ => KWD O (MemoKeysExc declName) 0) (fun e w => KW O (fun _ _ => True) w ∧ OkExc e) := by
  refine entryTop_windowD M hA hlog _ declName (fun _ b env ci isInst => ?_)
  have hD1 : (1 : Nat) ≠ 0 := Nat.one_ne_zero
  have hS := stableK_KWD O MemoKeysInChild 1
  have IH := synthesizeChild_depthK M hlog hImpl hleg 1 hD1
  have hchild : ∀ c, Keeps mctx mref cctx cref (KWD O MemoKeysInChild 1) (synthesizeChild c) :=
    fun c => keeps_iff.mpr (IH mctx cctx hA c)
  have hsv : ∀ w, KWD O MemoKeysInChild 1 w → sv w = some synthesizeChild := fun _ h => h.1.2.1
  have hEntry : ChildEntryK O (KWD O MemoKeysInChild 1) := by
    intro mctx' cctx' hA' c
    have hchild' : ∀ c, Keeps mctx' mref cctx' cref (KWD O MemoKeysInChild 1) (synthesizeChild c) :=
      fun c => keeps_iff.mpr (IH mctx' cctx' hA' c)
    refine keeps_iff.mpr ?_
    unfold childSynthEntry
    refine Triple.bindQ (tripleK_synthGet M hA' hS hsv) ?_
    intro s hs
    subst hs
    dsimp only
    exact keeps_iff.mp (hchild' c)
  have htr := translate_keepsK M hS env (hImpl 1 hD1) (legacyCachedK_of_impl M hS (hImpl 1 hD1)) hEntry mctx cctx hA
  exact Tools.ShippingGen4KWalkDepthArms.fromConst_frontends_windowD M hA hlog 1
    (fun e h t n => translateExprToWire env e h t n) b declName ci isInst htr hchild
    (fun hc hm => hleg 1 hD1 mctx cctx hA b env declName ci isInst hc hm)

end Top

end Tools.ShippingGen4KWalkDepthTop

#print axioms Tools.ShippingGen4KWalkDepthTop.triple_memoResetD
#print axioms Tools.ShippingGen4KWalkDepthTop.triple_childResetD
#print axioms Tools.ShippingGen4KWalkDepthTop.entryTop_windowD
#print axioms Tools.ShippingGen4KWalkDepthTop.topEntry_K
