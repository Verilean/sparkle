import Tools.ShippingGen4KWalkEmit
-- BUILT: kjob lake build Tools.ShippingGen4KWalkInst exit 0 (rt167, source as of de85ce20); axioms standard only. Clean build is the coder's. S3 (part 2) of scripts/gen4/KWALK_PLAN.md, frozen in scripts/gen4/KWALK_S3_FREEZE.md: the validated-cache wrapper, the instance helpers and the two instance lowerings
-- (copies of ShippingChildFallbackA 327-503), with `StableK` instead of `StableA`.
-- Takes `MemoFamily` (TRUSTED, approved) as a HYPOTHESIS `M`; adds NO premise, NO law, NO axiom.
-- No `sorry`, no `axiom`, no `native_decide`. Ledger delta: FG -0 +0 / T1 -0 +0.

namespace Tools.ShippingGen4KWalkInst
open Lean Meta
open Tools.ShippingEntrySoundness
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv
open Tools.ShippingChildBndInit
open Tools.ShippingChildBndCore
open Tools.ShippingChildInvA
open Tools.ShippingChildFresh
open Tools.ShippingChildPathA
open Tools.ShippingChildTranslateA
open Tools.Assume.MemoFamily
open Tools.ShippingGen4KWalk
open Tools.ShippingGen4KWalkPrims
open Tools.ShippingGen4KWalkTranslate
open Tools.ShippingGen4KWalkEmit
open Tools.ShippingChildKWalk

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-! ## The shared validated-cache wrapper -/

section Wrapper
variable {O : RefLawsAOps MkRefd mref cref} (M : MemoFamily O) (hA : AdmCtx O.quiet mctx cctx)
  {I : Void IO.RealWorld → Prop} (hS : StableK O.quiet I)
include M hA hS

theorem translateControlCachedWithK (lower : TranslateFn)
    (hlow : ∀ e hint top named, KeepsCP mctx mref cctx cref I (lower e hint top named))
    (e : Lean.Expr) (hint : String) (top named : Bool) :
    KeepsCP mctx mref cctx cref I (translateControlCachedWith lower e hint top named) := by
  unfold translateControlCachedWith
  try dsimp only
  kwalk [hlow _ _ _ _, cacheLookupValidatedK M hA hS _, recordTranslationK M hA hS _ _ _]

/-! ## The instance helpers (child compile in hand) -/

theorem instArmCacheGetK : Keeps mctx mref cctx cref I instArmCacheGet := by
  unfold instArmCacheGet
  exact keepsK_framedNM M hA hS (FramedNM.sideGet .singleOut)

theorem instArmCachePutK (key w : String) : Keeps mctx mref cctx cref I (instArmCachePut key w) := by
  unfold instArmCachePut
  exact keepsK_framedNM M hA hS (FramedNM.sideModify _ .singleOut)

theorem instArmOutGetK : Keeps mctx mref cctx cref I instArmOutGet := by
  unfold instArmOutGet
  exact keepsK_framedNM M hA hS (FramedNM.sideGet .subInstOut)

theorem instArmOutPutK (key : UInt64) (out w : String) :
    Keeps mctx mref cctx cref I (instArmOutPut key out w) := by
  unfold instArmOutPut
  exact keepsK_framedNM M hA hS (FramedNM.sideModify _ .subInstOut)

theorem instAddModulesK (existing : List String) :
    ∀ ms : List Sparkle.IR.AST.Module,
      KeepsCP mctx mref cctx cref I (instAddModules existing ms) := by
  -- (integrator, after fb6-fb9 timed out at the declaration: `induction` instead of a
  -- recursive theorem)
  intro ms
  induction ms with
  | nil => rw [instAddModules.eq_1]; exact KeepsCP.pure _
  | cons m ms ih =>
    -- (`unfold` timed out in `simp`, fb11: the equation lemma by `rw`)
    rw [instAddModules.eq_2]
    exact KeepsCP.ite (fun _ => KeepsCP.bind (addModuleToDesignA _) (fun _ => ih)) (fun _ => ih)

theorem instRegisterChildK (existing : List String) (sub : Sparkle.IR.AST.Module) :
    KeepsCP mctx mref cctx cref I (instRegisterChild existing sub) := by
  unfold instRegisterChild
  try dsimp only
  kwalk [addModuleToDesignA _]

theorem instClkRstK :
    ∀ (ps : List Sparkle.IR.AST.Port) (acc : List (String × Sparkle.IR.AST.Expr)),
      KeepsCP mctx mref cctx cref I (instClkRst acc ps)
  | [], acc => by unfold instClkRst; exact KeepsCP.pure _
  | p :: ps, acc => by
    have ih := fun acc => instClkRstK ps acc
    unfold instClkRst
    try dsimp only
    kwalk [ih _, addInputPK M hA hS _ _]  -- guess: F4

theorem instOutWiresK (callKey : UInt64) (hint : String) :
    ∀ (ps : List Sparkle.IR.AST.Port) (conns : List (String × Sparkle.IR.AST.Expr))
      (ws : List (String × String)),
      KeepsCP mctx mref cctx cref I (instOutWires callKey hint ps conns ws)
  | [], conns, ws => by unfold instOutWires; exact KeepsCP.pure _
  | outP :: rest, conns, ws => by
    have ih := fun conns ws => instOutWiresK callKey hint rest conns ws
    unfold instOutWires
    refine KeepsCP.bind (makeWirePK M hA hS _ _ _) (fun _ => ?_)
    refine KeepsCP.bind (KeepsCP.lift (instArmOutPutK M hA hS _ _ _)) (fun _ => ?_)
    exact ih _ _

end Wrapper

section LawFreeInst
variable {I : Void IO.RealWorld → Prop}

theorem instArityCheckK (mn : Name) (need got : Nat) :
    KeepsCP mctx mref cctx cref I (instArityCheck mn need got) := by
  unfold instArityCheck
  refine KeepsCP.ite (fun _ => KeepsCP.throw _ (by okmsg)) (fun _ => KeepsCP.pure _)

theorem instLinkCheckK (mn : Name) (child : Sparkle.IR.AST.Module)
    (conns : List (String × Sparkle.IR.AST.Expr)) :
    KeepsCP mctx mref cctx cref I (instLinkCheck mn child conns) := by
  unfold instLinkCheck
  refine KeepsCP.bind KeepsCP.get (fun _ => ?_)
  unfold instLinkGuard
  refine KeepsCP.ite (fun _ => KeepsCP.pure _) (fun _ => KeepsCP.throw _ (by okmsg))  -- guess: F5

/-- The call key: a builder-state save/restore around `canonHardwareKey`
(premise `hcanon`: not migrated). -/
theorem instCallKeyK (hcanon : ∀ a, KeepsCP mctx mref cctx cref I (canonHardwareKey a))
    (a : Lean.Expr) : KeepsCP mctx mref cctx cref I (instCallKey a) := by
  unfold instCallKey
  refine KeepsCP.bind KeepsCP.get (fun _ => ?_)
  refine KeepsCP.bind (hcanon _) (fun _ => ?_)
  refine KeepsCP.bind (KeepsCP.set _) (fun _ => ?_)
  exact KeepsCP.pure _

end LawFreeInst

/-! ## The instance lowerings -/

section Inst
variable {O : RefLawsAOps MkRefd mref cref} (M : MemoFamily O) (hA : AdmCtx O.quiet mctx cctx)
  {I : Void IO.RealWorld → Prop} (hS : StableK O.quiet I) (rec : TranslateFn)
  (hrec : ∀ e hint top named, KeepsCP mctx mref cctx cref I (rec e hint top named))
include M hA hS hrec

/-- **The single-output instance lowering** (child compile in hand). -/
theorem translateInstanceUncachedWithK (mn : Name) (sub : Sparkle.IR.AST.Module)
    (subD : Sparkle.IR.AST.Design) (singleOut : Sparkle.IR.AST.Port)
    (e : Lean.Expr) (hint : String) (top named : Bool) :
    KeepsCP mctx mref cctx cref I
      (translateInstanceUncachedWith rec mn sub subD singleOut e hint top named) := by
  unfold translateInstanceUncachedWith
  try dsimp only  -- guess: F2
  kwalk [instArmCacheGetK M hA hS, instArmCachePutK M hA hS, hrec _ _ _ _, instAddModulesK M hA hS _ _, instRegisterChildK M hA hS _ _, instClkRstK M hA hS _ _, instArityCheckK _ _ _, instArgsK M hA hS rec hrec _ _ _, KeepsCP.lift (instArmCacheGetK M hA hS), KeepsCP.lift (instArmCachePutK M hA hS _ _), makeWirePK M hA hS _ _ _, freshNameA _ _, instLinkCheckK _ _ _, emitInstanceA _ _ _]

/-- **The multi-output projection lowering** (child compile in hand), given
the call key's `canonHardwareKey` (premise) and the legacy fall-through. -/
theorem translateProjInstanceUncachedWithK
    (hcanon : ∀ a, KeepsCP mctx mref cctx cref I (canonHardwareKey a))
    (recName : Name) (sub : Sparkle.IR.AST.Module) (subD : Sparkle.IR.AST.Design)
    (fieldName : String) (recordArg : Lean.Expr) (legacy : TranslateFn)
    (hleg : ∀ e hint top named, KeepsCP mctx mref cctx cref I (legacy e hint top named))
    (e : Lean.Expr) (hint : String) (top named : Bool) :
    KeepsCP mctx mref cctx cref I
      (translateProjInstanceUncachedWith rec recName sub subD fieldName recordArg legacy
        e hint top named) := by
  unfold translateProjInstanceUncachedWith
  try dsimp only  -- guess: F2
  kwalk [instArmOutGetK M hA hS, hleg _ _ _ _, hrec _ _ _ _, instCallKeyK hcanon _, KeepsCP.lift (instArmOutGetK M hA hS), instAddModulesK M hA hS _ _, instRegisterChildK M hA hS _ _, instClkRstK M hA hS _ _, instArityCheckK _ _ _, instArgsK M hA hS rec hrec _ _ _, instOutWiresK M hA hS _ _ _ _ _, freshNameA _ _, instLinkCheckK _ _ _, emitInstanceA _ _ _]

/-- **The instance arm** (`fallbackKind e = .other`): the dispatch on the
head, the child's synthesis (`hchild`), the two certified lowerings under the
validated cache wrapper, else the legacy translator (`hlegC`). -/
theorem translateInstanceOrFallbackK (env : Lean.Environment)
    (hchild : ∀ c, Keeps mctx mref cctx cref I (childSynthEntry c))
    (hpf : ∀ n s, Keeps mctx mref cctx cref I (projFieldName? n s))
    (hcanon : ∀ a, KeepsCP mctx mref cctx cref I (canonHardwareKey a))
    (hlegC : ∀ e hint top named, KeepsCP mctx mref cctx cref I
      (Rec.translateExprToWireCached (fun e h t n => rec e h t n) e hint top named))
    (e : Lean.Expr) (hint : String) (top named : Bool) :
    KeepsCP mctx mref cctx cref I (translateInstanceOrFallback env rec e hint top named) := by
  unfold translateInstanceOrFallback
  -- (integrator, after fb1-fb8 timed out on the generic walk: the elaborated term, printed by
  -- `#print` (run pr2), walked by hand)
  split
  · refine KeepsCP.ite (fun _ => ?_) (fun _ => ?_)
    · refine KeepsCP.bind (KeepsCP.lift (hchild _)) (fun sub => ?_)
      split
      · exact translateControlCachedWithK M hA hS _
          (translateInstanceUncachedWithK M hA hS rec hrec _ _ _ _) _ _ _ _
      · exact hlegC _ _ _ _
    · split
      · split
        · refine KeepsCP.ite (fun _ => ?_) (fun _ => hlegC _ _ _ _)
          refine KeepsCP.bind (KeepsCP.lift (hpf _ _)) (fun fo => ?_)
          cases fo with
          | some fieldName =>
            refine KeepsCP.bind (KeepsCP.lift (hchild _)) (fun sub => ?_)
            exact KeepsCP.ite
              (fun _ => translateControlCachedWithK M hA hS _
                (translateProjInstanceUncachedWithK M hA hS rec hrec hcanon _ _ _ _ _ _
                  (fun e h t n => hlegC e h t n)) _ _ _ _)
              (fun _ => hlegC _ _ _ _)
          | none => exact hlegC _ _ _ _
        · exact hlegC _ _ _ _
      · exact hlegC _ _ _ _
  · exact hlegC _ _ _ _

end Inst

end Tools.ShippingGen4KWalkInst
