import Tools.ShippingGen4KWalkFallback
import Tools.ShippingChildFrontA
-- BUILT: kjob lake build Tools.ShippingGen4KWalkEntry exit 0 (rt169, source as of b0c1ab46); axioms standard only. Clean build is the coder's. S4 (part 1) of scripts/gen4/KWALK_PLAN.md, frozen in scripts/gen4/KWALK_S4_FREEZE.md: the entry arms' parts (emitLeaves / certified / mixed / machine) and the memo-write step that opens the window, for `KWalk`.
-- Takes `MemoFamily` (TRUSTED, approved) as a HYPOTHESIS `M`; adds NO premise, NO law, NO axiom to the family.
-- DIAG-PENDING hypothesis `LogMvK` (one run of the profile logger leaves the memo as it was): a `def`, NOT a family statement; it is what scripts/gen4/KWALK_DIAG_DECISION.md option A would give.
-- No `sorry`, no `axiom`, no `native_decide`. Ledger delta: FG -0 +0 / T1 -0 +0.
namespace Tools.ShippingGen4KWalkEntry
open Lean Meta
open Tools.ShippingEntrySoundness
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv
open Tools.ShippingChildBndInit
open Tools.ShippingChildBndCore
open Tools.ShippingChildInvA
open Tools.ShippingChildFresh
open Tools.ShippingChildVCA
open Tools.ShippingChildVertA
open Tools.ShippingChildPathA
open Tools.ShippingChildTranslateA
open Tools.ShippingChildFrontA
open Tools.Assume.MemoFamily
open Tools.ShippingGen4KWalk
open Tools.ShippingGen4KWalkPrims

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- **DIAG-PENDING HYPOTHESIS.** One run of the profile logger (`profLogIO b msg`, the entry's `logProf`) leaves the
memo as it was, in a quiet world. The A boundary (`O.diag`) says this of `cv`/`sv`/`dv` and quietness only. -/
def LogMvK (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx → ∀ b msg w, O.quiet w →
    mv (endW mctx mref cctx cref (liftM (profLogIO b msg) : MetaM Unit) w) = mv w

section Arms
variable {O : RefLawsAOps MkRefd mref cref} (M : MemoFamily O) (hA : AdmCtx O.quiet mctx cctx)
  {I : Void IO.RealWorld → Prop} (hS : StableK O.quiet I)
include M hA hS

/-- The profile logger keeps a `StableK` invariant, given `LogMvK`. -/
theorem keepsK_profLog (hlog : LogMvK O) (b : Bool) (msg : String) :
    Keeps mctx mref cctx cref I (liftM (profLogIO b msg) : MetaM Unit) := by
  intro w hw
  have hq := hS.1 w hw
  have hk := O.diag hA _ (Diag.profLog b msg) w hq
  have hm := hlog mctx cctx hA b msg w hq
  refine ⟨hS.2 w _ hk.1.1 hk.1.2.1 hk.1.2.2 hm (fun _ => hk.2) hw, ?_⟩
  unfold ErrOk
  cases hmm : (liftM (profLogIO b msg) : MetaM Unit) mctx mref cctx cref w with
  | ok a w1 => exact True.intro
  | error e w1 => exact O.excOk hA _ (.diag (Diag.profLog b msg)) w e w1 hq hmm

/-- `IO.mkRef v` returns a ref with provenance. -/
theorem tripleK_mkExprCache (v : Lean.ExprStructMap String) :
    Triple mctx mref cctx cref I (IO.mkRef v : MetaM (IO.Ref (Lean.ExprStructMap String)))
      (fun r w => I w ∧ MkRefd _ r) (fun e w => I w ∧ OkExc e) := by
  intro w hw
  have hK := keeps_iff.mp (keepsK_framedNM M hA hS (FramedNM.mkExprCache v)) w hw
  cases hm : (IO.mkRef v : MetaM (IO.Ref (Lean.ExprStructMap String))) mctx mref cctx cref w with
  | ok r w1 => rw [hm] at hK; exact ⟨hK, mkRefd_of_runs hm⟩
  | error e w1 => rw [hm] at hK; exact hK

theorem keepsK_mkExprCache_bind (v : Lean.ExprStructMap String) {β : Type}
    {k : IO.Ref (Lean.ExprStructMap String) → MetaM β}
    (hk : ∀ r, MkRefd _ r → Keeps mctx mref cctx cref I (k r)) :
    Keeps mctx mref cctx cref I
      ((IO.mkRef v : MetaM (IO.Ref (Lean.ExprStructMap String))) >>= k) :=
  keeps_iff.mpr (Triple.bindQ (φ := MkRefd _) (tripleK_mkExprCache M hA hS v)
    fun r hr => keeps_iff.mp (hk r hr))

/-! ## The binder walk and the leaf emission -/

theorem bindInputPortKP {α : Type} (fv : FVarId) (bn : String) (ty : Sparkle.IR.Type.HWType) (k : CompilerM α)
    (hk : KeepsCP mctx mref cctx cref I k) :
    KeepsCP mctx mref cctx cref I (bindInputPort fv bn ty k) := by
  unfold bindInputPort
  refine KeepsCP.bind (makeWirePK M hA hS _ _ _) (fun _ => ?_)
  refine KeepsCP.bind (addInputPK M hA hS _ _) (fun _ => ?_)
  exact withVarMappingP _ _ hk

theorem bindCertifiedInputsKP {α : Type} (k : CompilerM α) (hk : KeepsCP mctx mref cctx cref I k) :
    ∀ l : List ((Name × GateBinder) × FVarId),
      KeepsCP mctx mref cctx cref I (bindCertifiedInputs k l)
  | [] => by unfold bindCertifiedInputs; exact hk
  | ((_, .domain), _) :: rest => by
    unfold bindCertifiedInputs
    exact bindCertifiedInputsKP k hk rest
  | ((_, .signal _), _) :: rest => by
    unfold bindCertifiedInputs
    exact bindInputPortKP M hA hS _ _ _ _ (bindCertifiedInputsKP k hk rest)

theorem bindMixedCertifiedInputsKP {α : Type} (k : CompilerM α) (hk : KeepsCP mctx mref cctx cref I k) :
    ∀ l : List ((Name × MixedGateBinder) × FVarId),
      KeepsCP mctx mref cctx cref I (bindMixedCertifiedInputs k l)
  | [] => by unfold bindMixedCertifiedInputs; exact hk
  | ((_, .domain), _) :: rest => by
    unfold bindMixedCertifiedInputs
    exact bindMixedCertifiedInputsKP k hk rest
  | ((_, .bool), _) :: rest => by
    unfold bindMixedCertifiedInputs
    exact bindInputPortKP M hA hS _ _ _ _ (bindMixedCertifiedInputsKP k hk rest)
  | ((_, .bits _), _) :: rest => by
    unfold bindMixedCertifiedInputs
    exact bindInputPortKP M hA hS _ _ _ _ (bindMixedCertifiedInputsKP k hk rest)

/-- **`emitLeaves` for `StableK`**, the translator hypothesis restricted to `CtxOk` contexts (copy of `emitLeavesAP`):
every op but the translator is a `FramedNM` op or the logger (`hlog`). -/
theorem emitLeavesKP (hlog : LogMvK O)
    (translate : TranslateFn) (b : Bool) (r : IO.Ref (Lean.ExprStructMap String))
    (hr : MkRefd _ r)
    (htr : ∀ e hint top named, KeepsCP mctx mref cctx cref I (translate e hint top named)) :
    ∀ (leaves : List (String × Lean.Expr)) (fw : Option String) (idx : Nat),
      KeepsCP mctx mref cctx cref I (emitLeaves translate r (profLogIO b) leaves fw idx)
  | [], fw, idx => by
    unfold emitLeaves
    exact KeepsCP.pure _
  | (pn, le) :: rest, fw, idx => by
    unfold emitLeaves
    have clock : KeepsCP mctx mref cctx cref I (CompilerM.liftMetaM (liftM IO.monoMsNow)) :=
      KeepsCP.lift (keepsK_framedNM M hA hS FramedNM.monoMs)
    have calls : KeepsCP mctx mref cctx cref I
        (CompilerM.liftMetaM (ST.Ref.get sparkleCallCounter)) :=
      KeepsCP.lift (keepsK_framedNM M hA hS (FramedNM.sideGet .callCounter))
    have hits : KeepsCP mctx mref cctx cref I
        (CompilerM.liftMetaM (ST.Ref.get sparkleCacheHits)) :=
      KeepsCP.lift (keepsK_framedNM M hA hS (FramedNM.sideGet .cacheHits))
    have log : ∀ msg, KeepsCP mctx mref cctx cref I
        (CompilerM.liftMetaM (liftM (profLogIO b msg))) :=
      fun msg => KeepsCP.lift (keepsK_profLog M hA hS hlog b msg)
    refine KeepsCP.bind clock ?_; intro t0
    refine KeepsCP.bind calls ?_; intro c0
    refine KeepsCP.bind hits ?_; intro h0
    refine KeepsCP.bind (log _) ?_; intro _
    refine KeepsCP.bind (htr le pn false true) ?_; intro lw
    refine KeepsCP.bind clock ?_; intro t1
    refine KeepsCP.bind calls ?_; intro c1
    refine KeepsCP.bind hits ?_; intro h1
    refine KeepsCP.bind (log _) ?_; intro _
    dsimp only
    refine KeepsCP.ite
      (fun _ => KeepsCP.bind (KeepsCP.lift
        (keepsK_framedNM M hA hS (FramedNM.exprCacheModify r _ hr))) (fun _ => ?_))
      (fun _ => ?_)
    all_goals
      try dsimp only
      refine KeepsCP.bind KeepsCP.get ?_
      intro cs
      try dsimp only
      refine KeepsCP.ite (fun _ => ?_) (fun _ => ?_)
      · exact KeepsCP.throwBind _ (by okmsg) _
      · try dsimp only
        refine KeepsCP.bind (addOutputPK M hA hS _ _) ?_
        intro _
        refine KeepsCP.bind (emitAssignP _ _) ?_
        intro _
        exact emitLeavesKP hlog translate b r hr htr rest _ _

/-- `certRest` (the binder walk, the one leaf, the `CircuitM` run, `finishSynth`). -/
theorem certRest_keepsK (hlog : LogMvK O)
    (translate : TranslateFn) (b : Bool) (declName : Name)
    (bs : List (Name × GateBinder)) (body : Lean.Expr)
    (htr : ∀ e hint top named, KeepsCP mctx mref cctx cref I (translate e hint top named))
    (ids : List FVarId) (r : IO.Ref (Lean.ExprStructMap String)) (hr : MkRefd _ r) :
    Keeps mctx mref cctx cref I (certRest translate (profLogIO b) declName bs body ids r) := by
  unfold certRest
  refine keeps_iff.mpr ?_
  try dsimp only
  refine Triple.bind (keeps_iff.mp (bindCertifiedInputsKP M hA hS _
    (emitLeavesKP M hA hS hlog translate b r hr htr _ _ _) _ _ _ (ctxOk_entry false hr))) ?_
  rintro ⟨_, fs⟩
  exact finishSynthA declName fs

/-- `synthesizeCertified` (copy of `certified_keepsA`). -/
theorem certified_keepsK (hlog : LogMvK O)
    (translate : TranslateFn) (b : Bool) (declName : Name)
    (bs : List (Name × GateBinder)) (body : Lean.Expr)
    (htr : ∀ e hint top named, KeepsCP mctx mref cctx cref I (translate e hint top named)) :
    Keeps mctx mref cctx cref I (synthesizeCertified translate (profLogIO b) declName bs body) := by
  unfold synthesizeCertified
  refine Keeps.bind (Keeps.mapM _ (fun _ => keepsK_framedNM M hA hS (FramedNM.freshFVar (Fresh := MkRefd))) _) ?_
  intro ids
  refine Keeps.dite (fun _ => ?_) (fun _ => Keeps.throw _ ?_)
  · show Keeps mctx mref cctx cref I
      ((IO.mkRef ({} : Lean.ExprStructMap String) : MetaM (IO.Ref (Lean.ExprStructMap String)))
        >>= fun r => certRest translate (profLogIO b) declName bs body ids r)
    exact keepsK_mkExprCache_bind M hA hS {} (fun r hr =>
      certRest_keepsK M hA hS hlog translate b declName bs body htr ids r hr)
  · first
      | exact OkMsg.str _
      | (unfold OkExc; exact OkMsg.str _)
      | (show OkMsg (stringToMessageData _); exact OkMsg.str _)
      | exact OkMsg.fmt _

/-- `synthesizeMixedCertified` (copy of `mixed_keepsA`). -/
theorem mixed_keepsK (hlog : LogMvK O)
    (translate : TranslateFn) (b : Bool) (declName : Name)
    (bs : List (Name × MixedGateBinder)) (body : Lean.Expr)
    (htr : ∀ e hint top named, KeepsCP mctx mref cctx cref I (translate e hint top named)) :
    Keeps mctx mref cctx cref I
      (synthesizeMixedCertified translate (profLogIO b) declName bs body) := by
  rw [keeps_iff]
  unfold synthesizeMixedCertified
  refine Triple.bind
    (Triple.mapM _ (fun _ => keeps_iff.mp (keepsK_framedNM M hA hS (FramedNM.freshFVar (Fresh := MkRefd)))) _) ?_
  intro ids
  split
  · dsimp only
    refine Triple.bindQ (φ := MkRefd _) (tripleK_mkExprCache M hA hS _) ?_
    intro cacheRef hr
    refine Triple.bind (keeps_iff.mp (bindMixedCertifiedInputsKP M hA hS _
      (emitLeavesKP M hA hS hlog translate b cacheRef hr htr _ _ _) _ _ _ (ctxOk_entry false hr))) ?_
    rintro ⟨_, fs⟩
    exact finishSynthA declName fs
  · exact Triple.throw _ fun _ hw => ⟨hw, by okmsg⟩

/-! ## The machine synthesis -/

theorem tripleK_synthGet (hsv : ∀ w, I w → sv w = some synthesizeChild) :
    Triple mctx mref cctx cref I (sparkleChildSynth.get : MetaM _)
      (fun s w => I w ∧ s = some synthesizeChild) (fun e w => I w ∧ OkExc e) := by
  intro w hw
  have hK := keeps_iff.mp (keepsK_framedNM M hA hS FramedNM.synthGet) w hw
  cases hm : (sparkleChildSynth.get : MetaM _) mctx mref cctx cref w with
  | ok a w1 =>
    rw [hm] at hK
    exact ⟨hK, (runsTo_get_readOf _ hm).trans (hsv w hw)⟩
  | error e w1 => rw [hm] at hK; exact hK

theorem closeInstsM_keepsK (hsv : ∀ w, I w → sv w = some synthesizeChild)
    (hchild : ∀ c, Keeps mctx mref cctx cref I (synthesizeChild c))
    (shape : MachineShape) (t m : Sparkle.IR.AST.Module) (design : Sparkle.IR.AST.Design) :
    Keeps mctx mref cctx cref I (closeInstsM shape t m design) := by
  rw [keeps_iff]
  unfold closeInstsM
  refine Triple.bindQ (tripleK_synthGet M hA hS hsv) ?_
  intro s hs
  subst hs
  dsimp only
  refine Triple.bind (Triple.mapM _ (fun x => ?_) _) ?_
  · obtain ⟨c, _, _⟩ := x
    exact keeps_iff.mp (hchild c)
  · intro _
    exact Triple.pure fun _ hw => hw

theorem closeInstsGM_keepsK (hsv : ∀ w, I w → sv w = some synthesizeChild)
    (hchild : ∀ c, Keeps mctx mref cctx cref I (synthesizeChild c))
    (shape : MachineShape) (t m : Sparkle.IR.AST.Module) (design : Sparkle.IR.AST.Design) :
    Keeps mctx mref cctx cref I (closeInstsGM shape t m design) := by
  rw [keeps_iff]
  unfold closeInstsGM
  refine Triple.bindQ (tripleK_synthGet M hA hS hsv) ?_
  intro s hs
  subst hs
  dsimp only
  refine Triple.bind (Triple.mapM _ (fun x => ?_) _) ?_
  · obtain ⟨c, o⟩ := x
    dsimp only
    cases Sparkle.Compiler.MachInstOrigin.InstOrigin.child? o with
    | some md => exact Triple.pure fun _ hw => hw
    | none => exact keeps_iff.mp (hchild c)
  · intro _
    exact Triple.pure fun _ hw => hw

theorem machineCert_keepsK (hlog : LogMvK O)
    (translate : TranslateFn) (b : Bool) (declName : Name)
    (htr : ∀ e hint top named, KeepsCP mctx mref cctx cref I (translate e hint top named))
    (hchild : ∀ c, Keeps mctx mref cctx cref I (synthesizeChild c))
    (hsv : ∀ w, I w → sv w = some synthesizeChild) (shape : MachineShape) :
    Keeps mctx mref cctx cref I
      (synthesizeMachineCertified translate (profLogIO b) declName shape) := by
  rw [keeps_iff]
  unfold synthesizeMachineCertified
  refine Triple.bind
    (keeps_iff.mp (mixed_keepsK M hA hS hlog translate b declName shape.binders shape.body htr)) ?_
  rintro ⟨t, d⟩
  dsimp only
  split
  · split
    · exact Triple.pure fun _ hw => hw
    · split
      · exact keeps_iff.mp (closeInstsM_keepsK M hA hS hsv hchild _ _ _ _)
      · exact keeps_iff.mp (closeInstsGM_keepsK M hA hS hsv hchild _ _ _ _)
  · exact Triple.pure fun _ hw => hw

end Arms

/-! ## The window: the memo write of `n` opens it (K → K_n) -/

section Window
variable {O : RefLawsAOps MkRefd mref cref} (M : MemoFamily O) (hA : AdmCtx O.quiet mctx cctx)
include M hA

/-- The memo write `memo.modify (·.insert n r)`: from K, returns in K_n (it cannot throw). -/
theorem triple_memoInsert (n : Name) (r : Res) :
    Triple mctx mref cctx cref (KWalk O)
      (sparkleSubModuleCache.modify (·.insert n r) : MetaM Unit)
      (fun _ => KWalkX O n) (fun e w => KWalk O w ∧ OkExc e) := by
  intro w hw
  obtain ⟨a, w', hr⟩ := refModify_runs (mctx := mctx) (mref := mref) (cctx := cctx) (cref := cref)
    sparkleSubModuleCache (·.insert n r) w
  have e := hr
  unfold RunsTo at e
  rw [e]
  exact kwalk_memoInsert M hA n r hr hw

/-- A memo read that hits, or any step that leaves K: K weakens to K_n. -/
theorem kwalkX_of_kwalk {n : Name} {w : Void IO.RealWorld} (h : KWalk O w) : KWalkX O n w :=
  ⟨h.1, h.2.1, memoKeysInChild_exc n h.2.2⟩

end Window

end Tools.ShippingGen4KWalkEntry

#print axioms Tools.ShippingGen4KWalkEntry.keepsK_profLog
#print axioms Tools.ShippingGen4KWalkEntry.certified_keepsK
#print axioms Tools.ShippingGen4KWalkEntry.machineCert_keepsK
#print axioms Tools.ShippingGen4KWalkEntry.triple_memoInsert
