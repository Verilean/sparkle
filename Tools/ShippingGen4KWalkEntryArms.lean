import Tools.ShippingGen4KWalkEntry
-- BUILT: kjob lake build Tools.ShippingGen4KWalkEntryArms exit 0 (rt169, source as of b0c1ab46); axioms standard only. Clean build is the coder's. S4 (part 2) of scripts/gen4/KWALK_PLAN.md (frozen in scripts/gen4/KWALK_S4_FREEZE.md): the arms of `synthesizeFromConst` with the memo window (copy of ShippingChildFrontA 322-445, `Triple` from `KWalk` to `KWalkX declName`).
-- Takes `MemoFamily` (TRUSTED, approved) as a HYPOTHESIS `M`; adds NO premise, NO law, NO axiom to the family. DIAG-PENDING hypothesis `LogMvK` (see Entry). The legacy tail is the premise `hlegacy`.
-- No `sorry`, no `axiom`, no `native_decide`. Ledger delta: FG -0 +0 / T1 -0 +0.
namespace Tools.ShippingGen4KWalkEntryArms
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
open Tools.ShippingGen4KWalkEntry

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

theorem stableK_KWalk (O : RefLawsAOps MkRefd mref cref) : StableK O.quiet (KWalk O) :=
  stableK_KW O _

theorem triple_pure_bind_of {α β : Type} {P : Void IO.RealWorld → Prop} {a : α} {f : α → MetaM β}
    {Q : β → Void IO.RealWorld → Prop} {R : Exception → Void IO.RealWorld → Prop}
    (h : Triple mctx mref cctx cref P (f a) Q R) :
    Triple mctx mref cctx cref P (Pure.pure a >>= f) Q R := by
  first
    | exact h
    | (intro w hw; exact h w hw)

section Arms
variable {O : RefLawsAOps MkRefd mref cref} (M : MemoFamily O) (hA : AdmCtx O.quiet mctx cctx)
  (hlog : LogMvK O)
include M hA hlog

/-- **Certified arm**: from K, returns in K_n (n = declName), throws in K. -/
theorem fromConst_certified_windowK
    (translate : TranslateFn) (b : Bool) (declName : Name) (constInfo : ConstantInfo)
    (isInst : Lean.Expr → Bool) {bs : List (Name × GateBinder)} {body : Lean.Expr}
    (hshape : certifiedShape? false [] constInfo = some (bs, body))
    (htr : ∀ e hint top named, KeepsCP mctx mref cctx cref (KWalk O) (translate e hint top named)) :
    Triple mctx mref cctx cref (KWalk O)
      (synthesizeFromConst translate (profLogIO b) declName [] false true constInfo isInst)
      (fun _ => KWalkX O declName) (fun e w => KWalk O w ∧ OkExc e) := by
  have hd : (if true = true then certifiedShape? false [] constInfo else none) = some (bs, body) := by
    first
      | exact (if_pos rfl).trans hshape
      | (rw [if_pos rfl]; exact hshape)
      | simpa using hshape
  first | delta synthesizeFromConst | unfold synthesizeFromConst
  rw [hd]
  first
    | refine Triple.bind (keeps_iff.mp (keepsK_profLog M hA (stableK_KWalk O) hlog b _)) ?_
    | (dsimp only; refine Triple.bind (keeps_iff.mp (keepsK_profLog M hA (stableK_KWalk O) hlog b _)) ?_)
  intro _
  refine Triple.bind (keeps_iff.mp (certified_keepsK M hA (stableK_KWalk O) hlog translate b declName bs body htr)) ?_
  intro result
  refine Triple.bind (triple_memoInsert M hA declName result) ?_
  intro _
  exact Triple.pure fun _ hw => hw

/-- **Mixed arm**. -/
theorem fromConst_mixed_windowK
    (translate : TranslateFn) (b : Bool) (declName : Name) (constInfo : ConstantInfo)
    (isInst : Lean.Expr → Bool) {bs : List (Name × MixedGateBinder)} {body : Lean.Expr}
    (hc : certifiedShape? false [] constInfo = none)
    (hm : mixedCertifiedShape? false [] constInfo isInst = some (bs, body))
    (htr : ∀ e hint top named, KeepsCP mctx mref cctx cref (KWalk O) (translate e hint top named)) :
    Triple mctx mref cctx cref (KWalk O)
      (synthesizeFromConst translate (profLogIO b) declName [] false true constInfo isInst)
      (fun _ => KWalkX O declName) (fun e w => KWalk O w ∧ OkExc e) := by
  have hd1 : (if true = true then certifiedShape? false [] constInfo else none) = none := by
    first
      | exact (if_pos rfl).trans hc
      | (rw [if_pos rfl]; exact hc)
      | simpa using hc
  have hd2 : (if true = true then mixedCertifiedShape? false [] constInfo isInst else none) =
      some (bs, body) := by
    first
      | exact (if_pos rfl).trans hm
      | (rw [if_pos rfl]; exact hm)
      | simpa using hm
  first | delta synthesizeFromConst | unfold synthesizeFromConst
  rw [hd1, hd2]
  first
    | refine Triple.bind (keeps_iff.mp (keepsK_profLog M hA (stableK_KWalk O) hlog b _)) ?_
    | (dsimp only; refine Triple.bind (keeps_iff.mp (keepsK_profLog M hA (stableK_KWalk O) hlog b _)) ?_)
  intro _
  refine Triple.bind (keeps_iff.mp (mixed_keepsK M hA (stableK_KWalk O) hlog translate b declName bs body htr)) ?_
  intro result
  refine Triple.bind (triple_memoInsert M hA declName result) ?_
  intro _
  exact Triple.pure fun _ hw => hw

/-- **Both gates miss: the machine arm, and the fall-through to the legacy tail** (`hlegacy`: the entry with the
certified front end OFF, which runs the same tail, from K to K_n). -/
theorem fromConst_machine_windowK
    (translate : TranslateFn) (b : Bool) (declName : Name) (constInfo : ConstantInfo)
    (isInst : Lean.Expr → Bool)
    (hc : certifiedShape? false [] constInfo = none)
    (hm : mixedCertifiedShape? false [] constInfo isInst = none)
    (htr : ∀ e hint top named, KeepsCP mctx mref cctx cref (KWalk O) (translate e hint top named))
    (hchild : ∀ c, Keeps mctx mref cctx cref (KWalk O) (synthesizeChild c))
    (hlegacy : Triple mctx mref cctx cref (KWalk O)
      (synthesizeFromConst translate (profLogIO b) declName [] false false constInfo isInst)
      (fun _ => KWalkX O declName) (fun e w => KWalk O w ∧ OkExc e)) :
    Triple mctx mref cctx cref (KWalk O)
      (synthesizeFromConst translate (profLogIO b) declName [] false true constInfo isInst)
      (fun _ => KWalkX O declName) (fun e w => KWalk O w ∧ OkExc e) := by
  have hd1 : (if true = true then certifiedShape? false [] constInfo else none) = none := by
    first
      | exact (if_pos rfl).trans hc
      | (rw [if_pos rfl]; exact hc)
      | simpa using hc
  have hd2 : (if true = true then mixedCertifiedShape? false [] constInfo isInst else none) =
      none := by
    first
      | exact (if_pos rfl).trans hm
      | (rw [if_pos rfl]; exact hm)
      | simpa using hm
  have h := hlegacy
  first | delta synthesizeFromConst | unfold synthesizeFromConst
  first | delta synthesizeFromConst at h | unfold synthesizeFromConst at h
  rw [hd1, hd2]
  simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.and_true,
    List.isEmpty_nil] at h ⊢
  refine Triple.bind (keeps_iff.mp (keepsK_framedNM M hA (stableK_KWalk O) FramedNM.env)) (fun env => ?_)
  generalize machineShape? false [] constInfo (structEnv env) = m
  cases m with
  | none =>
    first
      | exact h
      | exact triple_pure_bind_of h
  | some shape =>
    refine triple_pure_bind_of ?_
    refine Triple.bind (keeps_iff.mp (machineCert_keepsK M hA (stableK_KWalk O) hlog translate b declName
      htr hchild (fun _ h => h.2.1) shape)) ?_
    intro r
    cases r with
    | some result =>
      refine Triple.bind (keeps_iff.mp (keepsK_profLog M hA (stableK_KWalk O) hlog b _)) ?_
      intro _
      refine Triple.bind (triple_memoInsert M hA declName result) ?_
      intro _
      exact Triple.pure fun _ hw => hw
    | none => exact h

/-- **The three front-end arms together** (certified / mixed / machine); the legacy tail is `hlegacy`, asked only of
constants on which both gates miss. -/
theorem fromConst_frontends_windowK
    (translate : TranslateFn) (b : Bool) (declName : Name) (constInfo : ConstantInfo)
    (isInst : Lean.Expr → Bool)
    (htr : ∀ e hint top named, KeepsCP mctx mref cctx cref (KWalk O) (translate e hint top named))
    (hchild : ∀ c, Keeps mctx mref cctx cref (KWalk O) (synthesizeChild c))
    (hlegacy : certifiedShape? false [] constInfo = none →
      mixedCertifiedShape? false [] constInfo isInst = none →
      Triple mctx mref cctx cref (KWalk O)
        (synthesizeFromConst translate (profLogIO b) declName [] false false constInfo isInst)
        (fun _ => KWalkX O declName) (fun e w => KWalk O w ∧ OkExc e)) :
    Triple mctx mref cctx cref (KWalk O)
      (synthesizeFromConst translate (profLogIO b) declName [] false true constInfo isInst)
      (fun _ => KWalkX O declName) (fun e w => KWalk O w ∧ OkExc e) := by
  cases hc : certifiedShape? false [] constInfo with
  | some p =>
    obtain ⟨bs, body⟩ := p
    exact fromConst_certified_windowK M hA hlog translate b declName constInfo isInst hc htr
  | none =>
    cases hm : mixedCertifiedShape? false [] constInfo isInst with
    | some p =>
      obtain ⟨bs, body⟩ := p
      exact fromConst_mixed_windowK M hA hlog translate b declName constInfo isInst hc hm htr
    | none =>
      exact fromConst_machine_windowK M hA hlog translate b declName constInfo isInst hc hm htr
        hchild (hlegacy hc hm)

end Arms

end Tools.ShippingGen4KWalkEntryArms

#print axioms Tools.ShippingGen4KWalkEntryArms.fromConst_certified_windowK
#print axioms Tools.ShippingGen4KWalkEntryArms.fromConst_mixed_windowK
#print axioms Tools.ShippingGen4KWalkEntryArms.fromConst_machine_windowK
#print axioms Tools.ShippingGen4KWalkEntryArms.fromConst_frontends_windowK
