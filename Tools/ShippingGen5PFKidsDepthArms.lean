-- Gen5 port of Tools.ShippingGen4FKidsDepthArms (scripts/gen4/PARAM_ASSEMBLY.md §Gen5): copy for the gen5 Elab; only the marked parts differ.
import Tools.ShippingGen4FKidsTac
import Tools.ShippingGen4FKidsTele
import Tools.ShippingGen4KWalkEntry
import Tools.ShippingGen4FKidsEntry
import Tools.ShippingGen5PFKidsDepth
import Tools.ShippingGen4FKidsEntryArms
namespace Tools.ShippingGen4FKidsDepthArms
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
open Tools.ShippingGen4FKidsPrims
open Tools.ShippingGen4KWalkEntry
open Tools.ShippingGen4FKidsEntry

open Tools.ShippingGen4FKids
open Tools.ShippingGen4FKidsCalc
open Tools.ShippingGen4FKidsPrims
open Tools.ShippingGen4FKidsTac
open Tools.ShippingGen4FKidsTele

open Tools.ShippingGen4KWalkDepth
open Tools.Assume.FramedACases
open Tools.ShippingGen4FKidsDepth
open Tools.ShippingGen4FKidsEntryArms

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

section Arms
variable {O : RefLawsAOps MkRefd mref cref} (M : MemoFamily O) (hA : AdmCtx O.quiet mctx cctx)
  (hlog : LogMvKS O) (D : Nat)
include M hA hlog

/-- **Certified arm**: from K, returns in K_n (n = declName), throws in K. -/
theorem fromConst_certified_windowD
    (translate : TranslateFn) (b : Bool) (declName : Name) (constInfo : ConstantInfo)
    (isInst : Lean.Expr → Bool) {bs : List (Name × GateBinder)} {body : Lean.Expr}
    (hshape : certifiedShape? false [] constInfo = some (bs, body))
    (htr : ∀ e hint top named, KeepsCS mctx mref cctx cref (WPF O D) (translate e hint top named)) :
    Triple mctx mref cctx cref (WPF O D)
      (synthesizeFromConst translate (profLogIO b) declName [] false true constInfo isInst)
      (fun r w => WPFX O declName D w ∧ PairPF r) (fun e w => WPF O D w ∧ OkExc e) := by
  have hd : (if true = true then certifiedShape? false [] constInfo else none) = some (bs, body) := by
    first
      | exact (if_pos rfl).trans hshape
      | (rw [if_pos rfl]; exact hshape)
      | simpa using hshape
  first | delta synthesizeFromConst | unfold synthesizeFromConst
  rw [hd]
  first
    | refine Triple.bind (keeps_iff.mp (keepsK_profLogS M hA (stableK_KWD O PPF D) hlog b _)) ?_
    | (dsimp only; refine Triple.bind (keeps_iff.mp (keepsK_profLogS M hA (stableK_KWD O PPF D) hlog b _)) ?_)
  intro _
  refine Triple.bindQ (P' := WPF O D) (φ := PairPF) (certified_keepsKS M hA (stableK_KWD O PPF D) hlog translate b declName bs body htr) ?_
  intro result hresult
  refine Triple.bind (triple_memoInsertDP M hA D declName result hresult) ?_
  intro _
  exact Triple.pure fun _ hw => ⟨hw, hresult⟩

/-- **Mixed arm**. -/
theorem fromConst_mixed_windowD
    (translate : TranslateFn) (b : Bool) (declName : Name) (constInfo : ConstantInfo)
    (isInst : Lean.Expr → Bool) {bs : List (Name × MixedGateBinder)} {body : Lean.Expr}
    (hc : certifiedShape? false [] constInfo = none)
    (hm : mixedCertifiedShape? false [] constInfo isInst = some (bs, body))
    (htr : ∀ e hint top named, KeepsCS mctx mref cctx cref (WPF O D) (translate e hint top named)) :
    Triple mctx mref cctx cref (WPF O D)
      (synthesizeFromConst translate (profLogIO b) declName [] false true constInfo isInst)
      (fun r w => WPFX O declName D w ∧ PairPF r) (fun e w => WPF O D w ∧ OkExc e) := by
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
    | refine Triple.bind (keeps_iff.mp (keepsK_profLogS M hA (stableK_KWD O PPF D) hlog b _)) ?_
    | (dsimp only; refine Triple.bind (keeps_iff.mp (keepsK_profLogS M hA (stableK_KWD O PPF D) hlog b _)) ?_)
  intro _
  refine Triple.bindQ (P' := WPF O D) (φ := PairPF) (mixed_keepsKS M hA (stableK_KWD O PPF D) hlog translate b declName bs body htr) ?_
  intro result hresult
  refine Triple.bind (triple_memoInsertDP M hA D declName result hresult) ?_
  intro _
  exact Triple.pure fun _ hw => ⟨hw, hresult⟩

/-- **Both gates miss: the machine arm, and the fall-through to the legacy tail** (`hlegacy`: the entry with the
certified front end OFF, which runs the same tail, from K to K_n). -/
theorem fromConst_machine_windowD
    (translate : TranslateFn) (b : Bool) (declName : Name) (constInfo : ConstantInfo)
    (isInst : Lean.Expr → Bool)
    (hc : certifiedShape? false [] constInfo = none)
    (hm : mixedCertifiedShape? false [] constInfo isInst = none)
    (htr : ∀ e hint top named, KeepsCS mctx mref cctx cref (WPF O D) (translate e hint top named))
    (hchild : ∀ c, Triple mctx mref cctx cref (WPF O D) (synthesizeChild c)
      (fun r w => WPF O D w ∧ PairPF r) (fun e w => WPF O D w ∧ OkExc e))
    (hlegacy : Triple mctx mref cctx cref (WPF O D)
      (synthesizeFromConst translate (profLogIO b) declName [] false false constInfo isInst)
      (fun r w => WPFX O declName D w ∧ PairPF r) (fun e w => WPF O D w ∧ OkExc e)) :
    Triple mctx mref cctx cref (WPF O D)
      (synthesizeFromConst translate (profLogIO b) declName [] false true constInfo isInst)
      (fun r w => WPFX O declName D w ∧ PairPF r) (fun e w => WPF O D w ∧ OkExc e) := by
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
  refine Triple.bind (keeps_iff.mp (keepsK_framedNM M hA (stableK_KWD O PPF D) FramedNM.env)) (fun env => ?_)
  generalize machineShape? false [] constInfo (structEnv env) = m
  cases m with
  | none =>
    first
      | exact h
      | exact triple_pure_bind_ofS h
  | some shape =>
    refine triple_pure_bind_ofS ?_
    refine Triple.bindQ (P' := WPF O D) (φ := OptPF) (machineCert_keepsKS M hA (stableK_KWD O PPF D) hlog translate b declName
      htr hchild (fun _ h => h.1.2.1) shape) ?_
    intro r hr
    cases r with
    | some result =>
      refine Triple.bind (keeps_iff.mp (keepsK_profLogS M hA (stableK_KWD O PPF D) hlog b _)) ?_
      intro _
      refine Triple.bind (triple_memoInsertDP M hA D declName result (hr result rfl)) ?_
      intro _
      exact Triple.pure fun _ hw => ⟨hw, hr result rfl⟩
    | none => exact h

/-- **The three front-end arms together** (certified / mixed / machine); the legacy tail is `hlegacy`, asked only of
constants on which both gates miss. -/
theorem fromConst_frontends_windowD
    (translate : TranslateFn) (b : Bool) (declName : Name) (constInfo : ConstantInfo)
    (isInst : Lean.Expr → Bool)
    (htr : ∀ e hint top named, KeepsCS mctx mref cctx cref (WPF O D) (translate e hint top named))
    (hchild : ∀ c, Triple mctx mref cctx cref (WPF O D) (synthesizeChild c)
      (fun r w => WPF O D w ∧ PairPF r) (fun e w => WPF O D w ∧ OkExc e))
    (hlegacy : certifiedShape? false [] constInfo = none →
      mixedCertifiedShape? false [] constInfo isInst = none →
      Triple mctx mref cctx cref (WPF O D)
        (synthesizeFromConst translate (profLogIO b) declName [] false false constInfo isInst)
        (fun r w => WPFX O declName D w ∧ PairPF r) (fun e w => WPF O D w ∧ OkExc e)) :
    Triple mctx mref cctx cref (WPF O D)
      (synthesizeFromConst translate (profLogIO b) declName [] false true constInfo isInst)
      (fun r w => WPFX O declName D w ∧ PairPF r) (fun e w => WPF O D w ∧ OkExc e) := by
  cases hc : certifiedShape? false [] constInfo with
  | some p =>
    obtain ⟨bs, body⟩ := p
    exact fromConst_certified_windowD M hA hlog D translate b declName constInfo isInst hc htr
  | none =>
    cases hm : mixedCertifiedShape? false [] constInfo isInst with
    | some p =>
      obtain ⟨bs, body⟩ := p
      exact fromConst_mixed_windowD M hA hlog D translate b declName constInfo isInst hc hm htr
    | none =>
      exact fromConst_machine_windowD M hA hlog D translate b declName constInfo isInst hc hm htr
        hchild (hlegacy hc hm)

end Arms

end Tools.ShippingGen4FKidsDepthArms

#print axioms Tools.ShippingGen4FKidsDepthArms.fromConst_frontends_windowD
