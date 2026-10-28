import Tools.ShippingChildLegacyImplA
import Tools.ShippingChildProjFieldA
import Tools.ShippingChildFrontCP
import Tools.ShippingChildLegacyCachedA
import Tools.ShippingChildCanonKeyA
import Tools.ShippingChildDepthA
-- BUILT (unit B3, par/u-b3): t7 exit 0 (`legacyTail_core`), t9 exit 0 (exports; earlier t1-t6/t8 exit 1: missing `Array.mapM`/`allM` rules,
-- `pure_bind` needs a LawfulMonad MetaM, namespaces); audit au3 (Tests.Compiler.ChildVertAuditTest) below.
-- No `sorry`, no `axiom`, no `native_decide`, no new law / field. Assumptions: `O : RefLawsAOps MkRefd mref cref`,
-- `hA : AdmCtx O.quiet mctx cctx`, `hS : StableA O.quiet I`, and the ADDED unproved telescope family
-- `T : RefLawsATele O.quiet mref cref` (fields `telescope`, `lamTelescope`; logical inconsistency NOT PROVEN).
-- PROVED: `legacyTailA_generic` (translator `RecA O I translate` is an ARGUMENT), `legacyTailA_of_step`
-- (`LegacyTailA O D` from `hC : ChildKeepsA O D`). The corollaries `bodyKeepsA_of_step`/`bodyStepA_of_T`/`core_tripleA_of_T`
-- were removed at integration: the JQ main theorem lives in Tools/ShippingChildMainA.lean only (no duplicates).
-- Runtime fit of `Lean.Expr`/`Meta` primitives and the model->ST correspondence: OPEN (see docs/parallel/legacy-tail-inventory.md).

namespace Tools.ShippingChildLegacyTailA
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
open Tools.ShippingChildWalkA
open Tools.ShippingChildLegacyHelpersA
open Tools.ShippingChildProjFieldA
open Tools.ShippingChildPathA
open Tools.ShippingChildTranslatePathA

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 4000000

attribute [keepsA] keepsA_getConstInfoInduct keepsA_getConstInfoCtor keepsA_getUserName

/-! ## `Array.mapM` / `Array.allM` (law-free, generic in `I`; the old forms were `(J L D)`) -/

theorem arrayMapM_map_keepsA {I : Void IO.RealWorld → Prop} {α β : Type} (f : α → MetaM β)
    (as : Array α) (hf : ∀ a, Keeps mctx mref cctx cref I (f a)) :
    ∀ (n i : Nat) (bs : Array β), as.size - i < n →
      Keeps mctx mref cctx cref I
        ((privConst% Init.Data.Array.Basic Array.mapM.map) f as i bs)
  | 0, _, _, h => by omega
  | n + 1, i, bs, h => by
    have ih := fun bs (h' : as.size - (i + 1) < n) => arrayMapM_map_keepsA f as hf n (i + 1) bs h'
    unfoldPriv Init.Data.Array.Basic Array.mapM.map
    vca

@[keepsA] theorem Keeps.arrayMapMA {I : Void IO.RealWorld → Prop} {α β : Type} (f : α → MetaM β)
    (as : Array α) (hf : ∀ a, Keeps mctx mref cctx cref I (f a)) :
    Keeps mctx mref cctx cref I (as.mapM f) := by
  unfold Array.mapM
  exact arrayMapM_map_keepsA f as hf _ 0 _ (Nat.lt_succ_self _)

theorem anyM_loop_keepsA {I : Void IO.RealWorld → Prop} {α : Type} (p : α → MetaM Bool)
    (as : Array α) (hp : ∀ a, Keeps mctx mref cctx cref I (p a)) (stop : Nat) (hs : stop ≤ as.size) :
    ∀ (n j : Nat), stop - j < n → Keeps mctx mref cctx cref I (Array.anyM.loop p as stop hs j)
  | 0, _, h => by omega
  | n + 1, j, h => by
    have ih := fun (h' : stop - (j + 1) < n) => anyM_loop_keepsA p as hp stop hs n (j + 1) h'
    unfold Array.anyM.loop
    vca

@[keepsA] theorem Keeps.allMA {I : Void IO.RealWorld → Prop} {α : Type} (p : α → MetaM Bool)
    (as : Array α) (start stop : Nat) (hp : ∀ a, Keeps mctx mref cctx cref I (p a)) :
    Keeps mctx mref cctx cref I (Array.allM p as start stop) := by
  have hl := fun (q : α → MetaM Bool) (hq : ∀ a, Keeps mctx mref cctx cref I (q a)) stop hs j =>
    anyM_loop_keepsA q as hq stop hs (stop - j + 1) j (Nat.lt_succ_self _)
  unfold Array.allM Array.anyM
  vca

section Tail
variable (O : RefLawsAOps MkRefd mref cref) {I : Void IO.RealWorld → Prop}
  (hS : StableA O.quiet I)
  (TLam : LamTelescopeLawA O.quiet mref cref) (TF : ForallTelescopeLawA O.quiet mref cref)
include O hS TLam TF

theorem openRecordInputs_walk_keeps (body : Lean.Expr) (params : Array Lean.Expr)
    (inner : Lean.Expr) :
    ∀ (fuel : Nat) (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx →
      ∀ idx binders subst opened,
      Keeps mctx mref cctx cref I
        (openRecordInputs.walk body params inner fuel idx binders subst opened)
  | 0, mctx, cctx, hA, idx, binders, subst, opened => by
    unfold openRecordInputs.walk
    vca
  | fuel + 1, mctx, cctx, hA, idx, binders, subst, opened => by
    have ih : ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx →
        ∀ idx binders subst opened,
        Keeps mctx mref cctx cref I
          (openRecordInputs.walk body params inner fuel idx binders subst opened) :=
      fun mctx cctx hA => openRecordInputs_walk_keeps body params inner fuel mctx cctx hA
    unfold openRecordInputs.walk
    vca

theorem openRecordInputs_keeps (hA : AdmCtx O.quiet mctx cctx) (body : Lean.Expr) :
    Keeps mctx mref cctx cref I (openRecordInputs body) := by
  have hw := openRecordInputs_walk_keeps O hS TLam TF
  unfold openRecordInputs
  vca

theorem splitReturnLeavesStep_keeps :
    ∀ (rec : Lean.Expr → Option String → MetaM (Array (String × Lean.Expr))),
      (∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx → ∀ a b,
        Keeps mctx mref cctx cref I (rec a b)) →
      ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx → ∀ a b,
        Keeps mctx mref cctx cref I (splitReturnLeavesStep rec a b) := by
  intro rec hrec mctx cctx hA e p
  unfold splitReturnLeavesStep
  vca

theorem splitReturnLeaves_keeps (hA : AdmCtx O.quiet mctx cctx) (e : Lean.Expr)
    (p : Option String) : Keeps mctx mref cctx cref I (splitReturnLeaves e p) :=
  fuelFixM2_keepsA splitReturnLeavesStep (splitReturnLeavesStep_keeps O hS TLam TF) _ mctx cctx hA e p

theorem bindInputsLegacy_keepsCP (hA : AdmCtx O.quiet mctx cctx) (parameters : List (String × Nat))
    (symbolicMode : Bool) (xs : Array Lean.Expr) (k : CompilerM String)
    (hk : KeepsCP mctx mref cctx cref I k) (i : Nat) :
    KeepsCP mctx mref cctx cref I (bindInputsLegacy parameters symbolicMode xs i k) := by
  by_cases h : i < xs.size
  · have ih := bindInputsLegacy_keepsCP hA parameters symbolicMode xs k hk (i + 1)
    unfold bindInputsLegacy
    rw [dif_pos h]
    vca
  · unfold bindInputsLegacy
    rw [dif_neg h]
    exact hk
termination_by xs.size - i
decreasing_by omega

attribute [keepsA] openRecordInputs_keeps splitReturnLeaves_keeps

theorem legacyTail_core (hA : AdmCtx O.quiet mctx cctx) (translate : TranslateFn)
    (htr : RecA O I translate)
    (b : Bool) (declName : Name) (ci : ConstantInfo) (isInst : Lean.Expr → Bool) :
    Keeps mctx mref cctx cref I
      (synthesizeFromConst translate (profLogIO b) declName [] false false ci isInst) := by
  unfold synthesizeFromConst
  simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.and_true,
    List.isEmpty_nil]
  refine Tools.ShippingChildFrontA.keeps_pure_bind_of ?_
  dsimp only
  refine Tools.ShippingChildFrontA.keeps_pure_bind_of ?_
  dsimp only
  refine Keeps.bind (by vca) fun memo => ?_
  split
  · vca
  · refine Keeps.bind (by vca) fun _ => ?_
    split
    · refine Keeps.bind (by vca) fun _ => ?_
      refine Keeps.bind (by vca) fun _ => ?_
      refine Keeps.bind (by vca) fun _ => ?_
      refine Keeps.bind (by vca) fun _ => ?_
      refine Keeps.bind (by vca) fun _ => ?_
      refine Keeps.bind (by vca) fun _ => ?_
      refine keepsA_lambdaTelescope O hA hS TLam _ _ _ (fun m c xs b' hA' => ?_)
      refine Keeps.bind (by vca) fun _ => ?_
      refine Keeps.bind (splitReturnLeaves_keeps O hS TLam TF hA' _ _) fun leaves => ?_
      refine Keeps.bind (by vca) fun _ => ?_
      refine Keeps.bind (by vca) fun _ => ?_
      rw [keeps_iff]
      refine Triple.bindQ (φ := MkRefd _) (tripleA_mkExprCache O hA' hS _) ?_
      intro cacheRef hr
      refine Triple.bind
        (keeps_iff.mp (bindInputsLegacy_keepsCP O hS TLam TF hA' _ _ _ _
          (emitLeavesAP O hA' hS translate b cacheRef hr (htr m c hA') _ _ _) 0 _ _
          (ctxOk_entry false hr))) ?_
      rintro ⟨_, fs⟩
      refine Triple.bind (finishSynthA declName fs) ?_
      intro result
      refine Triple.bind (keeps_iff.mp (keepsA_framed O hA' hS (FramedA.sideModify _ .subModule))) ?_
      intro _
      exact Triple.pure fun _ hw => hw
    · vca

end Tail

open Tools.ShippingChildFrontCP
open Tools.ShippingChildDepthA
open Tools.ShippingChildFallbackA

/-- **The legacy tail, GENERIC in the invariant** (`Keeps … I`, `StableA O.quiet I`): the entry
with the certified front end OFF (`synthesizeFromConst … false false ci isInst`) keeps `I`, given
the translator `RecA O I translate` as an argument and the telescope family `T` (an ADDED,
unproved boundary; used for `lambdaTelescope` and the `forallTelescopeReducing` inside
`openRecordInputs`/`splitReturnLeaves`). No gate hypothesis is needed: with the front end off both
gates and the machine route are skipped, so the statement holds for EVERY constant, in particular
for the ones on which both gates miss. No child hypothesis: the tail's only recursion is `translate`. -/
theorem legacyTailA_generic (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    {I : Void IO.RealWorld → Prop} (hS : StableA O.quiet I) (hA : AdmCtx O.quiet mctx cctx)
    (translate : TranslateFn) (htr : RecA O I translate) (b : Bool) (declName : Name)
    (ci : ConstantInfo) (isInst : Lean.Expr → Bool) :
    Keeps mctx mref cctx cref I
      (synthesizeFromConst translate (profLogIO b) declName [] false false ci isInst) :=
  legacyTail_core O hS (RefLawsATele.lamTelescopeLaw T) (RefLawsATele.forallTelescopeLaw T) hA
    translate htr b declName ci isInst

/-- **`LegacyTailA O D` from the depth step's hypothesis `ChildKeepsA O D`** (the JQ instance of
`legacyTailA_generic`): the translator at `JQ O.quiet D` is built from `hC` (the child entry through
the D2 bridge, `legacyImplA_of_tele`, `canonKeyA`, `legacyCachedA_of_impl`, `projFieldNameA`). Premise
beyond `hC`: `T` only. -/
theorem legacyTailA_of_step (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (D : Nat) (hC : ChildKeepsA O D) : LegacyTailA O D := by
  intro mctx cctx hA declName tenv b ci isInst _ _
  have hS := stableA_JQ O.quiet D
  have hcanon : CanonKeyA O (JQ O.quiet D) := Tools.ShippingChildCanonKeyA.canonKeyA O hS
  have hImpl : LegacyImplA O (JQ O.quiet D) :=
    Tools.ShippingChildLegacyImplA.legacyImplA_of_tele O hS T hcanon
      (childEntryA_JQ_of_childSynthA O D hC)
  exact legacyTailA_generic O T hS hA _
    (translate_keepsJQ O D tenv hImpl (Tools.ShippingChildLegacyCachedA.legacyCachedA_of_impl O hS hImpl)
      hcanon (Tools.ShippingChildProjFieldA.projFieldNameA O T hS) hC)
    b declName ci isInst

end Tools.ShippingChildLegacyTailA

#print axioms Tools.ShippingChildLegacyTailA.legacyTailA_generic
#print axioms Tools.ShippingChildLegacyTailA.legacyTailA_of_step
