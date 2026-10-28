import Tools.ShippingChildFrontA
import Tools.ShippingChildDepthA
import Tools.ShippingChildCacheA
-- BUILT (D2, par/u-d2): e3 (Tools.ShippingChildFrontCP) exit 0 (after e1 exit 1: bindQ needed an explicit read triple; e2 exit 0 before the JQ/JQC instances); audit e4 exit 0.
-- BUILT (unit D, par/u-d): d1 exit 0 (first try); audit d2 (Tests.Compiler.ChildVertAuditTest) exit 0.
-- No `sorry`, no `axiom`, no `native_decide`, no new law / boundary field. Law witness:
-- `O : RefLawsAOps MkRefd mref cref` at `hA : AdmCtx O.quiet mctx cctx` only.
-- The proofs COPY the built FrontA proofs with the translator hypothesis `KeepsC` (all compiler
-- contexts) replaced by the restricted `KeepsCP` (`CtxOk` contexts, Tools/ShippingChildTranslateA.lean).
-- The only context the MIXED branch builds is `entryCompilerState false cacheRef`, `cacheRef` from the
-- allocation recorded `MkRefd` (`tripleA_mkExprCache`): `ctxOk_entry false hr` (reused), the binder
-- walk keeps it via `bindInputPortAP` (reused). The MACHINE branch builds no further compiler context:
-- `closeInstsM_keepsA` / `closeInstsGM_keepsA` and the branch proof of `fromConst_machine_keepsA`
-- are reused / copied unchanged, only the translator and child hypotheses change form.
-- Writing-time guesses: R1 `bindMixedCertifiedInputsAP` as `bindCertifiedInputsAP`; R2 `mixed_keepsAP`
-- fixes the context by `ctxOk_entry false hr` (as TranslatePathA Q2); R3 the machine/fromConst proofs
-- are the FrontA ones verbatim modulo `htr`.

/-! # Mixed and machine front ends with the RESTRICTED translator

PROVED (given the named premises): `mixed_keepsAP`, `machineCert_keepsAP`, `fromConst_mixed_keepsAP`,
`fromConst_machine_keepsAP`, `fromConst_frontends_keepsCP` (generic stable `I`, translator `RecA`),
`fromConst_frontends_of_handlers` (translator from the five handler premises at generic `I`),
`bodyKeepsA_frontends`, `bodyStepA_of_handlers` (at `JQ O.quiet D`).

PREMISES (each named after one thing): `LegacyImplA`, `LegacyCachedA`, `CanonKeyA`,
`ProjFieldNameA`, `ChildEntryA` (translator, generic `I`; `ChildKeepsA O D` at `JQ`),
`ChildSynthA O I` (the machine branch's calls `synthesizeChild c` themselves — the synthesis ref is read
inside `closeInstsM`, and `childSynthEntry`'s read has an opaque result world, so `ChildEntryA` does not
give it; at `JQ O.quiet D` it is `ChildKeepsA O D` verbatim), and `LegacyTailA` — ONLY for constants on
which both gates miss and `machineShape?`/`synthesizeMachineCertified` fall through. `LegacyTailA` is a
premise about EVERY such constant, so it stays in the statement even when the constant at hand
takes the machine route successfully.

OPEN (as of this integration, poc after 0054b6b2): the legacy tail `LegacyTailA`; the handler
premises `LegacyImplA`, `LegacyCachedA`, `CanonKeyA` (units A/B work on them, NOT discharged);
`ProjFieldNameA` has a proof only from the ADDED, unproved boundary `T : RefLawsATele`
(Tools/ShippingChildProjFieldA.lean); `ChildEntryA` vs `ChildSynthA`: a bridge removing the
redundant hypothesis is removed by `childEntryA_of_childSynthA` (D2). -/

namespace Tools.ShippingChildFrontCP
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
open Tools.ShippingChildTranslatePathA
open Tools.ShippingChildFallbackA
open Tools.ShippingChildFrontA
open Tools.ShippingChildDepthA

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

section Walk
variable (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
  {I : Void IO.RealWorld → Prop} (hS : StableA O.quiet I)
include O hA hS

/-- `bindMixedCertifiedInputs` preserves `KeepsCP`. -/
theorem bindMixedCertifiedInputsAP {α : Type} (k : CompilerM α)
    (hk : KeepsCP mctx mref cctx cref I k) :
    ∀ l : List ((Name × MixedGateBinder) × FVarId),
      KeepsCP mctx mref cctx cref I (bindMixedCertifiedInputs k l)
  | [] => by unfold bindMixedCertifiedInputs; exact hk
  | ((_, .domain), _) :: rest => by
    unfold bindMixedCertifiedInputs
    exact bindMixedCertifiedInputsAP k hk rest
  | ((_, .bool), _) :: rest => by
    unfold bindMixedCertifiedInputs
    exact bindInputPortAP O hA hS _ _ _ _ (bindMixedCertifiedInputsAP k hk rest)
  | ((_, .bits _), _) :: rest => by
    unfold bindMixedCertifiedInputs
    exact bindInputPortAP O hA hS _ _ _ _ (bindMixedCertifiedInputsAP k hk rest)

/-- **`synthesizeMixedCertified` from the RESTRICTED translator.** -/
theorem mixed_keepsAP (translate : TranslateFn) (b : Bool) (declName : Name)
    (bs : List (Name × MixedGateBinder)) (body : Lean.Expr)
    (htr : ∀ e hint top named, KeepsCP mctx mref cctx cref I (translate e hint top named)) :
    Keeps mctx mref cctx cref I
      (synthesizeMixedCertified translate (profLogIO b) declName bs body) := by
  rw [keeps_iff]
  unfold synthesizeMixedCertified
  refine Triple.bind
    (Triple.mapM _ (fun _ => keeps_iff.mp (keepsA_framed O hA hS FramedA.freshFVar)) _) ?_
  intro ids
  split
  · dsimp only
    refine Triple.bindQ (φ := MkRefd _) (tripleA_mkExprCache O hA hS _) ?_
    intro cacheRef hr
    refine Triple.bind
      (keeps_iff.mp (bindMixedCertifiedInputsAP O hA hS _
        (emitLeavesAP O hA hS translate b cacheRef hr htr _ _ _) _ _ _
        (ctxOk_entry false hr))) ?_  -- guess: R2
    rintro ⟨_, fs⟩
    exact finishSynthA declName fs
  · exact Triple.throw _ fun _ hw => ⟨hw, by okmsg⟩

/-- **`synthesizeMachineCertified`**: the mixed harness, the pure closings, the child calls. -/
theorem machineCert_keepsAP (translate : TranslateFn) (b : Bool) (declName : Name)
    (htr : ∀ e hint top named, KeepsCP mctx mref cctx cref I (translate e hint top named))
    (hchild : ∀ c, Keeps mctx mref cctx cref I (synthesizeChild c))
    (hsv : ∀ w, I w → sv w = some synthesizeChild) (shape : MachineShape) :
    Keeps mctx mref cctx cref I
      (synthesizeMachineCertified translate (profLogIO b) declName shape) := by
  rw [keeps_iff]
  unfold synthesizeMachineCertified
  refine Triple.bind
    (keeps_iff.mp (mixed_keepsAP O hA hS translate b declName shape.binders shape.body htr)) ?_
  rintro ⟨t, d⟩
  dsimp only
  split
  · split
    · exact Triple.pure fun _ hw => hw
    · split
      · exact keeps_iff.mp (closeInstsM_keepsA O hA hS hsv hchild _ _ _ _)
      · exact keeps_iff.mp (closeInstsGM_keepsA O hA hS hsv hchild _ _ _ _)
  · exact Triple.pure fun _ hw => hw

/-- The mixed branch of `synthesizeFromConst`. -/
theorem fromConst_mixed_keepsAP (translate : TranslateFn) (b : Bool) (declName : Name)
    (constInfo : ConstantInfo) (isInst : Lean.Expr → Bool) {bs : List (Name × MixedGateBinder)}
    {body : Lean.Expr}
    (hc : certifiedShape? false [] constInfo = none)
    (hm : mixedCertifiedShape? false [] constInfo isInst = some (bs, body))
    (htr : ∀ e hint top named, KeepsCP mctx mref cctx cref I (translate e hint top named)) :
    Keeps mctx mref cctx cref I
      (synthesizeFromConst translate (profLogIO b) declName [] false true constInfo isInst) := by
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
    | refine Keeps.bind (keepsA_diag O hA hS (Diag.profLog b _)) ?_
    | (dsimp only; refine Keeps.bind (keepsA_diag O hA hS (Diag.profLog b _)) ?_)
  intro _
  refine Keeps.bind (mixed_keepsAP O hA hS translate b declName bs body htr) ?_
  intro result
  refine Keeps.bind (keepsA_framed O hA hS (FramedA.sideModify _ .subModule)) ?_
  intro _
  exact Keeps.pure _

/-- Both gates miss: the machine branch; the fall-through is `hlegacy` (the entry with the
certified front end OFF). Copy of `fromConst_machine_keepsA` (same walk). -/
theorem fromConst_machine_keepsAP (translate : TranslateFn) (b : Bool) (declName : Name)
    (constInfo : ConstantInfo) (isInst : Lean.Expr → Bool)
    (hc : certifiedShape? false [] constInfo = none)
    (hm : mixedCertifiedShape? false [] constInfo isInst = none)
    (htr : ∀ e hint top named, KeepsCP mctx mref cctx cref I (translate e hint top named))
    (hchild : ∀ c, Keeps mctx mref cctx cref I (synthesizeChild c))
    (hsv : ∀ w, I w → sv w = some synthesizeChild)
    (hlegacy : Keeps mctx mref cctx cref I
      (synthesizeFromConst translate (profLogIO b) declName [] false false constInfo isInst)) :
    Keeps mctx mref cctx cref I
      (synthesizeFromConst translate (profLogIO b) declName [] false true constInfo isInst) := by
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
  refine Keeps.bind (keepsA_framed O hA hS FramedA.env) (fun env => ?_)
  generalize machineShape? false [] constInfo (structEnv env) = m
  cases m with
  | none =>
    first
      | exact h
      | exact keeps_pure_bind_of h
  | some shape =>
    refine keeps_pure_bind_of ?_
    refine Keeps.bind (machineCert_keepsAP O hA hS translate b declName htr hchild hsv shape) ?_
    intro r
    cases r with
    | some result =>
      refine Keeps.bind (keepsA_diag O hA hS (Diag.profLog b _)) ?_
      intro _
      refine Keeps.bind (keepsA_framed O hA hS (FramedA.sideModify _ .subModule)) ?_
      intro _
      exact Keeps.pure _
    | none => exact h

/-- **The three front ends with the restricted translator** (certified: TranslatePathA). -/
theorem fromConst_frontends_keepsCP' (translate : TranslateFn) (b : Bool) (declName : Name)
    (constInfo : ConstantInfo) (isInst : Lean.Expr → Bool)
    (htr : ∀ e hint top named, KeepsCP mctx mref cctx cref I (translate e hint top named))
    (hchild : ∀ c, Keeps mctx mref cctx cref I (synthesizeChild c))
    (hsv : ∀ w, I w → sv w = some synthesizeChild)
    (hlegacy : certifiedShape? false [] constInfo = none →
      mixedCertifiedShape? false [] constInfo isInst = none →
      Keeps mctx mref cctx cref I
        (synthesizeFromConst translate (profLogIO b) declName [] false false constInfo isInst)) :
    Keeps mctx mref cctx cref I
      (synthesizeFromConst translate (profLogIO b) declName [] false true constInfo isInst) := by
  cases hc : certifiedShape? false [] constInfo with
  | some p =>
    obtain ⟨bs, body⟩ := p
    exact fromConst_certified_keepsAP O hA hS translate b declName constInfo isInst hc htr
  | none =>
    cases hm : mixedCertifiedShape? false [] constInfo isInst with
    | some p =>
      obtain ⟨bs, body⟩ := p
      exact fromConst_mixed_keepsAP O hA hS translate b declName constInfo isInst hc hm htr
    | none =>
      exact fromConst_machine_keepsAP O hA hS translate b declName constInfo isInst hc hm htr
        hchild hsv (hlegacy hc hm)

end Walk

/-! ## Generic `I`: the statements of INTERFACES.md -/

/-- The machine branch's own child calls (`closeInstsM`/`closeInstsGM` call `synthesizeChild`
after reading the synthesis ref): at `JQ O.quiet D` this is `ChildKeepsA O D`. -/
def ChildSynthA (O : RefLawsAOps MkRefd mref cref) (I : Void IO.RealWorld → Prop) : Prop :=
  ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx →
    ∀ c, Keeps mctx mref cctx cref I (synthesizeChild c)

/-- **D2-1: `ChildEntryA O I` from `ChildSynthA O I`.** `childSynthEntry c` reads the synthesis ref
(framed, so `I` is kept) and calls the value read; `hsv` says that value, read under `I`, is
`synthesizeChild`. The read's result is `readOf sparkleChildSynth w = sv w` (`runsTo_get_readOf`,
no law), so the world after the read is not opaque for the RESULT once `I` pins `sv`. -/
theorem childEntryA_of_childSynthA (O : RefLawsAOps MkRefd mref cref) {I : Void IO.RealWorld → Prop}
    (hS : StableA O.quiet I) (hsv : ∀ w, I w → sv w = some synthesizeChild)
    (hC : ChildSynthA O I) : ChildEntryA O I := by
  intro mctx cctx hA c
  rw [keeps_iff]
  unfold childSynthEntry
  have hread : Triple mctx mref cctx cref I (sparkleChildSynth.get : MetaM _)
      (fun s w => I w ∧ s = some synthesizeChild) (fun e w => I w ∧ OkExc e) := by
    intro w hw
    have hK := keeps_iff.mp (keepsA_framed O hA hS FramedA.synthGet) w hw
    cases hm : (sparkleChildSynth.get : MetaM _) mctx mref cctx cref w with
    | ok a w1 =>
      rw [hm] at hK
      exact ⟨hK, (runsTo_get_readOf _ hm).trans (hsv w hw)⟩
    | error e w1 => rw [hm] at hK; exact hK
  refine Triple.bindQ hread ?_
  · intro s hs
    subst hs
    exact keeps_iff.mp (hC mctx cctx hA c)

/-- At `JQ O.quiet D`: `ChildEntryA` from `ChildKeepsA O D` (= `ChildSynthA O (JQ O.quiet D)`),
`hsv` being `JQ`'s second component. -/
theorem childEntryA_JQ_of_childSynthA (O : RefLawsAOps MkRefd mref cref) (D : Nat)
    (hC : ChildKeepsA O D) : ChildEntryA O (JQ O.quiet D) :=
  childEntryA_of_childSynthA O (stableA_JQ _ D) (fun _ h => h.2.1) hC

/-- At `JQC O D` (unit E plugs in `ChildKeepsC O D` as `ChildSynthA O (JQC O D)`): `hsv` is the
`JQ` half of `JQC`. -/
theorem childEntryA_JQC_of_childSynthA (O : RefLawsAOps MkRefd mref cref) (D : Nat)
    (hC : ChildSynthA O (Tools.ShippingChildCacheA.JQC O D)) :
    ChildEntryA O (Tools.ShippingChildCacheA.JQC O D) :=
  childEntryA_of_childSynthA O (Tools.ShippingChildCacheA.stableA_JQC O D) (fun _ h => h.1.2.1) hC

/-- **`fromConst_frontends_keepsCP`**: the three front ends, generic stable `I`, translator in
the restricted `RecA` form. `hlegacy` only for constants on which both gates miss. -/
theorem fromConst_frontends_keepsCP (O : RefLawsAOps MkRefd mref cref)
    (hA : AdmCtx O.quiet mctx cctx) {I : Void IO.RealWorld → Prop} (hS : StableA O.quiet I)
    (translate : TranslateFn) (htr : RecA O I translate) (hchild : ChildSynthA O I)
    (hsv : ∀ w, I w → sv w = some synthesizeChild)
    (b : Bool) (declName : Name) (constInfo : ConstantInfo) (isInst : Lean.Expr → Bool)
    (hlegacy : certifiedShape? false [] constInfo = none →
      mixedCertifiedShape? false [] constInfo isInst = none →
      Keeps mctx mref cctx cref I
        (synthesizeFromConst translate (profLogIO b) declName [] false false constInfo isInst)) :
    Keeps mctx mref cctx cref I
      (synthesizeFromConst translate (profLogIO b) declName [] false true constInfo isInst) :=
  fromConst_frontends_keepsCP' O hA hS translate b declName constInfo isInst (htr mctx cctx hA)
    (hchild mctx cctx hA) hsv hlegacy

/-- **D2, generic `I`**: the translator `translateExprToWire tenv` from the five handler premises. -/
theorem fromConst_frontends_of_handlers (O : RefLawsAOps MkRefd mref cref)
    (hA : AdmCtx O.quiet mctx cctx) {I : Void IO.RealWorld → Prop} (hS : StableA O.quiet I)
    (hImpl : LegacyImplA O I) (hCached : LegacyCachedA O I) (hcanon : CanonKeyA O I)
    (hpf : ProjFieldNameA O I) (hchild : ChildSynthA O I)
    (hsv : ∀ w, I w → sv w = some synthesizeChild)
    (tenv : Lean.Environment) (b : Bool) (declName : Name) (constInfo : ConstantInfo)
    (isInst : Lean.Expr → Bool)
    (hlegacy : certifiedShape? false [] constInfo = none →
      mixedCertifiedShape? false [] constInfo isInst = none →
      Keeps mctx mref cctx cref I
        (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b)
          declName [] false false constInfo isInst)) :
    Keeps mctx mref cctx cref I
      (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b)
        declName [] false true constInfo isInst) :=
  fromConst_frontends_keepsCP O hA hS _
    (translate_keepsA O hS tenv hImpl hCached hcanon hpf
      (childEntryA_of_childSynthA O hS hsv hchild)) hchild hsv b declName constInfo
    isInst hlegacy

/-! ## At `JQ O.quiet D`: the body for every route but the legacy tail -/

/-- The legacy tail at depth `D`: the entry with the certified front end OFF keeps `JQ O.quiet D`.
PREMISE, asked only of constants on which both gates miss. -/
def LegacyTailA (O : RefLawsAOps MkRefd mref cref) (D : Nat) : Prop :=
  ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx →
    ∀ (declName : Name) (tenv : Lean.Environment) (b : Bool) (ci : ConstantInfo)
      (isInst : Lean.Expr → Bool),
    certifiedShape? false [] ci = none → mixedCertifiedShape? false [] ci isInst = none →
    Keeps mctx mref cctx cref (JQ O.quiet D)
      (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b)
        declName [] false false ci isInst)

/-- **The body at depth `D` for the certified, mixed and machine routes** (legacy tail: premise). -/
theorem bodyKeepsA_frontends (O : RefLawsAOps MkRefd mref cref) (D : Nat)
    (hImpl : LegacyImplA O (JQ O.quiet D)) (hCached : LegacyCachedA O (JQ O.quiet D))
    (hcanon : CanonKeyA O (JQ O.quiet D)) (hpf : ProjFieldNameA O (JQ O.quiet D))
    (hC : ChildKeepsA O D) (hlegacy : LegacyTailA O D) : BodyKeepsA O D := by
  intro mctx cctx hA declName tenv b ci isInst
  exact fromConst_frontends_of_handlers O hA (stableA_JQ _ D) hImpl hCached hcanon hpf
    hC (fun _ h => h.2.1) tenv b declName ci isInst
    (hlegacy mctx cctx hA declName tenv b ci isInst)

/-- **`BodyStepA O`** from the per-handler premises (every depth) and the legacy tail. -/
theorem bodyStepA_of_handlers (O : RefLawsAOps MkRefd mref cref)
    (hImpl : ∀ D, LegacyImplA O (JQ O.quiet D)) (hCached : ∀ D, LegacyCachedA O (JQ O.quiet D))
    (hcanon : ∀ D, CanonKeyA O (JQ O.quiet D)) (hpf : ∀ D, ProjFieldNameA O (JQ O.quiet D))
    (hlegacy : ∀ D, LegacyTailA O D) : BodyStepA O :=
  fun D _ hC => bodyKeepsA_frontends O D (hImpl D) (hCached D) (hcanon D) (hpf D) hC (hlegacy D)

/-- Mixed route only (no legacy tail asked): extends `bodyStepA_certified`. -/
theorem bodyStepA_mixed (O : RefLawsAOps MkRefd mref cref) (D : Nat)
    (hImpl : LegacyImplA O (JQ O.quiet D)) (hCached : LegacyCachedA O (JQ O.quiet D))
    (hcanon : CanonKeyA O (JQ O.quiet D)) (hpf : ProjFieldNameA O (JQ O.quiet D))
    (hC : ChildKeepsA O D) (mctx : Meta.Context) (cctx : Core.Context)
    (hA : AdmCtx O.quiet mctx cctx) (declName : Name) (tenv : Lean.Environment) (b : Bool)
    (ci : ConstantInfo) (isInst : Lean.Expr → Bool) {bs : List (Name × MixedGateBinder)}
    {body : Lean.Expr} (hc : certifiedShape? false [] ci = none)
    (hm : mixedCertifiedShape? false [] ci isInst = some (bs, body)) :
    Keeps mctx mref cctx cref (JQ O.quiet D)
      (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b)
        declName [] false true ci isInst) :=
  fromConst_mixed_keepsAP O hA (stableA_JQ _ D) _ b declName ci isInst hc hm
    (translate_keepsJQ O D tenv hImpl hCached hcanon hpf hC mctx cctx hA)

/-- Machine route (both gates miss), fall-through premise `hlegacy` for this constant only. -/
theorem bodyStepA_machine (O : RefLawsAOps MkRefd mref cref) (D : Nat)
    (hImpl : LegacyImplA O (JQ O.quiet D)) (hCached : LegacyCachedA O (JQ O.quiet D))
    (hcanon : CanonKeyA O (JQ O.quiet D)) (hpf : ProjFieldNameA O (JQ O.quiet D))
    (hC : ChildKeepsA O D) (mctx : Meta.Context) (cctx : Core.Context)
    (hA : AdmCtx O.quiet mctx cctx) (declName : Name) (tenv : Lean.Environment) (b : Bool)
    (ci : ConstantInfo) (isInst : Lean.Expr → Bool)
    (hc : certifiedShape? false [] ci = none) (hm : mixedCertifiedShape? false [] ci isInst = none)
    (hlegacy : Keeps mctx mref cctx cref (JQ O.quiet D)
      (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b)
        declName [] false false ci isInst)) :
    Keeps mctx mref cctx cref (JQ O.quiet D)
      (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b)
        declName [] false true ci isInst) :=
  fromConst_machine_keepsAP O hA (stableA_JQ _ D) _ b declName ci isInst hc hm
    (translate_keepsJQ O D tenv hImpl hCached hcanon hpf hC mctx cctx hA)
    (hC mctx cctx hA) (fun _ h => h.2.1) hlegacy

end Tools.ShippingChildFrontCP
