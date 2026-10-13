import Tools.ShippingWalkGrow
import Tools.ShippingInstanceTag

/-! # The instance arm over a captured environment, in the growing-cache calculus

WRITTEN, NOT BUILT (`fix/inst-arm-env`, an ISOLATED proposal). About
`translateInstanceArmWith env rec` — the instance arm that takes the
environment as an ARGUMENT (`Sparkle/Compiler/Elab.lean`, this branch only;
`docs/parallel/ENV-capture-proposal.md`). The arm of poc,
`translateInstanceOrFallback`, reads the environment itself, and no built law
relates that read to the entry's (`docs/parallel/B-slotless-parents-2.md`
§11); with the environment an argument the tag is a fact about a VALUE.

What is here:

* `spine_tag` — PURE. An expression the predicate of `env` designates, whose
  spine is a constant applied to input binders (`unifiedInstanceSpine`), has
  its head constant tagged in `env`. The predicate's second disjunct (a
  structure projection of a tagged record) is excluded by the spine itself:
  the last argument is a bound variable, not a call. So for the canonical
  instance root the tag in the entry's environment follows from the gate's
  acceptance alone, with no premise about the environment.
  `spineRoot_tag` — the same from `unifiedInstanceRoot … = true` and the
  spine disjunct. (For the pipeline root `hierInstRoot` the second disjunct
  is not excluded by the shape: `Tools.ShippingInstanceTag.root_tag` gives
  the disjunction there.)
* `armCont` — the arm's continuation after the child's synthesis, as a
  definition, and `armCont_keepsC`, `translateInstanceArmWith_keepsC` (the
  invariant side, by the walk `vc`, under the hypotheses of the built
  `translateInstanceOrFallback_keepsC`).
* `translateFallbackE_keepsC`, `translateExprToWireE_keepsC` — the whole
  translator over a captured environment keeps the invariant (the fuel
  induction of the built `translateRel_of_legacy`, with the captured arm).
* `instanceArm_grow` — the arm in `WG`: from an invariant world of positive
  depth, a returning run of the arm on a call whose head `mn` is tagged in
  the captured environment ends in an invariant world of the same depth
  whose cache contains the start cache, and there is a pair `y` such that
  `y` is a `RealChild` of `mn` (a run of the real full entry over these
  references), `y` is THE entry of `mn` in the end cache, and the wire is
  what `armCont rec mn y …` returned (a `Returns`: the door to the built
  shape lemmas, which analyse exactly that program).

No `HardwareTagged`, no `SubSynthDefines`: the tag is a hypothesis about the
value `env`, the child is the run's own.

NOT here: `gate_parent_run`. Its exact statement and what it still needs are
in `docs/parallel/ENV-capture-proposal.md` §6. -/

namespace Tools.ShippingInstanceTag
open Lean Sparkle.Compiler.Elab

/-- **The tag of a canonical call, from the predicate alone.** -/
theorem spine_tag {env : Environment} {kinds : Array MixedGateBinder} {e : Lean.Expr}
    {mn : Name} {us : List Level} (hfn : e.getAppFn = .const mn us)
    (happ : e.isApp = true) (hsp : unifiedInstanceSpine kinds e = true)
    (h : instancePredicate env e = true) :
    Sparkle.Compiler.isHardwareModule env mn = true := by
  cases e with
  | app f a =>
    cases a with
    | bvar i =>
      unfold instancePredicate at h
      rw [hfn] at h
      dsimp only at h
      rw [Bool.or_eq_true] at h
      rcases h with ht | hp
      · exact ht
      · exfalso
        cases hs : env.getProjectionStructureName? mn with
        | none =>
          rw [hs] at hp
          simp at hp
        | some s =>
          rw [hs] at hp
          simp [Lean.Expr.getAppFn] at hp
    | _ => first | cases hsp | (simp [unifiedInstanceSpine] at hsp)
  | _ => first | cases happ | (simp [Lean.Expr.isApp] at happ)

/-- The canonical instance root (`unifiedInstanceRoot`, its spine disjunct)
accepted under the predicate of `envR`: the head is tagged in `envR`. -/
theorem spineRoot_tag {envR : Environment} {kinds : Array MixedGateBinder} {e : Lean.Expr}
    {mn : Name} {us : List Level} (hfn : e.getAppFn = .const mn us)
    (h : unifiedInstanceRoot (instancePredicate envR) kinds e = true)
    (hsp : unifiedInstanceSpine kinds e = true) :
    Sparkle.Compiler.isHardwareModule envR mn = true := by
  have hi : instancePredicate envR e = true := unifiedInstanceRoot_isInst h
  have happ : e.isApp = true := by
    unfold unifiedInstanceRoot at h
    simp only [Bool.and_eq_true] at h
    exact h.1.2
  exact spine_tag hfn happ hsp hi

end Tools.ShippingInstanceTag

namespace Tools.ShippingChildInv
open Lean Meta
open Tools.ShippingEntrySoundness
open Sparkle.Compiler.Elab

/-- The instance arm after the child's synthesis returned `sub`: a child
with one output takes the certified lowering under the validated cache
wrapper, any other the legacy translator. (The text of
`translateInstanceArmWith` after its `let sub ← …`.) -/
def armCont (rec : TranslateFn) (mn : Name)
    (sub : Sparkle.IR.AST.Module × Sparkle.IR.AST.Design) (e : Lean.Expr) (hint : String)
    (top named : Bool) : CompilerM String :=
  match sub.1.outputs with
  | [singleOut] =>
    translateControlCachedWith
      (translateInstanceUncachedWith rec mn sub.1 sub.2 singleOut)
      e hint top named
  | _ => Rec.translateExprToWireCached (fun e h t n => rec e h t n) e hint top named

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
variable (L : RefLaws mref cref) (D : Nat)

section CapturedArm
variable (rec : TranslateFn)
  (hrec : ∀ (mctx : Meta.Context) (cctx : Core.Context) e hint top named,
    KeepsC mctx mref cctx cref (J L D) (rec e hint top named))
  (hC : ChildKeeps L D)
  (hlegC : ∀ e hint top named, KeepsC mctx mref cctx cref (J L D)
    (Rec.translateExprToWireCached (fun e h t n => rec e h t n) e hint top named))
  (hlegI : ∀ e hint top named, KeepsC mctx mref cctx cref (J L D)
    (Rec.translateExprToWireImpl (fun e h t n => rec e h t n) e hint top named))
include hrec hC hlegC

set_option linter.unusedSectionVars false in
/-- The continuation keeps the invariant (the walk of the built
`translateInstanceOrFallback_keepsC`, from the child's result on). -/
theorem armCont_keepsC (mn : Name) (sub : Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)
    (e : Lean.Expr) (hint : String) (top named : Bool) :
    KeepsC mctx mref cctx cref (J L D) (armCont rec mn sub e hint top named) := by
  vc

set_option linter.unusedSectionVars false in
/-- **The instance arm over a captured environment keeps the invariant**:
the child's synthesis (`childSynthEntry`), the single-output and the
projection lowerings under the validated cache wrapper, or the legacy
translator — the walk of `translateInstanceOrFallback_keepsC` without the
environment read. -/
theorem translateInstanceArmWith_keepsC (env : Environment) (e : Lean.Expr) (hint : String)
    (top named : Bool) :
    KeepsC mctx mref cctx cref (J L D) (translateInstanceArmWith env rec e hint top named) := by
  vc

include hlegI

set_option linter.unusedSectionVars false in
/-- **The fallback over a captured environment**: one arm per `fallbackKind`
(the walk of the built `translateFallback_keepsC`, its last arm the captured
one). -/
theorem translateFallbackE_keepsC (env : Environment) (e : Lean.Expr) (hint : String)
    (top named : Bool) :
    KeepsC mctx mref cctx cref (J L D) (translateFallbackE env rec e hint top named) := by
  vc

end CapturedArm

/-- **The translator over a captured environment keeps the invariant**, from
the legacy translator's relation (the proof of the built
`translateRel_of_legacy`, with `translateFallbackE env` for
`translateFallback`). -/
theorem translateExprToWireE_keepsC (hLg : LegacyRel L) (hC : ChildKeeps L D)
    (env : Environment) :
    ∀ (mctx : Meta.Context) (cctx : Core.Context) e hint top named,
      KeepsC mctx mref cctx cref (J L D) (translateExprToWireE env e hint top named) := by
  intro mctx cctx e hint top named
  unfold translateExprToWireE
  refine fuelFix_keepsC (translateStepWith (translateFallbackE env))
    (fun rec hrec mctx cctx e hint top named => ?_) _ mctx cctx e hint top named
  obtain ⟨h1, h2⟩ := hLg D hC rec hrec mctx cctx
  exact translateStepWith_keepsC L D (translateFallbackE env) rec hrec
    (translateFallbackE_keepsC L D rec hrec hC h1 h2 env) e hint top named

end Tools.ShippingChildInv

namespace Tools.ShippingWalkGrow
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.Builder
open Tools.ShippingEntrySoundness Tools.ShippingChildInv
open Tools.ShippingCacheCoherentRun Tools.ShippingCallsSame

variable {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
variable {L : RefLaws mref cref} {D : Nat} {ctx : CompilerState}

/-- **The instance arm over a captured environment, world-aware.** For a
call whose head `mn` is tagged in the captured `env`: the invariant, the
depth and every cache entry are kept; the child the arm instantiates is a
`RealChild` of `mn` and THE entry of `mn` in the end cache; the returned wire
is the one `armCont rec mn y …` returned for that child.

Hypotheses: `hB` is the proved `bodyRel`; `hrec`, `hC`, `hlegC` are the
hypotheses of the built `translateInstanceOrFallback_keepsC`, for every law
witness (the form `WG.ofKeeps` takes). -/
theorem instanceArm_grow (hB : ∀ L' : RefLaws mref cref, BodyRel L') (hD : D ≠ 0)
    {rec : TranslateFn}
    (hrec : ∀ (L' : RefLaws mref cref) (mctx : Meta.Context) (cctx : Core.Context)
      e hint top named, KeepsC mctx mref cctx cref (J L' D) (rec e hint top named))
    (hC : ∀ L' : RefLaws mref cref, ChildKeeps L' D)
    (hlegC : ∀ (L' : RefLaws mref cref) e hint top named,
      KeepsC mctx mref cctx cref (J L' D)
        (Rec.translateExprToWireCached (fun e h t n => rec e h t n) e hint top named))
    {env : Environment} {e : Lean.Expr} {mn : Name} {us : List Level}
    (hfn : e.getAppFn = .const mn us)
    (htag : Sparkle.Compiler.isHardwareModule env mn = true)
    (hint : String) (top named : Bool) {P : Std.HashMap Lean.Name Res → Prop} :
    WG mctx cctx L D ctx P (translateInstanceArmWith env rec e hint top named)
      (fun wire m => ∃ y : Res, RealChild mref cref mn y ∧ m.get? mn = some y ∧
        ∃ (st s' : CircuitState),
          Tools.ShippingTranslateSoundness.Returns (armCont rec mn y e hint top named)
            ctx st wire s') := by
  intro st w p w' hw hd hp hr
  -- the arm at a tagged constant head: the child's synthesis, then `armCont`
  unfold translateInstanceArmWith at hr
  rw [hfn] at hr
  try dsimp only at hr
  rw [htag] at hr
  simp only [if_true] at hr
  obtain ⟨⟨sub, s1⟩, w1, r1, r2⟩ := RunsTo.bind hr
  -- the child: a `RealChild`, an entry of the cache after it
  obtain ⟨hw1, hd1, hs1, hreal, hget⟩ :=
    (WG.child (L := L) (D := D) (ctx := ctx) (P := P) hB hD mn) st w (sub, s1) w1 hw hd hp r1
  -- the continuation is `armCont` on that child
  have r2' : RunsTo (armCont rec mn sub e hint top named ctx s1) mctx mref cctx cref w1 p w' := r2
  have hk : WG mctx cctx L D ctx (fun m => m.get? mn = some sub)
      (armCont rec mn sub e hint top named) (fun _ _ => True) :=
    WG.ofKeeps (fun L' st =>
      armCont_keepsC L' D rec (hrec L') (hC L') (hlegC L') mn sub e hint top named ctx st)
  obtain ⟨hw2, hd2, hs2, -⟩ := hk s1 w1 p w' hw1 hd1 hget r2'
  exact ⟨hw2, hd2, sub_trans hs1 hs2, sub, hreal, hs2 mn sub hget, s1, p.2,
    ⟨mctx, mref, cctx, cref, w1, w', r2'⟩⟩

/-- `instanceArm_grow` for the canonical instance root: the tag is not a
hypothesis but a consequence of the gate's acceptance of the body `e0`
(binder form) under the predicate of the SAME environment the arm was given.
`e` is the body as the harness translates it (its binders instantiated),
with the same head. -/
theorem instanceArm_grow_of_root (hB : ∀ L' : RefLaws mref cref, BodyRel L') (hD : D ≠ 0)
    {rec : TranslateFn}
    (hrec : ∀ (L' : RefLaws mref cref) (mctx : Meta.Context) (cctx : Core.Context)
      e hint top named, KeepsC mctx mref cctx cref (J L' D) (rec e hint top named))
    (hC : ∀ L' : RefLaws mref cref, ChildKeeps L' D)
    (hlegC : ∀ (L' : RefLaws mref cref) e hint top named,
      KeepsC mctx mref cctx cref (J L' D)
        (Rec.translateExprToWireCached (fun e h t n => rec e h t n) e hint top named))
    {envR : Environment} {kinds : Array MixedGateBinder} {e0 e : Lean.Expr} {mn : Name}
    {us us' : List Level}
    (hfn0 : e0.getAppFn = .const mn us)
    (hroot : unifiedInstanceRoot (instancePredicate envR) kinds e0 = true)
    (hsp : unifiedInstanceSpine kinds e0 = true)
    (hfn : e.getAppFn = .const mn us')
    (hint : String) (top named : Bool) {P : Std.HashMap Lean.Name Res → Prop} :
    WG mctx cctx L D ctx P (translateInstanceArmWith envR rec e hint top named)
      (fun wire m => ∃ y : Res, RealChild mref cref mn y ∧ m.get? mn = some y ∧
        ∃ (st s' : CircuitState),
          Tools.ShippingTranslateSoundness.Returns (armCont rec mn y e hint top named)
            ctx st wire s') :=
  instanceArm_grow hB hD hrec hC hlegC hfn
    (Tools.ShippingInstanceTag.spineRoot_tag hfn0 hroot hsp) hint top named

end Tools.ShippingWalkGrow
