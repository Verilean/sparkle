import Tools.ShippingLegacySemContract

variable {tenv : Lean.Environment}

/-! # The dispatch from the fallback to the legacy inline attempt, in stages

`Tools/ShippingLegacySemContract.lean` takes `ReachesInline rec ctx e` — every
successful run of `translateFallback` on `e` returns the wire of a run of
`Rec.tryInlineUnfold` — as ONE undischarged premise. As stated it has no room
for a cache hit, so it cannot hold for a cacheable call. This file restates
it per call (hint and flags fixed) with the hit as an explicit, VALIDATED
alternative, and splits the dispatch into its stages.

**Statement.** `ReachesAt rec ctx e hint top named`: a successful run of
`translateFallback rec e hint top named` from `s` to `t` returning `w` is

* the wire of a run of the inline attempt from `s` to `t`, or
* a validated hit: `t = s` and the builder state records `w` for `e`
  (`s.translateRecord.get? w = some e` — what `cacheLookupValidated` checks).

**Proved.**

* `inline_at_action` / `inline_step_contract_at` — `ReachesAt` (with the
  expression's `Meaning`, used only by the hit: a record is read back through
  `Meaning`) gives the fallback's `ActionSpec` and the step's `Contract`, like
  `translateFallback_legacy` / `legacy_step_contract` do from `ReachesInline`.
  `reachesAt_of_reachesInline`: the old premise is the special case without
  a hit.
* The first two stages of the dispatch, for a call whose head constant is
  neither tagged `@[hardware_module]` nor a structure projection in the
  environment the run reads (`PlainHead`):
  `fallback_eq_arm` (`fallbackKind e = .other` ⇒ the fallback IS the instance
  arm) and `arm_to_shim` (a run of `translateInstanceOrFallback` is a run of
  the caching shim `Rec.translateExprToWireCached`, same states, same wire).
* `reachesAt_of_stages` — the composition: with the shim stage and the body
  stage, `ReachesAt`.

**Stages taken as premises here.**

* `ShimAt rec ctx e hint top named` — a run of the shim is a run of the body
  `Rec.translateExprToWireImpl`, or a validated hit. For today's shim it is
  derived in `Tools/ShippingLegacySemShim.lean` exactly where it is true: a
  call that is not cacheable (`named`, `top`, or an `fvar`) and a context
  without an expression cache. For a cacheable call under the entry's
  context it is FALSE of today's shim (the hit is the raw `IO.Ref` read) and
  becomes true for every call once the shim validates its hit
  (docs/parallel/G2-legacy.md, the proposal).
* `BodyReachesInline rec ctx e` — a run of the body on `e` returns the wire of
  a run of the inline attempt, same states. NOT proved: it is the walk of the
  body's prefix (trace, call counter, limit, profile tick), its inline arms
  and `Rec.translateExprToWireApp`'s chain, in which each of the eight
  handlers before `Rec.handleDefinitionUnfold` has to be shown to return
  `none` on a plain call, and of `Rec.handleDefinitionUnfold` up to the
  attempt. Nothing in it reads a wire name from an `IO.Ref` before the
  attempt for such a call, so it is a statement `Returns` can express. -/
namespace Tools.ShippingLegacySem
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Builder Sparkle.IR.Semantics
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedMeaning
open Tools.ShippingUnifiedCache Tools.ShippingUnifiedInvariant
open Tools.ShippingTranslateSoundness hiding Inv Spec
open Tools.ShippingCompareLoweringSoundness
open Tools.ShippingEntrySoundness
open Tools.ShippingMixedBinarySoundness (Frame)
open Tools.ShippingUnifiedRecursion
open Tools.ShippingLinkCtx

/-! ## The statement, per call -/

/-- What a successful fallback run on a call the inline arm lowers is: the
inline attempt's wire, or a validated hit. -/
def InlineOrHit (rec : TranslateFn) (ctx : CompilerState) (e : Lean.Expr) (hint : String)
    (named : Bool) (s t : CircuitState) (w : String) : Prop :=
  (∃ r : Option String × Option Exception,
      Returns (Rec.tryInlineUnfold rec e hint named) ctx s r t ∧ r.1 = some w) ∨
    (t = s ∧ s.translateRecord.get? w = some e)

/-- The dispatch fact of one call: hint and flags fixed. -/
def ReachesAt (tenv : Lean.Environment) (rec : TranslateFn) (ctx : CompilerState) (e : Lean.Expr) (hint : String)
    (top named : Bool) : Prop :=
  ∀ (s t : CircuitState) (w : String),
    Returns ((translateFallback tenv) rec e hint top named) ctx s w t →
    InlineOrHit rec ctx e hint named s t w

/-- `ReachesInline` is `ReachesAt` for every call, never by a hit. -/
theorem reachesAt_of_reachesInline {rec : TranslateFn} {ctx : CompilerState} {e : Lean.Expr}
    (h : ReachesInline tenv rec ctx e) (hint : String) (top named : Bool) :
    ReachesAt tenv rec ctx e hint top named := by
  intro s t w hr
  exact Or.inl (h hint top named s t w hr)

/-! ## The stages -/

/-- The environment facts of a plain call: the head constant is not tagged
`@[hardware_module]` and is not a structure projection
* in `tenv`, the environment the translator was built from (the entry's
  read): what the instance arm tests, and
* in every environment a `getEnv` run returns: what the legacy handler
  `handleDefinitionUnfold` tests on its own reads. -/
def PlainHead (tenv : Lean.Environment) (mn : Name) : Prop :=
  (Sparkle.Compiler.isHardwareModule tenv mn = false ∧
    tenv.getProjectionStructureName? mn = none) ∧
  ∀ env, MReturns (Lean.getEnv : MetaM Lean.Environment) env →
    Sparkle.Compiler.isHardwareModule env mn = false ∧
    env.getProjectionStructureName? mn = none

/-- The shim stage of one call: the body's run, or a validated hit. -/
def ShimAt (rec : TranslateFn) (ctx : CompilerState) (e : Lean.Expr) (hint : String)
    (top named : Bool) : Prop :=
  ∀ (s t : CircuitState) (w : String),
    Returns (Rec.translateExprToWireCached (fun e h t n => rec e h t n) e hint top named)
      ctx s w t →
    Returns (Rec.translateExprToWireImpl (fun e h t n => rec e h t n) e hint top named)
      ctx s w t ∨
    (t = s ∧ s.translateRecord.get? w = some e)

/-- The body stage (a premise): the legacy body on `e` returns the inline
attempt's wire. -/
def BodyReachesInline (rec : TranslateFn) (ctx : CompilerState) (e : Lean.Expr) : Prop :=
  ∀ (hint : String) (top named : Bool) (s t : CircuitState) (w : String),
    Returns (Rec.translateExprToWireImpl (fun e h t n => rec e h t n) e hint top named)
      ctx s w t →
    ∃ r : Option String × Option Exception,
      Returns (Rec.tryInlineUnfold rec e hint named) ctx s r t ∧ r.1 = some w

/-- Stage 1: on a `fallbackKind = .other` expression the fallback is the
instance arm (the last line of `instance_step`). -/
theorem fallback_eq_arm (rec : TranslateFn) (e : Lean.Expr) (hint : String) (top named : Bool)
    (hkind : fallbackKind e = .other) :
    (translateFallback tenv) rec e hint top named =
      translateInstanceOrFallback tenv rec e hint top named := by
  simp only [translateFallback, hkind]

/-- Stage 2: for a plain head the instance arm hands the expression to the
caching shim — the environment read leaves the builder state, the tag test
and the projection test fail. (The walk of
`synthesizeMixedCertified_instanceProj_sound`, on the branch it does not
take.) -/
theorem arm_to_shim {rec : TranslateFn} {e : Lean.Expr} {mn : Name} {us : List Level}
    {hint : String} {top named : Bool} {ctx : CompilerState} {s t : CircuitState} {w : String}
    (hfn : e.getAppFn = .const mn us) (hplain : PlainHead tenv mn)
    (tr : Returns (translateInstanceOrFallback tenv rec e hint top named) ctx s w t) :
    Returns (Rec.translateExprToWireCached (fun e h t n => rec e h t n) e hint top named)
      ctx s w t := by
  unfold translateInstanceOrFallback at tr
  rw [hfn] at tr
  -- the environment read: its value `env`, and the builder state unchanged.
  -- The continuation gets a NEW name: `tr` still holds the whole program.
  change Returns (if Sparkle.Compiler.isHardwareModule tenv mn = true then _ else _) _ _ _ _ at tr
  have k1 := tr
  obtain ⟨⟨hnotTag, hprojS⟩, -⟩ := hplain
  rw [hnotTag] at k1
  simp only [Bool.false_eq_true, if_false] at k1
  rw [hprojS] at k1
  first
    | exact k1
    | (simp only [] at k1; exact k1)
    | (split at k1 <;> first | exact k1 | contradiction | simp_all)

/-- **The dispatch, composed**: for a plain call of kind `.other`, the shim
stage and the body stage give `ReachesAt`. -/
theorem reachesAt_of_stages {rec : TranslateFn} {ctx : CompilerState} {e : Lean.Expr}
    {mn : Name} {us : List Level} {hint : String} {top named : Bool}
    (hkind : fallbackKind e = .other) (hfn : e.getAppFn = .const mn us)
    (hplain : PlainHead tenv mn) (shim : ShimAt rec ctx e hint top named)
    (body : BodyReachesInline rec ctx e) :
    ReachesAt tenv rec ctx e hint top named := by
  intro s t w hr
  rw [fallback_eq_arm rec e hint top named hkind] at hr
  have hshim := arm_to_shim hfn hplain hr
  rcases shim s t w hshim with hbody | hhit
  · exact Or.inl (body hint top named s t w hbody)
  · exact Or.inr hhit

set_option linter.unusedSectionVars false

variable [LinkCtx] [ChildSem]

/-! ## From the dispatch fact to the contract -/

/-- **The fallback on a call the inline arm lowers, hit included.** An inline
run gives the unfolding's contract (`tryInlineUnfold_returns`); a validated
hit gives the recorded wire's value from the invariant's records, with the
state unchanged. -/
theorem inline_at_action {rec : TranslateFn} {ctx : CompilerState}
    {inputs : FVarId → Option Value} {we : WEnv} {mems : MEnv} {initial : Env}
    {e : Lean.Expr} {v : Value} {hint : String} {top named : Bool}
    (meaning : Meaning inputs e v)
    (reach : ReachesAt tenv rec ctx e hint top named)
    (sub : ∀ e' : Lean.Expr, InlineUnfolds e e' → Contract rec ctx inputs we mems initial e' v) :
    ActionSpec ((translateFallback tenv) rec e hint top named) ctx inputs we mems initial v := by
  constructor
  · intro s t w lookup hr
    have hh := reach s t w hr
    unfold InlineOrHit at hh
    rcases hh with ⟨r, hrun, hres⟩ | ⟨hts, _⟩
    · obtain ⟨e', hU, htr⟩ := tryInlineUnfold_returns hrun hres
      exact (sub e' hU).frame hint false named s t w lookup htr
    · rw [hts]
      exact Frame.refl s
  · intro s t w prior h widths hr
    have hh := reach s t w hr
    unfold InlineOrHit at hh
    rcases hh with ⟨r, hrun, hres⟩ | ⟨hts, hrec⟩
    · obtain ⟨e', hU, htr⟩ := tryInlineUnfold_returns hrun hres
      exact (sub e' hU).sem hint false named s t w prior h widths htr
    · obtain ⟨used, value, width⟩ := h.records w e hrec v meaning
      rw [hts]
      exact ⟨used, width, fun _ hu => hu, prior, h, value, fun _ _ => rfl⟩

/-- **One step on such a call** meets the certified contract, from the
dispatch fact of every call. -/
theorem inline_step_contract_at {rec : TranslateFn} {ctx : CompilerState}
    {inputs : FVarId → Option Value} {we : WEnv} {mems : MEnv} {initial : Env}
    {e : Lean.Expr} {v : Value} (nc : NotCore e) (meaning : Meaning inputs e v)
    (reach : ∀ (hint : String) (top named : Bool), ReachesAt tenv rec ctx e hint top named)
    (sub : ∀ e' : Lean.Expr, InlineUnfolds e e' → Contract rec ctx inputs we mems initial e' v) :
    Contract (translateStepWith (translateFallback tenv) rec) ctx inputs we mems initial e v := by
  constructor
  · intro hint top named s t w lookup hr
    rw [step_eq_fallback rec e hint top named nc.shape (nc.core rec hint top named)] at hr
    exact (inline_at_action meaning (reach hint top named) sub).frame s t w lookup hr
  · intro hint top named s t w prior h widths hr
    rw [step_eq_fallback rec e hint top named nc.shape (nc.core rec hint top named)] at hr
    exact (inline_at_action meaning (reach hint top named) sub).sem s t w prior h widths hr

end Tools.ShippingLegacySem
