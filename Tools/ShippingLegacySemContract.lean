import Tools.ShippingLegacySemInline

variable {tenv : Lean.Environment}

/-! # The simulation contract of the legacy route, in the certified translator's form

The certified arms are proved against `Contract`
(`Tools/ShippingUnifiedRecursion.lean`): for an expression `e` with source
value `v`, every successful run of the translator on `e` extends the builder
state by a frame, and from an invariant state (`Inv`) ends in one where the
returned wire carries `v` and every earlier wire is unchanged (`Outcome`).
`fuel_contract_leaves` closes the fuel induction for the quoted fragment.
What the legacy route emits has no such statement: `legacyRel` /
`bodyRel` are `Keeps` statements about the child cache (audit §4, G2).

This file states, over the SAME types, what a legacy arm has to satisfy for
the two to compose in one induction, and proves it for one arm.

**Definitions (the contract).**

* `RecSound Dom rec …` — the translator `rec` meets `Contract` on every
  `(e, v)` of a domain `Dom`.
* `fuel_of_step` — the fuel induction in the general form: IF one step
  `translateStepWith translateFallback` carries `RecSound Dom` from its
  recursive argument to itself, THEN `translateFuelFix translateStep fuel`
  (and so `translateExprToWire`) meets `Contract` on `Dom`, at every fuel.
  The certified proof's `succ` case is such a step for the quoted fragment.
* `LegacySem Dom …` — the same statement for the legacy translator's body
  `Rec.translateExprToWireImpl`, relative to its recursive argument: the
  semantic analogue of `LegacyRel`. STATED, NOT PROVED.
* `LegacyArm rec … e v` — one constructor per legacy handler proved to meet
  the contract: the handler's control-flow fact about `translateFallback` on
  `e`, and `Contract` for the sub-expressions the handler translates.

**Proved.**

* `translateFallback_legacy` — ONE theorem about `translateFallback`: an
  expression in a `LegacyArm` gets the fallback's `ActionSpec` (frame and
  semantic outcome) for every hint and flag. A further handler is a further
  constructor of `LegacyArm` and a further case of this theorem.
* `legacy_step_contract` — the step `translateStepWith translateFallback rec`
  meets `Contract` on such an expression when the core declines it.
* `legacy_fuel_contract` / `legacy_translate_contract` — one induction over
  `LegacyDom`, in which input binders, EVERY certified operator of the quoted
  fragment (over arbitrary leaves) and the legacy inline arm nest in any
  order: `translateExprToWire` meets `Contract` on every such expression.

**The arm proved: definition unfolding** (`LegacyArm.inlineUnfold`,
`Rec.tryInlineUnfold`). Its semantic step — the wire is one translation of an
unfolding, from the attempt's own start state, through both `catch`es — is
`tryInlineUnfold_returns` (`Tools/ShippingLegacySemInline.lean`).

**Premises that remain, and are NOT discharged here.**

* `ReachesInline rec ctx e`: every successful run of `translateFallback` on
  `e` returns the wire of a run of the inline attempt, from the same state to
  the same state. It is the dispatch walk (`translateInstanceOrFallback`, the
  caching shim `Rec.translateExprToWireCached`, the prefix of
  `Rec.translateExprToWireImpl`, `Rec.translateExprToWireApp`'s handler chain,
  `Rec.handleDefinitionUnfold` up to the attempt). With the expression cache
  enabled (`ctx.exprCache = some _`, which the entry always sets) it is NOT
  provable for a cacheable call: the shim returns whatever the `IO.Ref` map
  holds for the expression, unvalidated, and `Returns` says nothing of the
  world. See `docs/parallel/G2-legacy.md` for what has to change.
* `NotCore e`: the core's two syntactic tests decline `e` (decidable facts of
  the expression, `rfl` per shape as in `instance_step`).
* For every unfolding the oracles may return, membership in the domain WITH
  THE SAME VALUE. That an unfolding has the call's source value is Lean's
  definitional unfolding in the run's environment — reflection, not proved.
* The contract's own: `Inv` at the start state and `ScalarWidthsAgree` at the
  end state, as for the certified arms.

No theorem here is about the entry (`synthesizeFromConst`'s legacy arm:
`openRecordInputs`, `lambdaTelescope`, `splitReturnLeaves`,
`bindInputsLegacy`), the outputs, registers, memories or instances emitted by
the legacy handlers, or the emitted design. -/
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

/-! ## The step reaches the fallback -/

/-- The core declines the expression: it is not one of the shapes whose
validated cache hit the step tries first, and `translateCore` returns `none`
on it without touching the state. -/
structure NotCore (e : Lean.Expr) : Prop where
  shape : translateCoreShape e = false
  core : ∀ (rec : TranslateFn) (hint : String) (top named : Bool),
    translateCore rec e hint top named = pure none

/-- On an expression the core declines, one step IS the fallback (the proof of
`Tools.ShippingInstanceEntrySoundness.instance_step`, for any expression). -/
theorem step_eq_fallback (rec : TranslateFn) (e : Lean.Expr) (hint : String) (top named : Bool)
    (shape : translateCoreShape e = false)
    (core : translateCore rec e hint top named = pure none) :
    translateStepWith (translateFallback tenv) rec e hint top named =
      (translateFallback tenv) rec e hint top named := by
  simp [translateStepWith, shape, core] <;> rfl

set_option linter.unusedSectionVars false

variable [LinkCtx] [ChildSem]

/-! ## The contract, on a domain -/

/-- The translator `rec` meets the certified contract on every expression and
value of `Dom`. -/
def RecSound (Dom : Lean.Expr → Value → Prop) (rec : TranslateFn) (ctx : CompilerState)
    (inputs : FVarId → Option Value) (we : WEnv) (mems : MEnv) (initial : Env) : Prop :=
  ∀ (e : Lean.Expr) (v : Value), Dom e v → Contract rec ctx inputs we mems initial e v

/-- **The fuel induction, for any domain closed under one step.** The
certified fragment and a legacy arm are both instances of the premise: each
proves `Contract` of the step from `Contract` of the recursive argument on
the sub-expressions. -/
theorem fuel_of_step {Dom : Lean.Expr → Value → Prop} {ctx : CompilerState}
    {inputs : FVarId → Option Value} {we : WEnv} {mems : MEnv} {initial : Env}
    (step : ∀ rec : TranslateFn, RecSound Dom rec ctx inputs we mems initial →
      RecSound Dom (translateStepWith (translateFallback tenv) rec) ctx inputs we mems initial) :
    ∀ fuel : Nat, RecSound Dom (translateFuelFix (translateStep tenv) fuel) ctx inputs we mems initial := by
  intro fuel
  induction fuel with
  | zero =>
    intro e v _
    constructor
    · intro hint top named s' t w lookup hr; exact (Returns.throw hr).elim
    · intro hint top named s' t w prior h widths hr; exact (Returns.throw hr).elim
  | succ fuel ih => exact step _ ih

/-- The shipping translator meets the contract on a domain closed under one
step. -/
theorem translate_of_step {Dom : Lean.Expr → Value → Prop} {ctx : CompilerState}
    {inputs : FVarId → Option Value} {we : WEnv} {mems : MEnv} {initial : Env}
    (step : ∀ rec : TranslateFn, RecSound Dom rec ctx inputs we mems initial →
      RecSound Dom (translateStepWith (translateFallback tenv) rec) ctx inputs we mems initial) :
    RecSound Dom (fun e hint top named => translateExprToWire tenv e hint top named)
      ctx inputs we mems initial :=
  fuel_of_step step translateFuelLimit

/-- **The legacy translator's simulation contract** — the semantic analogue of
`LegacyRel` (`Tools/ShippingChildInv.lean`): relative to its recursive
argument, the block's body meets `Contract` on the domain. STATED ONLY. It is
about the uncached body: the caching shim `Rec.translateExprToWireCached`
cannot meet a contract stated with `Returns` while its hit is unvalidated. For
a domain whose expressions take a handler that reads a wire name from an
`IO.Ref` (the instance caches, the let / loop wire caches) it is not provable
in this form either. -/
def LegacySem (Dom : Lean.Expr → Value → Prop) (ctx : CompilerState)
    (inputs : FVarId → Option Value) (we : WEnv) (mems : MEnv) (initial : Env) : Prop :=
  ∀ rec : TranslateFn, RecSound Dom rec ctx inputs we mems initial →
    RecSound Dom
      (fun e hint top named =>
        Rec.translateExprToWireImpl (fun e h t n => rec e h t n) e hint top named)
      ctx inputs we mems initial

/-! ## Legacy arms -/

/-- **The inline arm's control-flow fact** (a premise, not proved): every
successful run of the fallback on `e` returns the wire of a successful run of
the inline attempt on `e`, with the same hint and name flag, from the same
builder state to the same builder state. -/
def ReachesInline (tenv : Lean.Environment) (rec : TranslateFn) (ctx : CompilerState) (e : Lean.Expr) : Prop :=
  ∀ (hint : String) (top named : Bool) (s t : CircuitState) (w : String),
    Returns ((translateFallback tenv) rec e hint top named) ctx s w t →
    ∃ r : Option String × Option Exception,
      Returns (Rec.tryInlineUnfold rec e hint named) ctx s r t ∧ r.1 = some w

/-- **What the proofs use of `ReachesInline`** (round 12): every successful
run of the fallback on `e` is a successful run of the recursive translator on
an unfolding of `e`, with the same hint and name flag and `isTopLevel =
false`, from the same builder state to the same builder state, with the same
wire. Weaker than `ReachesInline` (`ReachesInline.unfold`): it does not say
that the wire came from a run of `Rec.tryInlineUnfold`. It is what the walked
dispatch concludes (`plain_call_reaches`,
`Tools/ShippingLegacySemInstance.lean`). -/
def ReachesUnfold (tenv : Lean.Environment) (rec : TranslateFn) (ctx : CompilerState) (e : Lean.Expr) : Prop :=
  ∀ (hint : String) (top named : Bool) (s t : CircuitState) (w : String),
    Returns ((translateFallback tenv) rec e hint top named) ctx s w t →
    ∃ e' : Lean.Expr, InlineUnfolds e e' ∧ Returns (rec e' hint false named) ctx s w t

theorem ReachesInline.unfold {rec : TranslateFn} {ctx : CompilerState} {e : Lean.Expr}
    (h : ReachesInline tenv rec ctx e) : ReachesUnfold tenv rec ctx e := by
  intro hint top named s t w hr
  obtain ⟨r, hrun, hres⟩ := h hint top named s t w hr
  exact tryInlineUnfold_returns hrun hres

/-- The legacy handlers proved to meet the contract, as data: the handler an
expression takes and the contract of what that handler translates. -/
inductive LegacyArm (tenv : Lean.Environment) (rec : TranslateFn) (ctx : CompilerState) (inputs : FVarId → Option Value)
    (we : WEnv) (mems : MEnv) (initial : Env) : Lean.Expr → Value → Prop where
  /-- Definition unfolding: the fallback returns the inline attempt's wire,
  and every unfolding the attempt may translate meets the contract at the
  call's value. -/
  | inlineUnfold {e : Lean.Expr} {v : Value} :
      ReachesInline tenv rec ctx e →
      (∀ e' : Lean.Expr, InlineUnfolds e e' → Contract rec ctx inputs we mems initial e' v) →
      LegacyArm tenv rec ctx inputs we mems initial e v

/-- **The fallback on a legacy arm**: frame and semantic outcome, for every
hint and flag — the same `ActionSpec` the certified arms prove. One case per
`LegacyArm` constructor. -/
theorem translateFallback_legacy {rec : TranslateFn} {ctx : CompilerState}
    {inputs : FVarId → Option Value} {we : WEnv} {mems : MEnv} {initial : Env}
    {e : Lean.Expr} {v : Value} (arm : LegacyArm tenv rec ctx inputs we mems initial e v)
    (hint : String) (top named : Bool) :
    ActionSpec ((translateFallback tenv) rec e hint top named) ctx inputs we mems initial v := by
  cases arm with
  | inlineUnfold reach sub =>
    constructor
    · intro s t w lookup hr
      obtain ⟨r, hrun, hres⟩ := reach hint top named s t w hr
      obtain ⟨e', hU, htr⟩ := tryInlineUnfold_returns hrun hres
      exact (sub e' hU).frame hint false named s t w lookup htr
    · intro s t w prior h widths hr
      obtain ⟨r, hrun, hres⟩ := reach hint top named s t w hr
      obtain ⟨e', hU, htr⟩ := tryInlineUnfold_returns hrun hres
      exact (sub e' hU).sem hint false named s t w prior h widths htr

/-- **One step on a legacy arm** meets the certified contract. -/
theorem legacy_step_contract {rec : TranslateFn} {ctx : CompilerState}
    {inputs : FVarId → Option Value} {we : WEnv} {mems : MEnv} {initial : Env}
    {e : Lean.Expr} {v : Value} (nc : NotCore e)
    (arm : LegacyArm tenv rec ctx inputs we mems initial e v) :
    Contract (translateStepWith (translateFallback tenv) rec) ctx inputs we mems initial e v := by
  constructor
  · intro hint top named s t w lookup hr
    rw [step_eq_fallback rec e hint top named nc.shape (nc.core rec hint top named)] at hr
    exact (translateFallback_legacy arm hint top named).frame s t w lookup hr
  · intro hint top named s t w prior h widths hr
    rw [step_eq_fallback rec e hint top named nc.shape (nc.core rec hint top named)] at hr
    exact (translateFallback_legacy arm hint top named).sem s t w prior h widths hr

/-! ## One induction for certified nodes and legacy arms -/

/-- **The combined domain**: expressions built from input binders, the
certified operators of the quoted fragment over arbitrary leaves, and legacy
inline arms, nested in any order, each with its source value.

* `input` — a bound input, with the valuation's value;
* `cert` — a term of the quoted fragment over leaf expressions that are
  themselves in the domain, with the fragment's evaluation. The leaves'
  `Meaning` is asked separately: the certified arms record what they lower,
  and a record is read back by `Meaning`;
* `inline` — a call the legacy inline arm lowers: the core declines it,
  every run of the fallback on it in this context is a run of the translator
  on an unfolding (`ReachesUnfold`), and every unfolding the attempt may
  translate is in the domain at the same value.

Round 12 restated `inline`: its second premise was `∀ rec, ReachesInline rec
ctx e` and is now `∀ rec, ReachesUnfold rec ctx e`. The new premise FOLLOWS
from the old one (`ReachesInline.unfold`), so the domain did not shrink
(`LegacyDom.inline_of_reachesInline` is the old constructor, as a theorem)
and no theorem about the domain became weaker. What a derivation by `inline`
no longer records: that the returned wire was produced by a run of
`Rec.tryInlineUnfold` — only that it is the wire of a translation of an
unfolding. No proof used the stronger fact. -/
inductive LegacyDom (tenv : Lean.Environment) (ctx : CompilerState) (inputs : FVarId → Option Value) :
    Lean.Expr → Value → Prop where
  | input {id : FVarId} {v : Value} : inputs id = some v → LegacyDom tenv ctx inputs (.fvar id) v
  | cert {dom : Lean.Expr} {kb kv : Nat} {vw : Nat → Nat} {bE vE : Nat → Lean.Expr}
      {bools : Nat → Bool} {bits : (j : Nat) → (w : Nat) → BitVec w} {s : SType} (t : Term s) :
      t.WF kb kv vw →
      (∀ j, j < kb → Meaning inputs (bE j) (.bool (bools j))) →
      (∀ j, j < kv → Meaning inputs (vE j) (.bits (vw j) (bits j (vw j)))) →
      (∀ j, j < kb → LegacyDom tenv ctx inputs (bE j) (.bool (bools j))) →
      (∀ j, j < kv → LegacyDom tenv ctx inputs (vE j) (.bits (vw j) (bits j (vw j)))) →
      LegacyDom tenv ctx inputs (quote dom bE vE t) (pack s (eval bools bits t))
  | inline {e : Lean.Expr} {v : Value} : NotCore e →
      (∀ rec : TranslateFn, ReachesUnfold tenv rec ctx e) →
      (∀ e' : Lean.Expr, InlineUnfolds e e' → LegacyDom tenv ctx inputs e' v) →
      LegacyDom tenv ctx inputs e v

/-- The constructor `inline` as it was stated before round 12. -/
theorem LegacyDom.inline_of_reachesInline {ctx : CompilerState}
    {inputs : FVarId → Option Value} {e : Lean.Expr} {v : Value} (nc : NotCore e)
    (reach : ∀ rec : TranslateFn, ReachesInline tenv rec ctx e)
    (sub : ∀ e' : Lean.Expr, InlineUnfolds e e' → LegacyDom tenv ctx inputs e' v) :
    LegacyDom tenv ctx inputs e v :=
  LegacyDom.inline nc (fun rec => (reach rec).unfold) sub

/-- **Semantic preservation on the combined domain, at every fuel.** By
induction on the derivation: an input binder by `input_contract_fuel`, a
certified node by `fuel_contract_leaves` with the leaves' contracts from the
induction hypothesis, a legacy inline arm by `legacy_step_contract` with the
unfoldings' contracts from the induction hypothesis one fuel below. -/
theorem legacy_fuel_contract {ctx : CompilerState} {inputs : FVarId → Option Value}
    {we : WEnv} {mems : MEnv} {initial : Env} {e : Lean.Expr} {v : Value}
    (h : LegacyDom tenv ctx inputs e v) :
    ∀ fuel : Nat, Contract (translateFuelFix (translateStep tenv) fuel) ctx inputs we mems initial e v := by
  induction h with
  | input hi => exact input_contract_fuel hi
  | cert t wf mb mv _ _ ihb ihv =>
    intro fuel
    exact fuel_contract_leaves fuel mb mv ihb ihv t wf
  | inline nc reach _ ih =>
    intro fuel
    cases fuel with
    | zero =>
      constructor
      · intro hint top named s' t w lookup hr; exact (Returns.throw hr).elim
      · intro hint top named s' t w prior hinv widths hr; exact (Returns.throw hr).elim
    | succ fuel =>
      show Contract (translateStepWith (translateFallback tenv) (translateFuelFix (translateStep tenv) fuel))
        ctx inputs we mems initial _ _
      constructor
      · intro hint top named s t w lookup hr
        rw [step_eq_fallback (translateFuelFix (translateStep tenv) fuel) _ hint top named nc.shape
          (nc.core _ hint top named)] at hr
        obtain ⟨e', hU, htr⟩ := reach _ hint top named s t w hr
        exact (ih e' hU fuel).frame hint false named s t w lookup htr
      · intro hint top named s t w prior hinv widths hr
        rw [step_eq_fallback (translateFuelFix (translateStep tenv) fuel) _ hint top named nc.shape
          (nc.core _ hint top named)] at hr
        obtain ⟨e', hU, htr⟩ := reach _ hint top named s t w hr
        exact (ih e' hU fuel).sem hint false named s t w prior hinv widths htr

/-- **The shipping translator on the combined domain**: no recursive-child
premise; the entry invariant and the final widths stay explicit in
`Contract`, as for the certified fragment. -/
theorem legacy_translate_contract {ctx : CompilerState} {inputs : FVarId → Option Value}
    {we : WEnv} {mems : MEnv} {initial : Env} {e : Lean.Expr} {v : Value}
    (h : LegacyDom tenv ctx inputs e v) :
    Contract (fun e hint top named => translateExprToWire tenv e hint top named)
      ctx inputs we mems initial e v :=
  legacy_fuel_contract h translateFuelLimit

end Tools.ShippingLegacySem
