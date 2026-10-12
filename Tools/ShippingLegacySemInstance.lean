import Tools.ShippingLegacySemBodyPlain
import Tools.ShippingLegacySemPre
import Tools.ShippingLegacySemShim

/-! # One call, end to end: the step on a plain, non-cacheable call

Everything walked so far, composed for ONE call of the shipping step — the
form a real expression can be plugged into
(`Tests/Compiler/LegacySemInstanceTest.lean`).

**Proved** (`plain_call_action`, `plain_call_step`): for an application
`.app f a` whose head is the constant `name`, a call that is NOT cacheable
(`named`, or `top`) — so today's unvalidated cache hit cannot occur — the
fallback, and with `NotCore` the step `translateStepWith translateFallback
rec`, has the certified arms' `ActionSpec` at value `v`: frame, and from the
invariant the outcome `w ↦ v`.

Premises, by kind:

* decidable facts of the expression and the name: `fallbackKind = .other`,
  `NotCore`, `GlueName`, `PlainName`, `NotBitVecOp`, `PlainName2`, `ImplName`,
  the call's flags;
* the environment the run reads (`PlainHead`: not tagged, not a projection)
  — reflection;
* `HasMappedFVar ctx e` — the body's own test before its `whnf` step;
* `NoSubModule rec ctx e` — the inline attempt never comes back without a
  wire. NOT reflection and not decidable: it is about the run (the unfolding
  oracle returned an unfolding, and translating it did not throw);
* the unfoldings' contracts at the same value (`sub`) — reflection of
  unfolding, plus the recursion hypothesis;
* `Inv` / `ScalarWidthsAgree`, inside `ActionSpec`.

The dispatch used: `fallback_eq_arm`, `arm_to_shim`, `legacyShim_returns`
(no hit: the call is not cacheable), `pre_plain`, `chain_plain` with the nine
handler walks, `unfoldSpec_plain`, `tryInlineUnfold_returns`. -/
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

/-- **The dispatch of a plain, non-cacheable call**: a successful run of the
fallback is one translation of an unfolding, from the same state. -/
theorem plain_call_reaches {rec : TranslateFn} {ctx : CompilerState} {f a : Lean.Expr}
    {name : Name} {us : List Level} {hint : String} {top named : Bool}
    (hfn : (Lean.Expr.app f a).getAppFn = .const name us)
    (hkind : fallbackKind (.app f a) = .other)
    (hplain : PlainHead name) (g : GlueName name) (hn : PlainName name)
    (hb : NotBitVecOp name) (hm : PlainName2 name) (hi : ImplName name)
    (hmap : HasMappedFVar ctx (.app f a))
    (hnc : (!named && !(Lean.Expr.app f a).isFVar && !top) = false)
    (hnosub : NoSubModule rec ctx (.app f a))
    (s t : CircuitState) (w : String)
    (hr : Returns (translateFallback rec (.app f a) hint top named) ctx s w t) :
    ∃ e' : Lean.Expr, InlineUnfolds (.app f a) e' ∧
      Returns (rec e' hint false named) ctx s w t := by
  rw [fallback_eq_arm rec (.app f a) hint top named hkind] at hr
  have hshim := arm_to_shim hfn hplain hr
  rcases legacyShim_returns hshim with hbody | ⟨hc, _, _⟩
  · have ho := bodyOutcome_plain hfn hplain g hn hb hm (pre_plain hfn hi hmap)
      hint top named s t w hbody
    unfold UnfoldOutcome at ho
    rcases ho with ⟨q, hq, hres⟩ | ⟨q, hq, hnone⟩
    · exact tryInlineUnfold_returns hq hres
    · exact (hnosub hint named s q hq hnone).elim
  · exact absurd (hnc.symm.trans hc) (by decide)

set_option linter.unusedSectionVars false

variable [LinkCtx] [ChildSem]

/-- **The fallback on a plain, non-cacheable call.** -/
theorem plain_call_action {rec : TranslateFn} {ctx : CompilerState}
    {inputs : FVarId → Option Value} {we : WEnv} {mems : MEnv} {initial : Env}
    {f a : Lean.Expr} {name : Name} {us : List Level} {v : Value}
    {hint : String} {top named : Bool}
    (hfn : (Lean.Expr.app f a).getAppFn = .const name us)
    (hkind : fallbackKind (.app f a) = .other)
    (hplain : PlainHead name) (g : GlueName name) (hn : PlainName name)
    (hb : NotBitVecOp name) (hm : PlainName2 name) (hi : ImplName name)
    (hmap : HasMappedFVar ctx (.app f a))
    (hnc : (!named && !(Lean.Expr.app f a).isFVar && !top) = false)
    (hnosub : NoSubModule rec ctx (.app f a))
    (sub : ∀ e' : Lean.Expr, InlineUnfolds (.app f a) e' →
      Contract rec ctx inputs we mems initial e' v) :
    ActionSpec (translateFallback rec (.app f a) hint top named) ctx inputs we mems initial v := by
  constructor
  · intro s t w lookup hr
    obtain ⟨e', hU, htr⟩ :=
      plain_call_reaches hfn hkind hplain g hn hb hm hi hmap hnc hnosub s t w hr
    exact (sub e' hU).frame hint false named s t w lookup htr
  · intro s t w prior h widths hr
    obtain ⟨e', hU, htr⟩ :=
      plain_call_reaches hfn hkind hplain g hn hb hm hi hmap hnc hnosub s t w hr
    exact (sub e' hU).sem hint false named s t w prior h widths htr

/-- **The shipping step on a plain, non-cacheable call.** -/
theorem plain_call_step {rec : TranslateFn} {ctx : CompilerState}
    {inputs : FVarId → Option Value} {we : WEnv} {mems : MEnv} {initial : Env}
    {f a : Lean.Expr} {name : Name} {us : List Level} {v : Value}
    {hint : String} {top named : Bool}
    (hfn : (Lean.Expr.app f a).getAppFn = .const name us)
    (nc : NotCore (.app f a))
    (hkind : fallbackKind (.app f a) = .other)
    (hplain : PlainHead name) (g : GlueName name) (hn : PlainName name)
    (hb : NotBitVecOp name) (hm : PlainName2 name) (hi : ImplName name)
    (hmap : HasMappedFVar ctx (.app f a))
    (hnc : (!named && !(Lean.Expr.app f a).isFVar && !top) = false)
    (hnosub : NoSubModule rec ctx (.app f a))
    (sub : ∀ e' : Lean.Expr, InlineUnfolds (.app f a) e' →
      Contract rec ctx inputs we mems initial e' v) :
    ActionSpec (translateStepWith translateFallback rec (.app f a) hint top named)
      ctx inputs we mems initial v := by
  rw [step_eq_fallback rec (.app f a) hint top named nc.shape (nc.core rec hint top named)]
  exact plain_call_action hfn hkind hplain g hn hb hm hi hmap hnc hnosub sub

end Tools.ShippingLegacySem
