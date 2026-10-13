import Tools.ShippingLegacySemLeaf
import Tools.ShippingLegacySemInstance

variable {tenv : Lean.Environment}

/-! # Handlers as cases of the leaf domain

Round 18 added to `LeafDom` (`Tools/ShippingLegacySemLeaf.lean`) the
constructor

```
| handled (subs : String → Bool → Lean.Expr → Value → Prop) :
    HandlerCase ctx inputs hint named e v subs →
    (∀ h' n' e' v', subs h' n' e' v' → LeafDom ctx inputs h' n' e' v') →
    LeafDom ctx inputs hint named e v
```

(Round 24: `subs` carries the hint and the name flag at which the arm
translates each sub-expression; the inline arm instantiates them to the
node's own.)

`HandlerCase` is the obligation of ONE arm of the translator: two
implications (frame/outcome, and order) from the sub-expressions the arm
translates, at fuel `f`, to the node at fuel `f + 1`. The handler-level
theorem "the fallback's handlers are cases of the domain" is then: one PROVED
`HandlerCase` per arm; `leaf_fuel_spec`, `leaf_fuel_order`, `leaf_output`
and the entry theorems do not change when an arm is added.

**Proved here**

* `handlerCase_inline` — the inline arm IS a handler case: for an expression
  the core declines (`NotCore`) whose fallback runs are translator runs on
  an unfolding (`ReachesUnfoldAt`, every fuel), with
  `subs h' n' e' v' := h' = hint ∧ n' = named ∧ InlineUnfolds e e' ∧ v' = v`. The two proofs are the
  `inlineAt` cases of `leaf_fuel_spec` / `leaf_fuel_order`.
* `LeafDom.inline_handled` — the constructor `inlineAt`, derived through
  `handled` (so `handled` subsumes it; `inlineAt` is kept because the built
  instances use it).
* `plainCallee_leaf` — a plain call (`f a`, head an untagged constant `n`
  that fails the body's name tests) is in the leaf domain when its
  unfoldings are: the name facts as ONE bundle `PlainCallee n`, generic in
  the callee. A further declaration needs one `PlainCallee` instance (closed
  name tests, by evaluation), the expression's `NotCore` (a closed
  computation), and its unfolding's domain membership.

**Why no constructor for a second ARM this round.** Every handler lemma of
rounds 5–9 (`handleErrorPatterns_frame`, `handleApplicative_none`,
`handleRegister_none`, `handleMux_none`, `handleMemory_none`,
`handleLoop_none`, `handleBitVecOps_none`, `handleTupleProjections_none`,
`handleCircuitMonad_none`) is a DECLINE walk: the handler returns `none` on a
plain name. They are the path TO the inline arm and are already consumed by
`plain_call_reaches`. `UnfoldOutcome`'s second disjunct (the attempt returned
no wire: the sub-module synthesis follows) has a statement and no proof.
`impl_fvar` (the body's variable arm) needs the run's `Meta` context to say
anything about its recursion targets. The one arm with a proved contract
outside this line is the tagged single-output instance call
(`Tools.ShippingInstanceLeaf.inst_leaf_fuel`: a `Contract` at every fuel,
over the hierarchical context); making it a `HandlerCase` needs its ORDER
statement (`ActionOrder`; not proved anywhere) and an output statement over
the hierarchical run instead of the flat `RawValueAt`. See the inventory in
`docs/parallel/G2-legacy-round18.md`. -/
namespace Tools.ShippingLegacySem
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Builder Sparkle.IR.Semantics
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedMeaning
open Tools.ShippingUnifiedCache Tools.ShippingUnifiedInvariant
open Tools.ShippingTranslateSoundness hiding Inv Spec
open Tools.ShippingEntrySoundness
open Tools.ShippingUnifiedRecursion
open Tools.ShippingUnifiedProtection

/-- **The inline arm is a handler case.** -/
theorem handlerCase_inline {ctx : CompilerState} {inputs : FVarId → Option Value}
    {hint : String} {named : Bool} {e : Lean.Expr} {v : Value} (nc : NotCore e)
    (reach : ∀ fuel : Nat,
      ReachesUnfoldAt tenv (translateFuelFix (translateStep tenv) fuel) ctx e hint false named) :
    HandlerCase tenv ctx inputs hint named e v
      (fun h' n' e' v' => h' = hint ∧ n' = named ∧ InlineUnfolds e e' ∧ v' = v) where
  spec := by
    intro fuel we mems initial ih
    constructor
    · intro s t w lookup hr
      have hstep : Returns (translateStepWith (translateFallback tenv)
          (translateFuelFix (translateStep tenv) fuel) e hint false named) ctx s w t := hr
      obtain ⟨e', hU, htr⟩ := reach fuel s t w (step_run_fallback nc hstep)
      exact (ih hint named e' v ⟨rfl, rfl, hU, rfl⟩).frame s t w lookup htr
    · intro s t w prior hinv widths hr
      have hstep : Returns (translateStepWith (translateFallback tenv)
          (translateFuelFix (translateStep tenv) fuel) e hint false named) ctx s w t := hr
      obtain ⟨e', hU, htr⟩ := reach fuel s t w (step_run_fallback nc hstep)
      exact (ih hint named e' v ⟨rfl, rfl, hU, rfl⟩).sem s t w prior hinv widths htr
  order := by
    intro fuel we mems initial _ ih s t w prior hr hinv widths order
    have hstep : Returns (translateStepWith (translateFallback tenv)
        (translateFuelFix (translateStep tenv) fuel) e hint false named) ctx s w t := hr
    obtain ⟨e', hU, htr⟩ := reach fuel s t w (step_run_fallback nc hstep)
    exact ih hint named e' v ⟨rfl, rfl, hU, rfl⟩ s t w prior htr hinv widths order

/-- The constructor `inlineAt`, through `handled`. -/
theorem LeafDom.inline_handled {ctx : CompilerState} {inputs : FVarId → Option Value}
    {hint : String} {named : Bool} {e : Lean.Expr} {v : Value} (nc : NotCore e)
    (reach : ∀ fuel : Nat,
      ReachesUnfoldAt tenv (translateFuelFix (translateStep tenv) fuel) ctx e hint false named)
    (sub : ∀ e' : Lean.Expr, InlineUnfolds e e' → LeafDom tenv ctx inputs hint named e' v) :
    LeafDom tenv ctx inputs hint named e v :=
  LeafDom.handled (fun h' n' e' v' => h' = hint ∧ n' = named ∧ InlineUnfolds e e' ∧ v' = v)
    (handlerCase_inline nc reach)
    (fun h' n' e' v' hs => by
      obtain ⟨hh, hn, hU, hv⟩ := hs
      rw [hh, hn, hv]
      exact sub e' hU)

/-- The name facts of a plain callee, as one bundle: the head's name fails
every name test of the fallback chain before the inline attempt. -/
structure PlainCallee (n : Name) : Prop where
  glue : GlueName n
  plain : PlainName n
  notBV : NotBitVecOp n
  plain2 : PlainName2 n
  impl : ImplName n

/-- **A plain call is a leaf of the domain when its unfoldings are** — at
the entry's name flag (`named = true`: the shim's cache is not consulted),
any hint. Generic in the callee. Premises: the bundle (closed name tests),
the head and the kind (closed computations on the expression), `NotCore`,
and the three facts the walk cannot discharge: `PlainHead` (environment),
`HasMappedFVar` (kernel-opaque `Expr.find?`), `NoSubModule` (the run). -/
theorem plainCallee_leaf {ctx : CompilerState} {inputs : FVarId → Option Value}
    {f a : Lean.Expr} {n : Name} {us : List Level} {v : Value} {hint : String}
    (pc : PlainCallee n)
    (hfn : (Lean.Expr.app f a).getAppFn = .const n us)
    (hkind : fallbackKind (.app f a) = .other)
    (nc : NotCore (.app f a))
    (hplain : PlainHead tenv n) (hmap : HasMappedFVar ctx (.app f a))
    (hnosub : ∀ fuel : Nat, NoSubModule (translateFuelFix (translateStep tenv) fuel) ctx (.app f a))
    (sub : ∀ e' : Lean.Expr, InlineUnfolds (.app f a) e' →
      LeafDom tenv ctx inputs hint true e' v) :
    LeafDom tenv ctx inputs hint true (.app f a) v :=
  LeafDom.inlineAt nc
    (fun fuel s t w hr =>
      plain_call_reaches hfn hkind hplain pc.glue pc.plain pc.notBV pc.plain2 pc.impl hmap rfl
        (hnosub fuel) s t w hr)
    sub

end Tools.ShippingLegacySem
