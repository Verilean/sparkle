import Tools.ShippingLegacySemBody

/-! # What `handleDefinitionUnfold` does on a plain head: the true statement

`Rec.handleDefinitionUnfold` on a call whose head is an ordinary definition —
not tagged `@[hardware_module]`, not a structure projection — runs the inline
attempt `Rec.tryInlineUnfold` and then

* returns the attempt's wire, if the attempt returned one; or
* if the attempt returned NO wire: synthesises the callee as a sub-module
  (`Rec.synthesizeCombinational`), translates the call's arguments, and
  returns the output wire of an instance of that module — or a wire of the
  single-output instance cache / the multi-output port map, without emitting
  anything new.

So "a run returning `some w` returns the wire of a run of the inline attempt"
(the hypothesis `hunfold` of `bodyReachesInline_of_walk`) is FALSE as a
statement about the handler: the second case returns a wire with no
successful attempt behind it. The true statement has two cases
(`UnfoldOutcome`):

* `inline` — a run of the attempt from `s` to `t` returning `(some w, _)`;
* `subModule` — a run of the attempt from `s` returning `(none, _)` and
  leaving the builder state at `s`; the wire `w` and the end state `t` then
  come from the sub-module instance path, about which NOTHING is claimed here
  (it is the legacy instance lowering: `instLinkCheck`, the single-output
  instance cache, `sparkleSubInstanceOutputs`).

The branches of the handler that return a wire WITHOUT the inline attempt,
and where they are in this statement:

| Branch | Head | Here |
|---|---|---|
| projection, cached port (`sparkleSubInstanceOutputs` hit) | structure projection of a tagged call | excluded by `PlainHead` (not a projection) |
| projection, after translating the record call | 〃 | 〃 |
| projection, the constructor's field / the reassembled projection | structure projection | 〃 |
| sub-module instance, tagged callee | `@[hardware_module]` | excluded by `PlainHead` (not tagged); the certified instance arm takes such a call before the legacy body anyway |
| sub-module instance after a failed attempt (new wire, or the single-output cache's, or the port map's) | plain | the `subModule` case |

**Proved here**: `tryInlineUnfold_none_frame` (an attempt that returns no wire
leaves the builder state — both `catch`es roll it back, and the no-unfolding
branch never touched it); `inline_tail` (a program that runs the attempt and
returns its wire when there is one has an `UnfoldOutcome`, whatever it does
otherwise); `bodyOutcome_of_walk` (the body stage with the true statement:
`BodyOutcome`); `bodyReachesInline_of_outcome` (the old stage follows when
the sub-module case is excluded for the expression — a premise, used only to
connect to `ReachesAt`).

The walk of the handler's prefix (`UnfoldSpec` from `PlainHead`) is in
`Tools/ShippingLegacySemUnfoldWalk.lean`.

NOT proved: any contract for the `subModule` case. A call lowered that way is
outside `LegacyDom` and `ReachesAt`. -/
namespace Tools.ShippingLegacySem
open Lean Sparkle.Compiler.Elab Sparkle.IR.Builder
open Tools.ShippingTranslateSoundness hiding Inv Spec
open Tools.ShippingEntrySoundness

/-! ## An attempt without a wire leaves the builder state -/

/-- The postcondition "no wire ⇒ the state is the start state". -/
def NoneQ (s : CircuitState) (r : Option String × Option Exception) (t : CircuitState) :
    Prop :=
  r.1 = none → t = s

theorem noneQ_some {s t : CircuitState} {w : String} {ex : Option Exception} :
    NoneQ s (some w, ex) t := by
  intro h
  have h' : some w = (none : Option String) := h
  cases h'

theorem noneQ_none {s : CircuitState} {ex : Option Exception} : NoneQ s (none, ex) s := by
  intro _
  rfl

/-- **An inline attempt that returns no wire leaves the builder state.** The
same walk as `tryInlineUnfold_ensures`. -/
theorem tryInlineUnfold_none_frame (tr : TranslateFn) (e : Lean.Expr) (hint : String)
    (named : Bool) (ctx : CompilerState) (s : CircuitState) :
    Ensures (Rec.tryInlineUnfold tr e hint named) ctx s (NoneQ s) := by
  unfold Rec.tryInlineUnfold
  refine Ensures.bindLift ?_
  intro eReduced hU1
  refine Ensures.ite (fun hc => ?_) (fun _ => ?_)
  · refine Ensures.bindFrame snapshotWireCaches_frame ?_
    intro saved
    refine Ensures.tryCatch ?_ ?_
    · refine Ensures.bindRun ?_
      intro w t hr
      exact Ensures.pure noneQ_some
    · intro ex1
      refine Ensures.bindFrame (restoreWireCaches_frame saved) ?_
      intro _
      refine Ensures.tryCatch ?_ ?_
      · refine Ensures.bindLift ?_
        intro eReduced2 hU2
        refine Ensures.ite (fun hc2 => ?_) (fun _ => ?_)
        · refine Ensures.bindRun ?_
          intro w t hr
          exact Ensures.pure noneQ_some
        · exact Ensures.pure noneQ_none
      · intro ex2
        refine Ensures.bindFrame (restoreWireCaches_frame saved) ?_
        intro _
        exact Ensures.pure noneQ_none
  · exact Ensures.pure noneQ_none

/-! ## The outcome -/

/-- What a successful run of `Rec.handleDefinitionUnfold` returning `some w`
from `s` to `t` is, on a plain head. -/
def UnfoldOutcome (rec : TranslateFn) (ctx : CompilerState) (e : Lean.Expr) (hint : String)
    (named : Bool) (s t : CircuitState) (w : String) : Prop :=
  (∃ q : Option String × Option Exception,
      Returns (Rec.tryInlineUnfold rec e hint named) ctx s q t ∧ q.1 = some w) ∨
    (∃ q : Option String × Option Exception,
      Returns (Rec.tryInlineUnfold rec e hint named) ctx s q s ∧ q.1 = none)

/-- The handler's statement. -/
def UnfoldSpec (rec : TranslateFn) (ctx : CompilerState) (e : Lean.Expr) (name : Name) : Prop :=
  ∀ (hint : String) (named : Bool) (s t : CircuitState) (w : String),
    Returns (Rec.handleDefinitionUnfold (fun e h t n => rec e h t n) e name e.getAppArgs
      hint named) ctx s (some w) t →
    UnfoldOutcome rec ctx e hint named s t w

/-- **The tail of the handler**: a program that runs the attempt and, when the
attempt returned a wire, returns it (`hK`) — whatever it does when the attempt
returned none. A run returning `some w` has an `UnfoldOutcome`. -/
theorem inline_tail {rec : TranslateFn} {ctx : CompilerState} {e : Lean.Expr} {hint : String}
    {named : Bool} {s t : CircuitState} {w : String}
    {K : Option String × Option Exception → CompilerM (Option String)}
    (hK : ∀ (w' : String) (q2 : Option Exception), K (some w', q2) = pure (some w'))
    (h : Returns (Rec.tryInlineUnfold rec e hint named >>= K) ctx s (some w) t) :
    UnfoldOutcome rec ctx e hint named s t w := by
  unfold UnfoldOutcome
  obtain ⟨q, s7, hq, k7⟩ := Returns.bind h
  obtain ⟨q1, q2⟩ := q
  cases q1 with
  | none =>
    have hs7 : s7 = s := tryInlineUnfold_none_frame rec e hint named ctx s (none, q2) s7 hq rfl
    rw [hs7] at hq
    exact Or.inr ⟨(none, q2), hq, rfl⟩
  | some w' =>
    rw [hK w' q2] at k7
    obtain ⟨hr, ht⟩ := Returns.pure k7
    have hw : w = w' := Option.some.inj hr
    rw [ht, hw]
    exact Or.inl ⟨(some w', q2), hq, rfl⟩

/-! ## The body stage with the true statement -/

/-- The body stage: a run of the legacy body on a plain call has an
`UnfoldOutcome`. -/
def BodyOutcome (rec : TranslateFn) (ctx : CompilerState) (e : Lean.Expr) : Prop :=
  ∀ (hint : String) (top named : Bool) (s t : CircuitState) (w : String),
    Returns (Rec.translateExprToWireImpl (fun e h t n => rec e h t n) e hint top named)
      ctx s w t →
    UnfoldOutcome rec ctx e hint named s t w

/-- **The body stage from its walks**, with `Rec.handleDefinitionUnfold`'s
true statement in place of `hunfold`. -/
theorem bodyOutcome_of_walk {rec : TranslateFn} {ctx : CompilerState} {e : Lean.Expr}
    {name : Name}
    (hpre : ∀ (hint : String) (top named : Bool) (s t : CircuitState) (w : String),
      Returns (Rec.translateExprToWireImpl (fun e h t n => rec e h t n) e hint top named)
        ctx s w t →
      Returns (Rec.translateExprToWireApp (fun e h t n => rec e h t n) e hint named) ctx s w t)
    (hchain : PlainChain rec ctx e name e.getAppArgs →
      ∀ (hint : String) (named : Bool) (s t : CircuitState) (w : String),
        Returns (Rec.translateExprToWireApp (fun e h t n => rec e h t n) e hint named)
          ctx s w t →
        Returns (Rec.handleDefinitionUnfold (fun e h t n => rec e h t n) e name e.getAppArgs
          hint named) ctx s (some w) t)
    (handlers : PlainChain rec ctx e name e.getAppArgs)
    (hunfold : UnfoldSpec rec ctx e name) :
    BodyOutcome rec ctx e := by
  intro hint top named s t w hr
  exact hunfold hint named s t w (hchain handlers hint named s t w (hpre hint top named s t w hr))

/-- The attempt never comes back without a wire on `e` (in this context): the
condition under which the sub-module case does not arise. A premise about the
run — it holds, for instance, when no unfolding of `e` fails to translate. -/
def NoSubModule (rec : TranslateFn) (ctx : CompilerState) (e : Lean.Expr) : Prop :=
  ∀ (hint : String) (named : Bool) (s : CircuitState) (q : Option String × Option Exception),
    Returns (Rec.tryInlineUnfold rec e hint named) ctx s q s → q.1 = none → False

/-- The earlier, stronger stage from the true one, when the sub-module case is
excluded. -/
theorem bodyReachesInline_of_outcome {rec : TranslateFn} {ctx : CompilerState} {e : Lean.Expr}
    (h : BodyOutcome rec ctx e) (hno : NoSubModule rec ctx e) : BodyReachesInline rec ctx e := by
  intro hint top named s t w hr
  have ho := h hint top named s t w hr
  unfold UnfoldOutcome at ho
  rcases ho with hin | ⟨q, hq, hnone⟩
  · exact hin
  · exact (hno hint named s q hq hnone).elim

end Tools.ShippingLegacySem
