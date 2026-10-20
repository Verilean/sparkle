import Tools.ShippingLegacySemCalc
import Tools.ShippingLegacySemTrace

/-! # The legacy inline attempt returns the translation of an unfolding

`Rec.tryInlineUnfold` (`Sparkle/Compiler/Elab.lean`) is the "unfold and
translate inline" step of the legacy handler `Rec.handleDefinitionUnfold`: the
default lowering of a call to an untagged definition. It asks Lean for an
unfolding of the call, translates it, and on failure retries with the
reducible unfolding.

**Proved here** (`tryInlineUnfold_returns`), for EVERY successful run of the
real program, any recursive translator `tr`, any compiler context and builder
state: a wire the attempt returns is the wire a successful run of
`tr e' hint false named` returned, FROM THE ATTEMPT'S OWN START STATE to the
attempt's end state, for an expression `e'` that one of the attempt's two
unfolding oracles returned on the call and that the attempt's own test found
different from it (`InlineUnfolds`). In particular a failed first attempt
leaves nothing in the builder state the retry starts from, and the
`isTopLevel` flag of the sub-translation is `false` whatever the caller's.

(Cache fix, variant A: the attempt now snapshots the wire-naming `IO.Ref`
caches before the first translation and restores them in both `catch`
branches. Neither touches the builder state — `snapshotWireCaches_frame`,
`restoreWireCaches_frame` — so the statement below is unchanged.)

**NOT proved here**: that an unfolding means what the call means. On the
source side that is Lean's definitional unfolding (δ, then β) — a fact about
the run's environment, of the kind `EntryDefines` / `MachineDefines` state for
a declaration; the contract file takes it in the form "every unfolding the
oracles may return is in the domain with the same value". Nothing is proved
about `Rec.handleDefinitionUnfold` around the attempt (the projection
shortcuts, the sub-module synthesis after a failed attempt), nor about how the
legacy dispatch reaches the handler. -/
namespace Tools.ShippingLegacySem
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.Builder
open Tools.ShippingTranslateSoundness hiding Inv Spec
open Tools.ShippingEntrySoundness

/-- The inline attempt's first oracle, as `Rec.tryInlineUnfold` runs it:
Lean's one-step unfolding of the head definition at the ambient transparency,
or the expression itself. -/
def unfoldOnce (e : Lean.Expr) : MetaM Lean.Expr := do
  match ← Lean.Meta.unfoldDefinition? e with
    | some e' => return e'
    | none => return e

/-- The retry's oracle: the same at reducible transparency. -/
def unfoldOnceReducible (e : Lean.Expr) : MetaM Lean.Expr := do
  Lean.Meta.withTransparency .reducible do
    match ← Lean.Meta.unfoldDefinition? e with
    | some e' => return e'
    | none => return e

/-- `e'` is an expression the inline attempt may translate in place of the
call `e`: a result of one of its two oracles on `e` (in SOME run: `MReturns`
quantifies the Meta context and the world) that the attempt's test
`e' != e` accepts. -/
def InlineUnfolds (e e' : Lean.Expr) : Prop :=
  (e' != e) = true ∧
    (MReturns (unfoldOnce e) e' ∨ MReturns (unfoldOnceReducible e) e')

/-- What a run of the inline attempt from `s` establishes of its result and
end state: a returned wire is a translation of an unfolding, run from `s`. -/
def InlineQ (tr : TranslateFn) (e : Lean.Expr) (hint : String) (named : Bool)
    (ctx : CompilerState) (s : CircuitState)
    (r : Option String × Option Exception) (t : CircuitState) : Prop :=
  ∀ w : String, r.1 = some w →
    ∃ e' : Lean.Expr, InlineUnfolds e e' ∧ Returns (tr e' hint false named) ctx s w t

theorem inlineQ_none {tr : TranslateFn} {e : Lean.Expr} {hint : String} {named : Bool}
    {ctx : CompilerState} {s t : CircuitState} {ex : Option Exception} :
    InlineQ tr e hint named ctx s (none, ex) t := by
  intro w hw
  have hw' : (none : Option String) = some w := hw
  cases hw'

theorem inlineQ_some {tr : TranslateFn} {e e' : Lean.Expr} {hint : String} {named : Bool}
    {ctx : CompilerState} {s t : CircuitState} {w : String} {ex : Option Exception}
    (hne : (e' != e) = true)
    (hU : MReturns (unfoldOnce e) e' ∨ MReturns (unfoldOnceReducible e) e')
    (hr : Returns (tr e' hint false named) ctx s w t) :
    InlineQ tr e hint named ctx s (some w, ex) t := by
  intro w' hw'
  have hw'' : some w = some w' := hw'
  cases hw''
  exact ⟨e', ⟨hne, hU⟩, hr⟩

/-! ## The snapshot and the restore leave the builder state

(Cache fix, variant A.) `Rec.tryInlineUnfold` reads the wire-naming `IO.Ref`
caches before its attempt (`snapshotWireCaches`) and writes them back in both
`catch` branches (`restoreWireCaches`). Both are sequences of a context read
and lifted `IO.Ref` operations: the builder state is not touched. -/

/-- A context read leaves the builder state. -/
theorem Ensures.read_frame {ctx : CompilerState} {s : CircuitState} :
    Ensures CompilerM.getCompilerState ctx s (fun _ t => t = s) := by
  intro c t hr
  exact (Returns.read hr).2

/-- A bind whose first action leaves the builder state: the continuation runs
from the same state. -/
theorem Ensures.bindFrame {α β : Type} {c : CompilerM α} {f : α → CompilerM β}
    {ctx : CompilerState} {s : CircuitState} {Q : β → CircuitState → Prop}
    (hc : Ensures c ctx s (fun _ t => t = s)) (h : ∀ a : α, Ensures (f a) ctx s Q) :
    Ensures (c >>= f) ctx s Q := by
  intro b t hr
  obtain ⟨a, s1, ha, hb⟩ := Returns.bind hr
  have hs1 : s1 = s := hc a s1 ha
  rw [hs1] at hb
  exact h a b t hb

/-- Close `Ensures P ctx s (fun _ t => t = s)` for a program built from the
context read, lifted oracles, `pure`, `>>=`, `if` / `match`. -/
macro "frame_walk" : tactic =>
  `(tactic| repeat' (first
      | exact Ensures.pure rfl
      | exact Ensures.lift_frame
      | exact Ensures.read_frame
      | refine Ensures.bindLift (fun _ _ => ?_)
      | refine Ensures.bindFrame ?_ (fun _ => ?_)
      | split))

/-- The snapshot leaves the builder state. Expected shape (NOT observed):
`getCompilerState >>= fun c => (match c.exprCache with | some ref =>
liftMetaM ref.get >>= fun m => pure (some m) | none => pure none) >>= fun expr
=> liftMetaM … >>= … (eight reads) … pure {…}`. -/
theorem snapshotWireCaches_frame {ctx : CompilerState} {s : CircuitState} :
    Ensures snapshotWireCaches ctx s (fun _ t => t = s) := by
  unfold snapshotWireCaches
  try dsimp only
  frame_walk

/-- The restore leaves the builder state. Expected shape (NOT observed):
`getCompilerState >>= fun c0 => (match c0.exprCache, c.expr with | some ref,
some m => liftMetaM (ref.set m) | _, _ => pure ()) >>= fun _ => liftMetaM … >>=
… (eight writes)`, possibly with the continuation as a join point (inlined by
`dsimp only`). -/
theorem restoreWireCaches_frame (c : WireCaches) {ctx : CompilerState} {s : CircuitState} :
    Ensures (restoreWireCaches c) ctx s (fun _ t => t = s) := by
  unfold restoreWireCaches
  try dsimp only
  frame_walk

/-- **The inline attempt, walked**: the oracle, the test, the first
translation under a `catch`; in the handler the retry's oracle, its test and
its translation under a second `catch`. Both `catch`es run their handler from
the state the attempt started in (`Ensures.tryCatch`), so every returning path
is ONE translation from that state. The walk follows the same program
structure as `tryInlineUnfold_tripleC` (`Tools/ShippingChildLegacy.lean`). -/
theorem tryInlineUnfold_ensures (tr : TranslateFn) (e : Lean.Expr) (hint : String) (named : Bool)
    (ctx : CompilerState) (s : CircuitState) :
    Ensures (Rec.tryInlineUnfold tr e hint named) ctx s (InlineQ tr e hint named ctx s) := by
  unfold Rec.tryInlineUnfold
  refine Ensures.bindLift ?_
  intro eReduced hU1
  refine Ensures.ite (fun hc => ?_) (fun _ => ?_)
  · -- the snapshot (the builder state is left), then the attempt
    refine Ensures.bindFrame snapshotWireCaches_frame ?_
    intro saved
    refine Ensures.tryCatch ?_ ?_
    · refine Ensures.bindRun ?_
      intro w t hr
      exact Ensures.pure (inlineQ_some hc (Or.inl hU1) hr)
    · intro ex1
      -- the restore (the builder state is left), then the retry
      refine Ensures.bindFrame (restoreWireCaches_frame saved) ?_
      intro _
      refine Ensures.tryCatch ?_ ?_
      · refine Ensures.bindLift ?_
        intro eReduced2 hU2
        refine Ensures.ite (fun hc2 => ?_) (fun _ => ?_)
        · refine Ensures.bindRun ?_
          intro w t hr
          exact Ensures.pure (inlineQ_some hc2 (Or.inr hU2) hr)
        · exact Ensures.pure inlineQ_none
      · intro ex2
        refine Ensures.bindFrame (restoreWireCaches_frame saved) ?_
        intro _
        exact Ensures.pure inlineQ_none
  · exact Ensures.pure inlineQ_none

/-- **The inline attempt's semantic step.** A wire returned by a successful
run of `Rec.tryInlineUnfold` from `s` to `t` is the result of a successful run
of the recursive translator on an unfolding of the call, from `s` to `t`, with
the caller's hint and name flag and `isTopLevel = false`. -/
theorem tryInlineUnfold_returns {tr : TranslateFn} {e : Lean.Expr} {hint : String}
    {named : Bool} {ctx : CompilerState} {s t : CircuitState}
    {r : Option String × Option Exception} {w : String}
    (hrun : Returns (Rec.tryInlineUnfold tr e hint named) ctx s r t) (hres : r.1 = some w) :
    ∃ e' : Lean.Expr, InlineUnfolds e e' ∧ Returns (tr e' hint false named) ctx s w t := by
  have h := tryInlineUnfold_ensures tr e hint named ctx s r t hrun
  exact h w hres

end Tools.ShippingLegacySem
