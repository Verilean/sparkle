import Tools.ShippingLegacySemUnfold
import Tools.ShippingLegacySemSteps

/-! # The handler chain of `Rec.translateExprToWireApp`, walked

`Rec.translateExprToWireApp` on an application whose head is a constant
`name`: a trace; `handleErrorPatterns`; three inline guards (the unit
terminator, `Signal.pure` / `Signal.lit` of a unit, the `Seq.seq` /
`Functor.map` spine); then nine handler calls, each under the profile wrapper
and each returning its wire if it has one; then an error.

**Proved** (`chain_plain`): for a head that is none of the six names of the
inline guards (`GlueName`), given the nine handler facts (`PlainChain`) and
`Rec.handleDefinitionUnfold`'s statement (`UnfoldSpec`), a successful run of
`Rec.translateExprToWireApp` on `e` returning `w` has an `UnfoldOutcome`: the
inline attempt's wire, or the attempt returned none, left the builder state,
and the wire is the sub-module path's.

This replaces the hypothesis `hchain` of `bodyOutcome_of_walk`
(`bodyOutcome_of_pre`): what is left of the body stage is `hpre`.

No `dsimp` / `simp` / `split` on the program: each step is an inversion lemma
of `Tools/ShippingLegacySemSteps.lean` or `Returns.bind`, and the handler
facts are used as given.

**Expected elaborated shape** (NOT observed), join points written inline:

```
match e.getAppFn with
| .const name _ =>
  trace[…] ;                                   -- returns_trace_then
  profHandler 0 (handleErrorPatterns …) >>= fun _ =>
  if (name == ``PUnit.unit || name == ``Unit.unit) = true then … else
  if ((name == ``Signal.pure || name == ``Signal.lit) && decide (args.size ≥ 1)) = true
    then … else
  if ((name == ``Seq.seq || name == ``Functor.map) && decide (args.size ≥ 1)) = true
    then … else
  profHandler 1 (handleCircuitMonad …) >>= fun r =>
    match r with | some w => pure w | _ =>
  … (profHandler 2 … 8, the same) …
  profHandler 9 (handleDefinitionUnfold …) >>= fun r =>
    match r with | some w => pure w | _ => CompilerM.liftMetaM (if … then throwError … else throwError …)
| _ => …
```
-/
namespace Tools.ShippingLegacySem
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.Builder
open Tools.ShippingTranslateSoundness hiding Inv Spec
open Tools.ShippingEntrySoundness

/-- The names the three inline guards of `Rec.translateExprToWireApp` test,
failing. -/
structure GlueName (name : Name) : Prop where
  punit : (name == ``PUnit.unit) = false
  unit : (name == ``Unit.unit) = false
  sigPure : (name == ``Sparkle.Core.Signal.Signal.pure) = false
  sigLit : (name == ``Sparkle.Core.Signal.Signal.lit) = false
  seq : (name == ``Seq.seq) = false
  fmap : (name == ``Functor.map) = false

/-- A lifted `throwError`, in either branch of an `if`, does not return. -/
theorem returns_throw_ite {c : Prop} [Decidable c] {m1 m2 : MessageData}
    {ctx : CompilerState} {s t : CircuitState} {r : String}
    (h : Returns (CompilerM.liftMetaM
      (if c then (Lean.throwError m1 : MetaM String) else Lean.throwError m2)) ctx s r t) :
    False := by
  obtain ⟨hm, _⟩ := returns_liftMetaM h
  rcases MReturns.ite hm with h1 | h1
  · obtain ⟨mctx, mref, cctx, cref, w0, w1, hrun⟩ := h1
    exact Tools.ShippingChildInv.throwError_not_runs (mctx := mctx) (mref := mref)
      (cctx := cctx) (cref := cref) m1 hrun
  · obtain ⟨mctx, mref, cctx, cref, w0, w1, hrun⟩ := h1
    exact Tools.ShippingChildInv.throwError_not_runs (mctx := mctx) (mref := mref)
      (cctx := cctx) (cref := cref) m2 hrun

set_option maxHeartbeats 1000000 in
/-- **The chain on a plain head.** -/
theorem chain_plain {rec : TranslateFn} {ctx : CompilerState} {e : Lean.Expr} {name : Name}
    {us : List Level} (hfn : e.getAppFn = .const name us) (g : GlueName name)
    (handlers : PlainChain rec ctx e name e.getAppArgs) (hunfold : UnfoldSpec rec ctx e name)
    (hint : String) (named : Bool) (s t : CircuitState) (w : String)
    (h : Returns (Rec.translateExprToWireApp (fun e h t n => rec e h t n) e hint named)
      ctx s w t) :
    UnfoldOutcome rec ctx e hint named s t w := by
  unfold Rec.translateExprToWireApp at h
  rw [hfn] at h
  -- the trace, then `handleErrorPatterns` under the profile wrapper
  have k1 := returns_trace_then h
  obtain ⟨u, s1, hep, k2⟩ := Returns.bind k1
  have hs1 : s1 = s := handlers.errors hint named s s1 u (profHandler_returns hep)
  rw [hs1] at k2
  -- the three inline guards
  rcases returns_ite k2 with ⟨hc, _⟩ | ⟨_, k3⟩
  · exact absurd hc (by
      simp only [g.punit, g.unit, Bool.or_self, Bool.false_and, Bool.false_eq_true,
        not_false_eq_true])
  rcases returns_ite k3 with ⟨hc, _⟩ | ⟨_, k4⟩
  · exact absurd hc (by
      simp only [g.sigPure, g.sigLit, Bool.or_self, Bool.false_and, Bool.false_eq_true,
        not_false_eq_true])
  rcases returns_ite k4 with ⟨hc, _⟩ | ⟨_, k5⟩
  · exact absurd hc (by
      simp only [g.seq, g.fmap, Bool.or_self, Bool.false_and, Bool.false_eq_true,
        not_false_eq_true])
  -- the eight handlers that return `none`
  obtain ⟨r1, t1, hh1, m1⟩ := Returns.bind k5
  obtain ⟨hr1, ht1⟩ := handlers.circuit hint named s t1 r1 (profHandler_returns hh1)
  rw [hr1, ht1] at m1
  obtain ⟨r2, t2, hh2, m2⟩ := Returns.bind m1
  obtain ⟨hr2, ht2⟩ := handlers.tuple hint named s t2 r2 (profHandler_returns hh2)
  rw [hr2, ht2] at m2
  obtain ⟨r3, t3, hh3, m3⟩ := Returns.bind m2
  obtain ⟨hr3, ht3⟩ := handlers.applicative hint named s t3 r3 (profHandler_returns hh3)
  rw [hr3, ht3] at m3
  obtain ⟨r4, t4, hh4, m4⟩ := Returns.bind m3
  obtain ⟨hr4, ht4⟩ := handlers.bitvec hint named s t4 r4 (profHandler_returns hh4)
  rw [hr4, ht4] at m4
  obtain ⟨r5, t5, hh5, m5⟩ := Returns.bind m4
  obtain ⟨hr5, ht5⟩ := handlers.register hint named s t5 r5 (profHandler_returns hh5)
  rw [hr5, ht5] at m5
  obtain ⟨r6, t6, hh6, m6⟩ := Returns.bind m5
  obtain ⟨hr6, ht6⟩ := handlers.mux hint named s t6 r6 (profHandler_returns hh6)
  rw [hr6, ht6] at m6
  obtain ⟨r7, t7, hh7, m7⟩ := Returns.bind m6
  obtain ⟨hr7, ht7⟩ := handlers.memory hint named s t7 r7 (profHandler_returns hh7)
  rw [hr7, ht7] at m7
  obtain ⟨r8, t8, hh8, m8⟩ := Returns.bind m7
  obtain ⟨hr8, ht8⟩ := handlers.loop hint named s t8 r8 (profHandler_returns hh8)
  rw [hr8, ht8] at m8
  -- `handleDefinitionUnfold`: its wire, or the terminal error (no run)
  obtain ⟨r9, t9, hh9, m9⟩ := Returns.bind m8
  have hu := profHandler_returns hh9
  cases r9 with
  | none => exact (returns_throw_ite m9).elim
  | some w9 =>
    obtain ⟨hw, ht⟩ := Returns.pure m9
    rw [hw, ht]
    exact hunfold hint named s t9 w9 hu

/-- **The body stage, with the chain discharged**: what is left is the body's
prefix. -/
theorem bodyOutcome_of_pre {rec : TranslateFn} {ctx : CompilerState} {e : Lean.Expr}
    {name : Name} {us : List Level} (hfn : e.getAppFn = .const name us) (g : GlueName name)
    (handlers : PlainChain rec ctx e name e.getAppArgs) (hunfold : UnfoldSpec rec ctx e name)
    (hpre : ∀ (hint : String) (top named : Bool) (s t : CircuitState) (w : String),
      Returns (Rec.translateExprToWireImpl (fun e h t n => rec e h t n) e hint top named)
        ctx s w t →
      Returns (Rec.translateExprToWireApp (fun e h t n => rec e h t n) e hint named) ctx s w t) :
    BodyOutcome rec ctx e := by
  intro hint top named s t w hr
  exact chain_plain hfn g handlers hunfold hint named s t w (hpre hint top named s t w hr)

end Tools.ShippingLegacySem
