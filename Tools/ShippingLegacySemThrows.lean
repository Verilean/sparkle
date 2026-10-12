import Tools.ShippingLegacySemCalc

/-! # A failure predicate, and a `try … catch` inversion that reports the failure

`Returns c ctx s a t` says that SOME run of `c` returned. `returns_tryCatch`
(`Tools/ShippingLegacySemCalc.lean`) inverts a returning `try x catch e => h e`
into "`x` returned, or `h ex` returned for some `ex`" — the second disjunct
does not say that `x` FAILED, because `Returns` cannot express a failure.

**Defined here**: `Throws c ctx s ex` — some run of `c` from the compiler
context `ctx` and the builder state `s` ended in the exception `ex`. The
same world quantification as `Returns` (contexts, state references and worlds
existential); nothing else.

**Proved here**

* `RetPost.tryCatchThrows` — `RetPost.tryCatch` with the handler's obligation
  asked only for exceptions that `x` actually threw (in these contexts and
  references, from some world) and that are not an interrupt or a runtime
  exception (`Core.tryCatch` rethrows those: the handler does not run on
  them). The proof is `RetPost.tryCatch`'s, with the failing run kept.
* `returns_tryCatch_throws` — **the failure-reporting inversion**: a returning
  `try x catch e => h e` is a returning run of `x`, OR `x` THREW some `ex`
  that is neither an interrupt nor a runtime exception and `h ex` returned —
  all from the same builder state.
* `Throws.bind` — a failing `m >>= f`: `m` failed, or `m` returned and the
  continuation failed.
* `Throws.pure` — `pure` does not fail.

What this does NOT give: the failing run of `x` and the returning run of the
handler are two facts with separately quantified worlds, as everywhere in
this calculus. It is enough to use a premise of the form "this action has no
catchable failure". -/
namespace Tools.ShippingLegacySem
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.Builder
open Tools.ShippingTranslateSoundness hiding Inv Spec
open Tools.ShippingEntrySoundness

/-- Some run of `c` from `(ctx, s)` ended in the exception `ex`. -/
def Throws {α : Type} (c : CompilerM α) (ctx : CompilerState) (s : CircuitState)
    (ex : Exception) : Prop :=
  ∃ (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
    (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State) (w w' : Void IO.RealWorld),
    (c ctx s) mctx mref cctx cref w = EST.Out.error ex w'

/-- `RetPost.tryCatch`, the handler asked only on exceptions the body threw
and `Core.tryCatch` hands over. -/
theorem RetPost.tryCatchThrows {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {α : Type} {x : MetaM α} {h : Exception → MetaM α}
    {Q : α → Void IO.RealWorld → Prop}
    (hx : RetPost mctx mref cctx cref x Q)
    (hh : ∀ (e : Exception) (w0 w1 : Void IO.RealWorld),
      x mctx mref cctx cref w0 = EST.Out.error e w1 →
      ¬ ((e.isInterrupt || e.isRuntime) = true) →
      ∀ (w2 : Void IO.RealWorld) (a : α) (w3 : Void IO.RealWorld),
        h e mctx mref cctx cref w2 = EST.Out.ok a w3 → Q a w3) :
    RetPost mctx mref cctx cref (MonadExcept.tryCatch x h) Q := by
  intro w
  have h1 := hx w
  change match (Core.tryCatch (x mctx mref) (fun e => h e mctx mref)) cctx cref w with
    | .ok a w' => Q a w' | .error _ _ => True
  unfold Core.tryCatch
  change match (EST.tryCatch (x mctx mref cctx cref)
      (fun ex => (if (ex.isInterrupt || ex.isRuntime) = true then (MonadExcept.throw ex : CoreM α)
        else h ex mctx mref) cctx cref)) w with
    | .ok a w' => Q a w' | .error _ _ => True
  unfold EST.tryCatch
  cases hxw : x mctx mref cctx cref w with
  | ok a w1 => rw [hxw] at h1; exact h1
  | error e w1 =>
    rw [hxw] at h1
    dsimp only
    by_cases hc : (e.isInterrupt || e.isRuntime) = true
    · rw [if_pos hc]; exact h1
    · rw [if_neg hc]
      exact (RetPost.of_ok (m := h e) (hh e w w1 hxw hc)) w1

/-- **A successful `try … catch`, with the failure reported**: the body's
run, or the body THREW a catchable exception and the handler ran on it — from
the same builder state. -/
theorem returns_tryCatch_throws {α : Type} {x : CompilerM α} {h : Exception → CompilerM α}
    {ctx : CompilerState} {s t : CircuitState} {a : α}
    (hr : Returns (MonadExcept.tryCatch x h) ctx s a t) :
    Returns x ctx s a t ∨
      ∃ ex, Throws x ctx s ex ∧ ¬ ((ex.isInterrupt || ex.isRuntime) = true) ∧
        Returns (h ex) ctx s a t := by
  obtain ⟨mctx, mref, cctx, cref, w, w', hrun⟩ := hr
  have hx : RetPost mctx mref cctx cref (x ctx s)
      (fun p _ => Returns x ctx s p.1 p.2 ∨
        ∃ ex, Throws x ctx s ex ∧ ¬ ((ex.isInterrupt || ex.isRuntime) = true) ∧
          Returns (h ex) ctx s p.1 p.2) :=
    RetPost.of_ok fun w1 p w2 h1 =>
      Or.inl (show Returns x ctx s p.1 p.2 from ⟨mctx, mref, cctx, cref, w1, w2, h1⟩)
  have T : RetPost mctx mref cctx cref ((MonadExcept.tryCatch x h : CompilerM α) ctx s)
      (fun p _ => Returns x ctx s p.1 p.2 ∨
        ∃ ex, Throws x ctx s ex ∧ ¬ ((ex.isInterrupt || ex.isRuntime) = true) ∧
          Returns (h ex) ctx s p.1 p.2) :=
    RetPost.tryCatchThrows (x := x ctx s) (h := fun ex => h ex ctx s) hx
      (fun e w0 w1 hthrow hc w2 p w3 h1 =>
        Or.inr ⟨e,
          (show Throws x ctx s e from ⟨mctx, mref, cctx, cref, w0, w1, hthrow⟩), hc,
          (show Returns (h e) ctx s p.1 p.2 from ⟨mctx, mref, cctx, cref, w2, w3, h1⟩)⟩)
  exact RetPost.ok T hrun

/-- A failing bind: the first action failed, or it returned and the
continuation failed. -/
theorem Throws.bind {α β : Type} {m : CompilerM α} {f : α → CompilerM β}
    {ctx : CompilerState} {s : CircuitState} {ex : Exception}
    (h : Throws (m >>= f) ctx s ex) :
    Throws m ctx s ex ∨ ∃ a s', Returns m ctx s a s' ∧ Throws (f a) ctx s' ex := by
  obtain ⟨mctx, mref, cctx, cref, w, w', hrun⟩ := h
  change (EST.bind (m ctx s mctx mref cctx cref)
    fun p => f p.1 ctx p.2 mctx mref cctx cref) w = _ at hrun
  unfold EST.bind at hrun
  split at hrun
  · rename_i p w1 heq
    exact Or.inr ⟨p.1, p.2, ⟨mctx, mref, cctx, cref, w, w1, heq⟩,
      ⟨mctx, mref, cctx, cref, w1, w', hrun⟩⟩
  · rename_i e1 w1 heq
    -- the two `error`s are at different result types: compare components
    injection hrun with he hw
    rw [he, hw] at heq
    exact Or.inl ⟨mctx, mref, cctx, cref, w, w', heq⟩

/-- `pure` does not fail. -/
theorem Throws.pure {α : Type} {a : α} {ctx : CompilerState} {s : CircuitState}
    {ex : Exception} (h : Throws (Pure.pure a : CompilerM α) ctx s ex) : False := by
  obtain ⟨mctx, mref, cctx, cref, w, w', hrun⟩ := h
  change EST.Out.ok (a, s) w = _ at hrun
  cases hrun

end Tools.ShippingLegacySem
