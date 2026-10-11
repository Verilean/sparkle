import Tools.ShippingUnifiedRecursion

/-! # A success-postcondition calculus for the legacy translator's handlers

The legacy handlers (`Sparkle/Compiler/Elab.lean`, block `Rec.*`) are
`CompilerM` programs with `try … catch`. The certified arms are walked with
`Returns` (a successful run of the real action) by inverting `>>=`, `pure` and
the lifted oracles; nothing there inverts a `catch`. This file adds that
rule and packages the inversions as a goal-directed calculus:

* `Ensures c ctx s Q` — every successful run of `c` from the compiler context
  `ctx` and the builder state `s` returns a result and an end state satisfying
  `Q`. It is a statement about `Returns`, nothing else.
* `returns_tryCatch` — a successful run of `try x catch e => h e` is a
  successful run of `x`, or a successful run of `h e` for some `e`, and in
  BOTH cases FROM THE SAME builder state `s`: `StateT`'s `tryCatch` hands the
  handler the state the `try` started in, so what a failed attempt emitted is
  discarded. (It is not discarded from the `IO.Ref` caches; see
  `docs/parallel/G2-legacy.md`.)
* the structural rules `Ensures.pure / bindRun / bindLift / ite / tryCatch`.

What is NOT here: any rule for the world (the `IO.Ref`s a handler reads), any
rule for `withLocalDecl` / `withReader`, loops. A handler that takes a wire
name out of an `IO.Ref` cannot be given a postcondition by this calculus:
`Returns` quantifies the world existentially. -/
namespace Tools.ShippingLegacySem
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.Builder
open Tools.ShippingTranslateSoundness hiding Inv Spec
open Tools.ShippingEntrySoundness

/-! ## Successful runs of a `MetaM` action -/

/-- From every world, a returning run of `m` ends in `Q`; a throwing run
claims nothing. -/
def RetPost (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State) (cctx : Core.Context)
    (cref : ST.Ref IO.RealWorld Core.State) {α : Type} (m : MetaM α)
    (Q : α → Void IO.RealWorld → Prop) : Prop :=
  ∀ w : Void IO.RealWorld, match m mctx mref cctx cref w with
    | .ok a w' => Q a w'
    | .error _ _ => True

section MetaLevel
variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- `RetPost` from the action's successful runs. -/
theorem RetPost.of_ok {α : Type} {m : MetaM α} {Q : α → Void IO.RealWorld → Prop}
    (h : ∀ (w : Void IO.RealWorld) (a : α) (w' : Void IO.RealWorld),
      m mctx mref cctx cref w = EST.Out.ok a w' → Q a w') :
    RetPost mctx mref cctx cref m Q := by
  intro w
  cases hm : m mctx mref cctx cref w with
  | ok a w' => exact h w a w' hm
  | error e w' => exact trivial

/-- A successful run of an action with a `RetPost` postcondition satisfies it. -/
theorem RetPost.ok {α : Type} {m : MetaM α} {Q : α → Void IO.RealWorld → Prop}
    {w w' : Void IO.RealWorld} {a : α}
    (h : RetPost mctx mref cctx cref m Q)
    (hrun : m mctx mref cctx cref w = EST.Out.ok a w') : Q a w' := by
  have this := h w
  rw [hrun] at this
  exact this

/-- `try x catch e => h e`: a returning run is a returning run of `x`, or of
the handler from the world the failing `x` ended in (an interrupt or a runtime
exception is rethrown and returns nothing: `Core.tryCatch`). -/
theorem RetPost.tryCatch {α : Type} {x : MetaM α} {h : Exception → MetaM α}
    {Q : α → Void IO.RealWorld → Prop}
    (hx : RetPost mctx mref cctx cref x Q)
    (hh : ∀ e, RetPost mctx mref cctx cref (h e) Q) :
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
    · rw [if_neg hc]; exact hh e w1

end MetaLevel

/-! ## Successful runs of a `CompilerM` action -/

/-- A lifted oracle: its value is one the inner action returned, and the
builder state is untouched. (The statement of
`Tools.ShippingInstanceEntrySoundness.Returns.liftMetaM_mreturns`, repeated
here so this file does not depend on the instance-arm development.) -/
theorem returns_liftMetaM {α : Type} {x : MetaM α} {ctx : CompilerState}
    {s s' : CircuitState} {a : α}
    (h : Returns (CompilerM.liftMetaM x) ctx s a s') : MReturns x a ∧ s' = s := by
  obtain ⟨mctx, mref, cctx, cref, w, w', hrun⟩ := h
  change (EST.bind (x mctx mref cctx cref) fun a => EST.pure (a, s)) w = _ at hrun
  unfold EST.bind at hrun
  split at hrun
  · rename_i b w1 heq
    simp only [EST.pure] at hrun
    cases hrun
    exact ⟨⟨mctx, mref, cctx, cref, w, _, heq⟩, rfl⟩
  · cases hrun

/-- **A successful `try … catch`**: the body's run, or the handler's — from
the SAME builder state. The `StateT` layer of `CompilerM` runs the handler on
the state the `try` started in. -/
theorem returns_tryCatch {α : Type} {x : CompilerM α} {h : Exception → CompilerM α}
    {ctx : CompilerState} {s t : CircuitState} {a : α}
    (hr : Returns (MonadExcept.tryCatch x h) ctx s a t) :
    Returns x ctx s a t ∨ ∃ ex, Returns (h ex) ctx s a t := by
  obtain ⟨mctx, mref, cctx, cref, w, w', hrun⟩ := hr
  have hx : RetPost mctx mref cctx cref (x ctx s)
      (fun p _ => Returns x ctx s p.1 p.2 ∨ ∃ ex, Returns (h ex) ctx s p.1 p.2) :=
    RetPost.of_ok fun w1 p w2 h1 =>
      Or.inl (show Returns x ctx s p.1 p.2 from ⟨mctx, mref, cctx, cref, w1, w2, h1⟩)
  have hh : ∀ ex, RetPost mctx mref cctx cref (h ex ctx s)
      (fun p _ => Returns x ctx s p.1 p.2 ∨ ∃ ex, Returns (h ex) ctx s p.1 p.2) :=
    fun ex => RetPost.of_ok fun w1 p w2 h1 =>
      Or.inr ⟨ex, (show Returns (h ex) ctx s p.1 p.2 from ⟨mctx, mref, cctx, cref, w1, w2, h1⟩)⟩
  -- the `ReaderT` / `StateT` layers of `tryCatch` apply the body and the
  -- handler to the same context and state
  have T : RetPost mctx mref cctx cref ((MonadExcept.tryCatch x h : CompilerM α) ctx s)
      (fun p _ => Returns x ctx s p.1 p.2 ∨ ∃ ex, Returns (h ex) ctx s p.1 p.2) :=
    RetPost.tryCatch (x := x ctx s) (h := fun ex => h ex ctx s) hx hh
  exact RetPost.ok T hrun

/-- Every successful run of `c` from `(ctx, s)` returns a result and an end
state satisfying `Q`. -/
def Ensures {α : Type} (c : CompilerM α) (ctx : CompilerState) (s : CircuitState)
    (Q : α → CircuitState → Prop) : Prop :=
  ∀ (a : α) (t : CircuitState), Returns c ctx s a t → Q a t

theorem Ensures.pure {α : Type} {a : α} {ctx : CompilerState} {s : CircuitState}
    {Q : α → CircuitState → Prop} (h : Q a s) :
    Ensures (Pure.pure a : CompilerM α) ctx s Q := by
  intro b t hr
  obtain ⟨hb, ht⟩ := Returns.pure hr
  subst hb ht
  exact h

/-- A bind: the continuation is run from wherever the first action's
successful run ended, and may use that run. -/
theorem Ensures.bindRun {α β : Type} {c : CompilerM α} {f : α → CompilerM β}
    {ctx : CompilerState} {s : CircuitState} {Q : β → CircuitState → Prop}
    (h : ∀ (a : α) (s1 : CircuitState), Returns c ctx s a s1 → Ensures (f a) ctx s1 Q) :
    Ensures (c >>= f) ctx s Q := by
  intro b t hr
  obtain ⟨a, s1, ha, hb⟩ := Returns.bind hr
  exact h a s1 ha b t hb

/-- A bind on a lifted oracle: the continuation runs from the same builder
state, on a value the oracle returned. -/
theorem Ensures.bindLift {α β : Type} {x : MetaM α} {f : α → CompilerM β}
    {ctx : CompilerState} {s : CircuitState} {Q : β → CircuitState → Prop}
    (h : ∀ a : α, MReturns x a → Ensures (f a) ctx s Q) :
    Ensures (CompilerM.liftMetaM x >>= f) ctx s Q := by
  intro b t hr
  obtain ⟨a, s1, ha, hb⟩ := Returns.bind hr
  obtain ⟨hm, hs⟩ := returns_liftMetaM ha
  subst hs
  exact h a hm b t hb

theorem Ensures.ite {α : Type} {c : Prop} [Decidable c] {a b : CompilerM α}
    {ctx : CompilerState} {s : CircuitState} {Q : α → CircuitState → Prop}
    (ha : c → Ensures a ctx s Q) (hb : ¬c → Ensures b ctx s Q) :
    Ensures (if c then a else b) ctx s Q := by
  by_cases hc : c
  · rw [if_pos hc]; exact ha hc
  · rw [if_neg hc]; exact hb hc

/-- `try x catch e => h e`: both the body and every handler are asked from the
state the `try` starts in. -/
theorem Ensures.tryCatch {α : Type} {x : CompilerM α} {h : Exception → CompilerM α}
    {ctx : CompilerState} {s : CircuitState} {Q : α → CircuitState → Prop}
    (hx : Ensures x ctx s Q) (hh : ∀ ex, Ensures (h ex) ctx s Q) :
    Ensures (MonadExcept.tryCatch x h) ctx s Q := by
  intro a t hr
  rcases returns_tryCatch hr with h1 | ⟨ex, h2⟩
  · exact hx a t h1
  · exact hh ex a t h2

end Tools.ShippingLegacySem
