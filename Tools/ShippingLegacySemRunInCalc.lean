import Tools.ShippingLegacySemRunIn
import Tools.ShippingLegacySemCalc

/-! # The `RunsIn` calculus

`Tools/ShippingLegacySemRunIn.lean` defines `MRunsIn m mctx a` and
`RunsIn c mctx ctx s a t` (a successful run IN the `Meta` context `mctx`) with
`MRunsIn.bind`, `MRunsIn.pure`, `getLCtx_runsIn`, `getDecl_runsIn`. This file
adds the inversions a walk needs. Every proof is the proof of the `Returns` /
`MReturns` lemma of the same name with the context kept instead of
re-quantified (`Returns.bind`, `Returns.pure`:
`Tools/ShippingTranslateSoundness.lean`; `returns_liftMetaM`,
`returns_tryCatch`: `Tools/ShippingLegacySemCalc.lean`; `MReturns.run`:
`Tools/ShippingEntrySoundness.lean`).

* `RunsIn.bind`, `RunsIn.pure` — both parts of a bind run in the same context.
* `RunsIn.liftMetaM` — a lifted `MetaM` action: the inner action's run IN THE
  SAME context, and the builder state untouched.
* `MRunsIn.run` — `(c.run ctx).run s` in `mctx` is `RunsIn c mctx ctx s`.
* `MRunsIn.ite_pos / ite_neg`, `RunsIn.ite`, `RunsIn.dite_pos / dite_neg`.
* `runsIn_tryCatch` — `try x catch e => h e`: the body's run or a handler's,
  from the same builder state AND in the same context (`Core.tryCatch` passes
  the reader on).
* `getDecl_runsIn_find` — a successful `getDecl` of a variable that the
  context's local context declares returned that declaration. (The version
  of `getDecl_runsIn` with the error path excluded by the lookup's result;
  the same five steps as its proof.)

Nothing here is specific to the compiler. -/
namespace Tools.ShippingLegacySem
open Lean Meta Sparkle.Compiler.Elab Sparkle.IR.Builder
open Tools.ShippingTranslateSoundness (Returns)
open Tools.ShippingEntrySoundness (MReturns)

/-! ## `MetaM` -/

theorem MRunsIn.ite_pos {α : Type} {c : Prop} [Decidable c] {a b : MetaM α}
    {mctx : Meta.Context} {r : α} (h : MRunsIn (if c then a else b) mctx r) (hc : c) :
    MRunsIn a mctx r := by
  rw [if_pos hc] at h
  exact h

theorem MRunsIn.ite_neg {α : Type} {c : Prop} [Decidable c] {a b : MetaM α}
    {mctx : Meta.Context} {r : α} (h : MRunsIn (if c then a else b) mctx r) (hc : ¬ c) :
    MRunsIn b mctx r := by
  rw [if_neg hc] at h
  exact h

/-- The run of a compiler action from a context and a builder state, inside
`MetaM`, is that action's run in the same `Meta` context. -/
theorem MRunsIn.run {α : Type} {c : CompilerM α} {mctx : Meta.Context} {ctx : CompilerState}
    {s : CircuitState} {p : α × CircuitState} (h : MRunsIn ((c.run ctx).run s) mctx p) :
    RunsIn c mctx ctx s p.1 p.2 := by
  obtain ⟨mref, cctx, cref, w, w', hrun⟩ := h
  exact ⟨mref, cctx, cref, w, w', hrun⟩

/-- `getDecl` of a variable the context declares. -/
theorem getDecl_runsIn_find {mctx : Meta.Context} {fid id : FVarId} {decl d0 : LocalDecl}
    (hid : fid = id) (hfind : mctx.lctx.find? id = some d0)
    (h : MRunsIn fid.getDecl mctx decl) : decl = d0 := by
  subst hid
  unfold FVarId.getDecl at h
  obtain ⟨l, hl, hk⟩ := MRunsIn.bind h
  obtain rfl := getLCtx_runsIn hl
  rw [hfind] at hk
  exact MRunsIn.pure hk

/-! ## `CompilerM` -/

/-- Both parts of a bind run in the same context. -/
theorem RunsIn.bind {α β : Type} {m : CompilerM α} {f : α → CompilerM β}
    {mctx : Meta.Context} {ctx : CompilerState} {s s'' : CircuitState} {b : β}
    (h : RunsIn (m >>= f) mctx ctx s b s'') :
    ∃ a s', RunsIn m mctx ctx s a s' ∧ RunsIn (f a) mctx ctx s' b s'' := by
  obtain ⟨mref, cctx, cref, w, w', hrun⟩ := h
  change (EST.bind (m ctx s mctx mref cctx cref)
    fun p => f p.1 ctx p.2 mctx mref cctx cref) w = _ at hrun
  unfold EST.bind at hrun
  split at hrun
  · rename_i p w1 heq
    exact ⟨p.1, p.2, ⟨mref, cctx, cref, w, w1, heq⟩, ⟨mref, cctx, cref, w1, w', hrun⟩⟩
  · cases hrun

theorem RunsIn.pure {α : Type} {a b : α} {mctx : Meta.Context} {ctx : CompilerState}
    {s s' : CircuitState} (h : RunsIn (Pure.pure a : CompilerM α) mctx ctx s b s') :
    b = a ∧ s' = s := by
  obtain ⟨mref, cctx, cref, w, w', hrun⟩ := h
  change EST.Out.ok (a, s) w = _ at hrun
  cases hrun; exact ⟨rfl, rfl⟩

/-- A lifted `MetaM` action runs in the same context and leaves the builder
state. -/
theorem RunsIn.liftMetaM {α : Type} {x : MetaM α} {mctx : Meta.Context} {ctx : CompilerState}
    {s s' : CircuitState} {a : α}
    (h : RunsIn (CompilerM.liftMetaM x) mctx ctx s a s') : MRunsIn x mctx a ∧ s' = s := by
  obtain ⟨mref, cctx, cref, w, w', hrun⟩ := h
  change (EST.bind (x mctx mref cctx cref) fun a => EST.pure (a, s)) w = _ at hrun
  unfold EST.bind at hrun
  split at hrun
  · rename_i b w1 heq
    simp only [EST.pure] at hrun
    cases hrun
    exact ⟨⟨mref, cctx, cref, w, _, heq⟩, rfl⟩
  · cases hrun

theorem RunsIn.ite {α : Type} {c : Prop} [Decidable c] {a b : CompilerM α}
    {mctx : Meta.Context} {ctx : CompilerState} {s t : CircuitState} {r : α}
    (h : RunsIn (if c then a else b) mctx ctx s r t) :
    (c ∧ RunsIn a mctx ctx s r t) ∨ (¬c ∧ RunsIn b mctx ctx s r t) := by
  by_cases hc : c
  · rw [if_pos hc] at h
    exact Or.inl ⟨hc, h⟩
  · rw [if_neg hc] at h
    exact Or.inr ⟨hc, h⟩

theorem RunsIn.dite_pos {α : Type} {c : Prop} [Decidable c] {a : c → CompilerM α}
    {b : ¬ c → CompilerM α} {mctx : Meta.Context} {ctx : CompilerState} {s t : CircuitState}
    {r : α} (h : RunsIn (dite c a b) mctx ctx s r t) (hc : c) :
    RunsIn (a hc) mctx ctx s r t := by
  rw [dif_pos hc] at h
  exact h

theorem RunsIn.dite_neg {α : Type} {c : Prop} [Decidable c] {a : c → CompilerM α}
    {b : ¬ c → CompilerM α} {mctx : Meta.Context} {ctx : CompilerState} {s t : CircuitState}
    {r : α} (h : RunsIn (dite c a b) mctx ctx s r t) (hc : ¬ c) :
    RunsIn (b hc) mctx ctx s r t := by
  rw [dif_neg hc] at h
  exact h

/-- **A successful `try … catch` in a context**: the body's run, or a
handler's — from the SAME builder state, in the SAME context. -/
theorem runsIn_tryCatch {α : Type} {x : CompilerM α} {h : Exception → CompilerM α}
    {mctx : Meta.Context} {ctx : CompilerState} {s t : CircuitState} {a : α}
    (hr : RunsIn (MonadExcept.tryCatch x h) mctx ctx s a t) :
    RunsIn x mctx ctx s a t ∨ ∃ ex, RunsIn (h ex) mctx ctx s a t := by
  obtain ⟨mref, cctx, cref, w, w', hrun⟩ := hr
  have hx : RetPost mctx mref cctx cref (x ctx s)
      (fun p _ => RunsIn x mctx ctx s p.1 p.2 ∨ ∃ ex, RunsIn (h ex) mctx ctx s p.1 p.2) :=
    RetPost.of_ok fun w1 p w2 h1 =>
      Or.inl (show RunsIn x mctx ctx s p.1 p.2 from ⟨mref, cctx, cref, w1, w2, h1⟩)
  have hh : ∀ ex, RetPost mctx mref cctx cref (h ex ctx s)
      (fun p _ => RunsIn x mctx ctx s p.1 p.2 ∨ ∃ ex, RunsIn (h ex) mctx ctx s p.1 p.2) :=
    fun ex => RetPost.of_ok fun w1 p w2 h1 =>
      Or.inr ⟨ex, (show RunsIn (h ex) mctx ctx s p.1 p.2 from ⟨mref, cctx, cref, w1, w2, h1⟩)⟩
  have T : RetPost mctx mref cctx cref ((MonadExcept.tryCatch x h : CompilerM α) ctx s)
      (fun p _ => RunsIn x mctx ctx s p.1 p.2 ∨ ∃ ex, RunsIn (h ex) mctx ctx s p.1 p.2) :=
    RetPost.tryCatch (x := x ctx s) (h := fun ex => h ex ctx s) hx hh
  exact RetPost.ok T hrun

end Tools.ShippingLegacySem
