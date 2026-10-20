import Tools.ShippingEntrySoundness

/-! # A run predicate that exposes the `Meta` context

`MReturns m a` / `Returns c ctx s a t` (`Tools/ShippingEntrySoundness.lean`,
`Tools/ShippingTranslateSoundness.lean`) quantify the `Meta.Context` of the
run existentially. That is enough for everything proved about the certified
entry, which never reads the local context. The LEGACY entry does: its
binder walk (`bindInputsLegacy`) reads each binder's name and type with
`fvarId.getDecl`, from the local context that `lambdaTelescope` installed. A
statement "the telescope declared `x` with this name and type, so the walk
finds them" needs the context of the two runs to be the same, named, object.

**Defined here** (next to `MReturns`, nothing existing is changed):

* `MRunsIn m mctx a` — a successful run of the `MetaM` action `m` IN the
  context `mctx` (the states and the world stay existential);
* `RunsIn c mctx ctx s a t` — the same for a `CompilerM` action.

**Proved here**: they refine the existing predicates (`MRunsIn.returns`,
`RunsIn.returns`); `MRunsIn.bind` (both parts run in the SAME context — the
reader passes it on); `MRunsIn.pure`; `getLCtx_runsIn` (the local context
read is the context's); `getDecl_runsIn` — a successful `fvarId.getDecl` in
`mctx` returned the declaration `mctx.lctx.find? fvarId`, or it is a
successful run of `fvarId.throwUnknown` (which throws; not walked here).

**NOT done**: the telescope's statement in this form (which `mctx` the
continuation runs in: `lambdaTelescopeImp` extends `lctx` by `withReader`),
and the binder walk over it. This file is the definition the two need. -/
namespace Tools.ShippingLegacySem
open Lean Meta Sparkle.Compiler.Elab Sparkle.IR.Builder
open Tools.ShippingTranslateSoundness (Returns)
open Tools.ShippingEntrySoundness (MReturns)

/-- A successful run of `m` in the `Meta` context `mctx`. -/
def MRunsIn {α : Type} (m : MetaM α) (mctx : Meta.Context) (a : α) : Prop :=
  ∃ (mref : ST.Ref IO.RealWorld Meta.State)
    (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State) (w w' : Void IO.RealWorld),
    m mctx mref cctx cref w = EST.Out.ok a w'

/-- A successful run of the compiler action `c` in the `Meta` context `mctx`. -/
def RunsIn {α : Type} (c : CompilerM α) (mctx : Meta.Context) (ctx : CompilerState)
    (s : CircuitState) (a : α) (t : CircuitState) : Prop :=
  ∃ (mref : ST.Ref IO.RealWorld Meta.State)
    (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State) (w w' : Void IO.RealWorld),
    (c ctx s) mctx mref cctx cref w = EST.Out.ok (a, t) w'

theorem MRunsIn.returns {α : Type} {m : MetaM α} {mctx : Meta.Context} {a : α}
    (h : MRunsIn m mctx a) : MReturns m a := by
  obtain ⟨mref, cctx, cref, w, w', hrun⟩ := h
  exact ⟨mctx, mref, cctx, cref, w, w', hrun⟩

theorem RunsIn.returns {α : Type} {c : CompilerM α} {mctx : Meta.Context}
    {ctx : CompilerState} {s t : CircuitState} {a : α}
    (h : RunsIn c mctx ctx s a t) : Returns c ctx s a t := by
  obtain ⟨mref, cctx, cref, w, w', hrun⟩ := h
  exact ⟨mctx, mref, cctx, cref, w, w', hrun⟩

/-- Both parts of a bind run in the same context. -/
theorem MRunsIn.bind {α β : Type} {m : MetaM α} {f : α → MetaM β} {mctx : Meta.Context}
    {b : β} (h : MRunsIn (m >>= f) mctx b) :
    ∃ a, MRunsIn m mctx a ∧ MRunsIn (f a) mctx b := by
  obtain ⟨mref, cctx, cref, w, w', hrun⟩ := h
  change (EST.bind (m mctx mref cctx cref) fun a => f a mctx mref cctx cref) w = _ at hrun
  unfold EST.bind at hrun
  split at hrun
  · rename_i a w1 heq
    exact ⟨a, ⟨mref, cctx, cref, w, w1, heq⟩, ⟨mref, cctx, cref, w1, w', hrun⟩⟩
  · cases hrun

theorem MRunsIn.pure {α : Type} {a b : α} {mctx : Meta.Context}
    (h : MRunsIn (Pure.pure a : MetaM α) mctx b) : b = a := by
  obtain ⟨mref, cctx, cref, w, w', hrun⟩ := h
  change EST.Out.ok a w = _ at hrun
  cases hrun; rfl

/-- The local context an action reads is the context's. -/
theorem getLCtx_runsIn {mctx : Meta.Context} {l : LocalContext}
    (h : MRunsIn (getLCtx : MetaM LocalContext) mctx l) : l = mctx.lctx := by
  obtain ⟨mref, cctx, cref, w, w', hrun⟩ := h
  change EST.Out.ok mctx.lctx w = _ at hrun
  cases hrun; rfl

/-- A successful `getDecl` in `mctx` returned the context's declaration (or it
is a successful run of the error path, which is not walked here). -/
theorem getDecl_runsIn {mctx : Meta.Context} {id : FVarId} {decl : LocalDecl}
    (h : MRunsIn id.getDecl mctx decl) :
    mctx.lctx.find? id = some decl ∨ MRunsIn id.throwUnknown mctx decl := by
  unfold FVarId.getDecl at h
  obtain ⟨l, hl, hk⟩ := MRunsIn.bind h
  obtain rfl := getLCtx_runsIn hl
  cases hfind : mctx.lctx.find? id with
  | some d0 =>
    rw [hfind] at hk
    have e := MRunsIn.pure hk
    exact Or.inl (by rw [e])
  | none =>
    rw [hfind] at hk
    exact Or.inr hk

end Tools.ShippingLegacySem
