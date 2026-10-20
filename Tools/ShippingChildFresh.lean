import Tools.ShippingChildInvA
-- BUILT by the integrator: fr1 exit 0 (311 jobs) (round par/vert, base 777630e9). Isolated: only Tools/ShippingChildVCA.lean
-- uses it. No `sorry`, no `axiom`, no `native_decide`, no new law.
-- Writing-time guesses:
--  F1 `(IO.mkRef v : MetaM (IO.Ref σ))` elaborates (IO.mkRef is generic over `MonadLiftT BaseIO m`),
--     the same form as `FramedA.mkExprCache` (ShippingChildInvA.lean) and Elab.lean:2940;
--  F2 `RunsTo.bind` (ShippingEntrySoundness.lean:946) applies to `x >>= k` with `x` the mkRef run
--     (implicit unification of `m`/`f` from the hypothesis' type);
--  F3 the anonymous-constructor nesting `⟨v, mctx, mref, cctx, cref, w, w1, Or.inl h1⟩` for the
--     existential `MkRefd`.

/-! # Provenance of run-local refs: `MkRefd`

`FramedA Fresh` (Tools/ShippingChildInvA.lean) asks a provenance proof
`Fresh σ r` of every caller-supplied run-local ref (`exprCache*`, `local*`).
Here `Fresh` gets a MEANING: `MkRefd σ r` — `r` is the result of a returning
run of `IO.mkRef v` (in some contexts, from some world). It is NOT
`fun _ _ => True`: it is a statement about the runtime's `IO.mkRef`.

What `MkRefd` does NOT give by itself: that such a ref is distinct from the
three tracked refs (`sparkleChildCache`, `sparkleChildSynth`,
`sparkleSynthDepth`). That non-alias is exactly what the law
`RefLawsAOps.frame` at `FramedA MkRefd (.localSet r v _ hr)` /
`.exprCacheModify r f hr` states (a set/modify of an `MkRefd` ref leaves the
three tracked values): it stays a LAW of the new boundary (a premise, field of
`RefLawsAOps MkRefd …`), not proved here. No law field is added. The
allocation itself (`IO.mkRef`) is framed by the existing constructors
`FramedA.mkExprCache` / `FramedA.localMk`.

Proved here (no law used at all):
* `mkRefd_of_runs` / `mkRefd_of_runsIO`: a returning mkRef run gives `MkRefd`;
* `runsTo_mkRef_bind` / `runsTo_mkRefIO_bind`: in a returning run of
  `IO.mkRef v >>= k`, the continuation is run on a ref `r` with `MkRefd σ r`
  (the bind's `RunsTo` decomposition). -/

namespace Tools.ShippingChildFresh
open Lean Meta
open Tools.ShippingEntrySoundness
open Tools.ShippingChildInv
open Tools.ShippingChildInvA

/-- **Provenance**: `r` was returned by a run of `IO.mkRef` (in `MetaM`
directly, or lifted from `IO`). -/
def MkRefd (σ : Type) (r : IO.Ref σ) : Prop :=
  ∃ (v : σ) (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
    (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State) (w w' : Void IO.RealWorld),
    RunsTo (IO.mkRef v : MetaM (IO.Ref σ)) mctx mref cctx cref w r w' ∨  -- guess: F1
    RunsTo (liftM (IO.mkRef v : IO (IO.Ref σ)) : MetaM (IO.Ref σ)) mctx mref cctx cref w r w'

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

theorem mkRefd_of_runs {σ : Type} {v : σ} {w : Void IO.RealWorld} {r : IO.Ref σ}
    {w' : Void IO.RealWorld}
    (h : RunsTo (IO.mkRef v : MetaM (IO.Ref σ)) mctx mref cctx cref w r w') : MkRefd σ r :=
  ⟨v, mctx, mref, cctx, cref, w, w', Or.inl h⟩  -- guess: F3

theorem mkRefd_of_runsIO {σ : Type} {v : σ} {w : Void IO.RealWorld} {r : IO.Ref σ}
    {w' : Void IO.RealWorld}
    (h : RunsTo (liftM (IO.mkRef v : IO (IO.Ref σ)) : MetaM (IO.Ref σ)) mctx mref cctx cref w r w') :
    MkRefd σ r :=
  ⟨v, mctx, mref, cctx, cref, w, w', Or.inr h⟩

/-- **Threading**: a returning run of `x ← IO.mkRef v; k x` runs `k` on a ref
with provenance `MkRefd`, from the world the allocation ended in. -/
theorem runsTo_mkRef_bind {σ β : Type} {v : σ} {k : IO.Ref σ → MetaM β}
    {w : Void IO.RealWorld} {b : β} {w'' : Void IO.RealWorld}
    (h : RunsTo ((IO.mkRef v : MetaM (IO.Ref σ)) >>= k) mctx mref cctx cref w b w'') :
    ∃ r w1, MkRefd σ r ∧
      RunsTo (IO.mkRef v : MetaM (IO.Ref σ)) mctx mref cctx cref w r w1 ∧
      RunsTo (k r) mctx mref cctx cref w1 b w'' := by
  obtain ⟨r, w1, h1, h2⟩ := RunsTo.bind h  -- guess: F2
  exact ⟨r, w1, mkRefd_of_runs h1, h1, h2⟩

theorem runsTo_mkRefIO_bind {σ β : Type} {v : σ} {k : IO.Ref σ → MetaM β}
    {w : Void IO.RealWorld} {b : β} {w'' : Void IO.RealWorld}
    (h : RunsTo ((liftM (IO.mkRef v : IO (IO.Ref σ)) : MetaM (IO.Ref σ)) >>= k)
      mctx mref cctx cref w b w'') :
    ∃ r w1, MkRefd σ r ∧
      RunsTo (liftM (IO.mkRef v : IO (IO.Ref σ)) : MetaM (IO.Ref σ)) mctx mref cctx cref w r w1 ∧
      RunsTo (k r) mctx mref cctx cref w1 b w'' := by
  obtain ⟨r, w1, h1, h2⟩ := RunsTo.bind h
  exact ⟨r, w1, mkRefd_of_runsIO h1, h1, h2⟩

end Tools.ShippingChildFresh
