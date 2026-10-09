import Tools.ShippingChildSynth

/-! # The child cache, proved — `ChildSynthIs` from two smaller boundaries

`sparkleChildSynth` holds `synthesizeChild` (`Sparkle/Compiler/Elab.lean`), an
ORDINARY definition: a hit in `sparkleChildCache` returns the cached result,
a miss runs the real entry `synthesizeCombinational` and records its result.
So `ChildSynthIs` (every read of the ref gives a function whose every run
returns a real-entry result) follows from

* `RefIs`: a read of `sparkleChildSynth` returns `some synthesizeChild`
  (the ref's content — set once at initialisation), and
* `CacheReads`: a read of `sparkleChildCache` returns a map all of whose
  entries are real-entry results (`CacheInv`),

with the memoised entry's behaviour PROVED (`synthesizeChild_run`: hit and
miss). The cache invariant is proved at its initialisation (`cacheInv_empty`:
the cache is cleared at the start of each top-level synthesis) and preserved
by `synthesizeChild`'s write (`cacheInv_insert`, the inserted result being a
real one by the miss path). What `CacheReads` still assumes: that each read
of the `IO.Ref` returns what the last write left (a law of `IO.Ref`, opaque in
the logic). The legacy translator no longer writes the cache: its
`Rec.synthesizeCombinational` goes through `sparkleChildSynth`, so
`synthesizeChild` is the cache's single reader and writer besides the depth-0
clear (before, it inserted results of whatever fuel-truncated translator it
was instantiated with, under the same name key). `CacheReads` is replaced
along the run by pre/post conditions in `ShippingChildCacheRun`. -/
namespace Tools.ShippingChildCache
open Lean Meta
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingChildSynth (RealChild ChildSynthIs)
open Sparkle.Compiler.Elab

/-- The cache's entries are real-entry results, in these contexts. -/
def CacheInv (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
    (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State)
    (m : Std.HashMap Name (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)) : Prop :=
  ∀ c r, m.get? c = some r → RealChild mctx mref cctx cref c r

/-- **Initialisation**: the empty cache. -/
theorem cacheInv_empty {mctx mref cctx cref} : CacheInv mctx mref cctx cref {} := by
  intro c r h; simp at h

/-- **Write preservation**: inserting a real result keeps the invariant. -/
theorem cacheInv_insert {mctx mref cctx cref} {m : Std.HashMap Name (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)}
    {c : Name} {r : Sparkle.IR.AST.Module × Sparkle.IR.AST.Design}
    (h : CacheInv mctx mref cctx cref m) (hr : RealChild mctx mref cctx cref c r) :
    CacheInv mctx mref cctx cref (m.insert c r) := by
  intro c' r' h'
  rw [Std.HashMap.get?_insert] at h'
  split at h'
  · rename_i heq
    have : c = c' := by simpa using heq
    subst this
    cases h'
    exact hr
  · exact h c' r' h'

/-- The ref's content: a read of `sparkleChildSynth` returns `synthesizeChild`. -/
def RefIs (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
    (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State) : Prop :=
  ∀ w r w', RunsTo (sparkleChildSynth.get : MetaM _) mctx mref cctx cref w r w' →
    r = some synthesizeChild

/-- Every read of the cache satisfies the invariant. -/
def CacheReads (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
    (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State) : Prop :=
  ∀ w m w', RunsTo (sparkleChildCache.get : MetaM _) mctx mref cctx cref w m w' →
    CacheInv mctx mref cctx cref m

/-- **The memoised entry, hit and miss.** A run of `synthesizeChild c` read the
cache; on a hit it returned the cached entry, on a miss it ran the real entry
— its result a real one, and the map it records keeps the invariant. -/
theorem synthesizeChild_run {mctx mref cctx cref} {c : Name} {w w'} {y : Sparkle.IR.AST.Module × Sparkle.IR.AST.Design}
    (h : RunsTo (synthesizeChild c) mctx mref cctx cref w y w') :
    ∃ (m : Std.HashMap Name (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)) (w1 : Void IO.RealWorld),
      RunsTo (sparkleChildCache.get : MetaM _) mctx mref cctx cref w m w1 ∧
      (m.get? c = some y ∨
        (m.get? c = none ∧ RealChild mctx mref cctx cref c y ∧
          ∀ m', CacheInv mctx mref cctx cref m' → CacheInv mctx mref cctx cref (m'.insert c y))) := by
  unfold synthesizeChild at h
  obtain ⟨m, w1, hget, h⟩ := RunsTo.bind h
  refine ⟨m, w1, hget, ?_⟩
  cases hm : m.get? c with
  | some r =>
    simp only [hm] at h
    exact Or.inl (by rw [Tools.ShippingMachineEntry.RunsTo.pure_eq h])
  | none =>
    simp only [hm] at h
    obtain ⟨r, w2, hrun, h⟩ := RunsTo.bind h
    obtain ⟨_, w3, _, h⟩ := RunsTo.bind h
    have := Tools.ShippingMachineEntry.RunsTo.pure_eq h
    subst this
    have hr : RealChild mctx mref cctx cref c y := ⟨w1, w2, hrun⟩
    exact Or.inr ⟨rfl, hr, fun m' hm' => cacheInv_insert hm' hr⟩

/-- Every run of the memoised entry returns a real-entry result, given that
the cache's reads satisfy the invariant. -/
theorem synthesizeChild_real {mctx mref cctx cref} (hc : CacheReads mctx mref cctx cref)
    {c : Name} {w w'} {y : Sparkle.IR.AST.Module × Sparkle.IR.AST.Design}
    (h : RunsTo (synthesizeChild c) mctx mref cctx cref w y w') :
    RealChild mctx mref cctx cref c y := by
  obtain ⟨m, w1, hget, hor⟩ := synthesizeChild_run h
  rcases hor with hhit | ⟨_, hr, _⟩
  · exact hc _ _ _ hget c y hhit
  · exact hr

/-- **`ChildSynthIs` from the ref's content and the cache's reads.** -/
theorem childSynthIs_of {mctx mref cctx cref} (href : RefIs mctx mref cctx cref)
    (hc : CacheReads mctx mref cctx cref) : ChildSynthIs mctx mref cctx cref := by
  intro w r w' hget
  refine ⟨synthesizeChild, href w r w' hget, fun c w1 y w2 hrun => synthesizeChild_real hc hrun⟩

/-- `RefIs ∧ CacheReads` at the contexts of a `ChildSynthIs …` type (for the generators). -/
def splitOf (hsynT : Lean.Expr) : MetaM Lean.Expr := do
  let args := (← whnfR hsynT).getAppArgs
  unless args.size == 4 do throwError "not a ChildSynthIs premise: {hsynT}"
  mkAppM ``And #[mkAppN (mkConst ``RefIs) args, mkAppN (mkConst ``CacheReads) args]

/-- `ChildSynthIs` from a proof of `RefIs ∧ CacheReads` (for the generators). -/
def synOf (p : Lean.Expr) : MetaM Lean.Expr := do
  mkAppM ``childSynthIs_of #[← mkAppM ``And.left #[p], ← mkAppM ``And.right #[p]]

end Tools.ShippingChildCache
