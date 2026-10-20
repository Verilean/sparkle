import Tools.ShippingChildInv
-- Round par/cbnd. BUILT: cb1 (Init exit 0; Core failed: `C` not in scope in two theorems), cb2 (exit 0 after the integrator added the explicit `(C : RefLawsCore mref cref)` binder to `cacheModify' and depthModify'`); axioms standard (ax1). No `sorry`, no `axiom`, no `native_decide`.
-- Writing-time guesses are marked `-- (writing-time guess, accepted by build cb2: …)`.

/-! # The child boundary `ChildBnd`, split into what it is about

`ChildBnd mref cref w = ∃ L : RefLaws mref cref, StartV L w ∧ L.quiet w`
(`Tools/ShippingChildInv.lean:674`). `StartV` is stated by the witness's VALUE
functions (`L.sval w`, `L.dval w`, `L.val w`), which are fields of the witness,
not the refs' contents. This file reads them back to the refs' contents and
splits the boundary into

* a LAW-FREE start condition about what reads of the three refs return in `w`
  — `StartW` (`ShippingChildInv.lean:486`), or, more primitively, `readOf r w`
  (`ShippingChildInv.lean:102`: the value component of `ST.Ref.get r` run
  on `w`); and
* the existence of a law witness quiet at `w` — `QuietAt` (`ShippingChildInv.lean:473`).

Results (all statements are about existing definitions; nothing is added to
`RefLaws`, no law is assumed):

* `runsTo_get_readOf`: a successful lifted read returns `readOf r w`.
* `refLaws_val_eq` / `refLaws_sval_eq` / `refLaws_dval_eq`: EVERY law witness's value
  functions ARE `readOf` of the three refs (the three value fields are not
  free once the read laws hold).
* `startV_of_startW` / `startW_of_startV`, `childBnd_iff`:
  `ChildBnd w ↔ StartW w ∧ QuietAt w`.
* `startW_of_readOf`, `childBnd_of_init` / `childBnd_of_init_empty`: the
  initial-state form — the synthesis ref holds `some synthesizeChild` and the
  depth ref holds `0` (or the cache holds `{}`) — gives `StartV` for EVERY
  witness, and `ChildBnd` from `QuietAt`.
* `ChildBnd.plain`: the auxiliary predicate of the witness (`aux`,
  `auxInsert`) can always be taken trivial.

What the initial-state hypotheses are NOT: derived. `readOf r w` is the value
of the OPAQUE `ST.Prim.Ref.get` (`@[extern "lean_st_ref_get"] opaque`) at an
opaque world; the repo has no lemma about what `IO.mkRef v` / an `initialize`
leaves in a world, so `readOf sparkleSynthDepth w = 0` etc. at the start world
of a compile stay premises (runtime semantics). See
`docs/parallel/childbnd-residual.md`. -/

namespace Tools.ShippingChildBndInit
open Lean Meta
open Tools.ShippingEntrySoundness
open Tools.ShippingMachineEntry
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-! ## 1. A successful read returns `readOf` -/

/-- **A successful lifted read of `r` from `w` returns `readOf r w`** — by the
definition of the lift (the same unfolding `refGet_runs` uses), no law. -/
theorem runsTo_get_readOf {σ : Type} (r : IO.Ref σ) {w : Void IO.RealWorld} {a : σ}
    {w' : Void IO.RealWorld}
    (h : RunsTo (ST.Ref.get r : MetaM σ) mctx mref cctx cref w a w') : a = readOf r w := by
  unfold RunsTo at h
  -- (writing-time guess, accepted by build cb2: the same `change` as in `refGet_runs`, ShippingChildInv.lean:690, here on a hypothesis)
  change (match (ST.Ref.get r : ST IO.RealWorld σ) w with | .mk a s => EST.Out.ok a s) = _ at h
  cases hg : (ST.Ref.get r : ST IO.RealWorld σ) w with
  | mk b s =>
    -- (writing-time guess, accepted by build cb2: `rw [hg]` finds the discriminant inside `readOf`'s match and closes by `rfl`)
    have hr : readOf r w = b := by unfold readOf; rw [hg]; try rfl
    rw [hg] at h
    change EST.Out.ok b s = EST.Out.ok a w' at h
    injection h with h1 _
    rw [hr, h1]

/-! ## 2. Every witness's values are the refs' contents -/

/-- The cache value of ANY witness is what the cache holds. (The contexts only
serve to run a read; any will do.) -/
theorem refLaws_val_eq (L : RefLaws mref cref) (mctx : Meta.Context) (cctx : Core.Context) (w : Void IO.RealWorld) :
    L.val w = readOf sparkleChildCache w := by
  obtain ⟨m, w1, hg⟩ := refGet_runs (mctx := mctx) (mref := mref) (cctx := cctx) (cref := cref)
    sparkleChildCache w
  rw [← L.cacheGet _ _ _ hg]
  exact runsTo_get_readOf sparkleChildCache hg

theorem refLaws_sval_eq (L : RefLaws mref cref) (mctx : Meta.Context) (cctx : Core.Context) (w : Void IO.RealWorld) :
    L.sval w = readOf sparkleChildSynth w := by
  obtain ⟨s, w1, hg⟩ := refGet_runs (mctx := mctx) (mref := mref) (cctx := cctx) (cref := cref)
    sparkleChildSynth w
  rw [← L.synthGet _ _ _ hg]
  exact runsTo_get_readOf sparkleChildSynth hg

theorem refLaws_dval_eq (L : RefLaws mref cref) (mctx : Meta.Context) (cctx : Core.Context) (w : Void IO.RealWorld) :
    L.dval w = readOf sparkleSynthDepth w := by
  obtain ⟨d, w1, hg⟩ := refGet_runs (mctx := mctx) (mref := mref) (cctx := cctx) (cref := cref)
    sparkleSynthDepth w
  rw [← L.depthGet _ _ _ hg]
  exact runsTo_get_readOf sparkleSynthDepth hg

/-! ## 3. The start condition, law-free -/

/-- What a read of the synthesis ref returns, from its contents. -/
theorem synthAt_of_readOf {w : Void IO.RealWorld}
    (h : readOf sparkleChildSynth w = some synthesizeChild) : SynthAt mref cref w :=
  fun _ _ s _ hg => (runsTo_get_readOf sparkleChildSynth hg).trans h

/-- What a read of the cache returns, from its contents. -/
theorem cacheAt_of_readOf {w : Void IO.RealWorld}
    (h : CacheInv mref cref (readOf sparkleChildCache w)) : CacheAt mref cref w := by
  intro _ _ m _ hg
  rw [runsTo_get_readOf sparkleChildCache hg]
  exact h

/-- **The initial-state form of the law-free start condition**: the synthesis
ref holds `some synthesizeChild`, and the depth ref holds `0` or the cache's
entries are `RealChild`s. -/
theorem startW_of_readOf {w : Void IO.RealWorld}
    (hs : readOf sparkleChildSynth w = some synthesizeChild)
    (hd : readOf sparkleSynthDepth w = 0 ∨ CacheInv mref cref (readOf sparkleChildCache w)) :
    StartW mref cref w := by
  refine ⟨synthAt_of_readOf hs, ?_⟩
  rcases hd with hd | hc
  · exact Or.inl fun _ _ d _ hg => (runsTo_get_readOf sparkleSynthDepth hg).trans hd
  · exact Or.inr (cacheAt_of_readOf hc)

/-- The converse: the law-free start condition, read back to the contents
(the contexts only run the reads). -/
theorem readOf_of_startW (mctx : Meta.Context) (cctx : Core.Context) {w : Void IO.RealWorld}
    (h : StartW mref cref w) :
    readOf sparkleChildSynth w = some synthesizeChild ∧
      (readOf sparkleSynthDepth w = 0 ∨ CacheInv mref cref (readOf sparkleChildCache w)) := by
  obtain ⟨hs, hd⟩ := h
  refine ⟨?_, ?_⟩
  · obtain ⟨s, w1, hg⟩ := refGet_runs (mctx := mctx) (mref := mref) (cctx := cctx) (cref := cref)
      sparkleChildSynth w
    rw [← runsTo_get_readOf sparkleChildSynth hg]
    exact hs mctx cctx s w1 hg
  · rcases hd with hd | hc
    · obtain ⟨d, w1, hg⟩ := refGet_runs (mctx := mctx) (mref := mref) (cctx := cctx) (cref := cref)
        sparkleSynthDepth w
      left
      rw [← runsTo_get_readOf sparkleSynthDepth hg]
      exact hd mctx cctx d w1 hg
    · obtain ⟨m, w1, hg⟩ := refGet_runs (mctx := mctx) (mref := mref) (cctx := cctx) (cref := cref)
        sparkleChildCache w
      right
      rw [← runsTo_get_readOf sparkleChildCache hg]
      exact hc mctx cctx m w1 hg

/-! ## 4. `StartV` from the law-free start condition, for EVERY witness -/

/-- **`StartV` of any witness from the law-free start condition** (by the
witness's read laws; the same steps as `invV_of_invW`). The premise speaks of
what reads return, not of the witness. -/
theorem startV_of_startW (L : RefLaws mref cref) (mctx : Meta.Context) (cctx : Core.Context)
    {w : Void IO.RealWorld} (h : StartW mref cref w) : StartV L w := by
  obtain ⟨hs, hd⟩ := readOf_of_startW mctx cctx h
  refine ⟨(refLaws_sval_eq L mctx cctx w).trans hs, ?_⟩
  rcases hd with hd | hc
  · exact Or.inl ((refLaws_dval_eq L mctx cctx w).trans hd)
  · right
    rw [refLaws_val_eq L mctx cctx w]
    exact hc

/-- The converse (no contexts needed: a read that ran gives them). -/
theorem startW_of_startV (L : RefLaws mref cref) {w : Void IO.RealWorld} (h : StartV L w) :
    StartW mref cref w := by
  refine ⟨fun _ _ s _ hg => by rw [L.synthGet _ _ _ hg]; exact h.1, ?_⟩
  rcases h.2 with hd | hc
  · exact Or.inl fun _ _ d _ hg => by rw [L.depthGet _ _ _ hg]; exact hd
  · exact Or.inr fun _ _ m _ hg => by rw [L.cacheGet _ _ _ hg]; exact hc

/-- **The initialisation lemma.** If, in `w`, the synthesis ref holds
`some synthesizeChild` and the depth ref holds `0` — the state an outermost
compile starts in — then `StartV L w` for EVERY witness `L`. -/
theorem startV_of_init (L : RefLaws mref cref) (mctx : Meta.Context) (cctx : Core.Context)
    {w : Void IO.RealWorld}
    (hs : readOf sparkleChildSynth w = some synthesizeChild)
    (hd : readOf sparkleSynthDepth w = 0) : StartV L w :=
  startV_of_startW L mctx cctx (startW_of_readOf hs (Or.inl hd))

/-- The same with the cache in its initial (empty) state instead of depth 0. -/
theorem startV_of_init_empty (L : RefLaws mref cref) (mctx : Meta.Context) (cctx : Core.Context)
    {w : Void IO.RealWorld}
    (hs : readOf sparkleChildSynth w = some synthesizeChild)
    (hc : readOf sparkleChildCache w = {}) : StartV L w :=
  startV_of_startW L mctx cctx
    (startW_of_readOf hs (Or.inr (by rw [hc]; exact cacheInv_empty)))

/-! ## 5. The boundary split -/

/-- **`ChildBnd` is exactly the law-free start condition together with a law
witness quiet at `w`.** The start-condition half is about what the three refs
hold in `w`; the residual half is `QuietAt` (= `∃ L : RefLaws, L.quiet w`). -/
theorem childBnd_iff (mctx : Meta.Context) (cctx : Core.Context) {w : Void IO.RealWorld} :
    ChildBnd mref cref w ↔ StartW mref cref w ∧ QuietAt mref cref w := by
  constructor
  · rintro ⟨L, hs, hq⟩
    exact ⟨startW_of_startV L hs, L, hq⟩
  · rintro ⟨hs, L, hq⟩
    exact ⟨L, startV_of_startW L mctx cctx hs, hq⟩

/-- **`ChildBnd` from the initial state and the residual.** -/
theorem childBnd_of_init (mctx : Meta.Context) (cctx : Core.Context) {w : Void IO.RealWorld}
    (hq : QuietAt mref cref w)
    (hs : readOf sparkleChildSynth w = some synthesizeChild)
    (hd : readOf sparkleSynthDepth w = 0) : ChildBnd mref cref w :=
  (childBnd_iff mctx cctx).2 ⟨startW_of_readOf hs (Or.inl hd), hq⟩

theorem childBnd_of_init_empty (mctx : Meta.Context) (cctx : Core.Context)
    {w : Void IO.RealWorld} (hq : QuietAt mref cref w)
    (hs : readOf sparkleChildSynth w = some synthesizeChild)
    (hc : readOf sparkleChildCache w = {}) : ChildBnd mref cref w := by
  obtain ⟨L, hq⟩ := hq
  exact ⟨L, startV_of_init_empty L mctx cctx hs hc, hq⟩

/-- **The auxiliary predicate is never a premise**: from a boundary witness,
one whose `aux` is `True` everywhere (`RefLaws.plain`; the values and
`quiet` are unchanged, `ShippingCallsSame.lean:87-90`). -/
theorem ChildBnd.plain {w : Void IO.RealWorld} (h : ChildBnd mref cref w) :
    ∃ L : RefLaws mref cref, StartV L w ∧ L.quiet w ∧ ∀ m, L.aux m := by
  obtain ⟨L, hs, hq⟩ := h
  -- (writing-time guess, accepted by build cb2: `StartV L.plain w` / `L.plain.quiet w` are `StartV L w` / `L.quiet w` by `rfl`,
  -- as `withAux_sval` / `withAux_quiet` are)
  exact ⟨L.plain, hs, hq, fun _ => trivial⟩

end Tools.ShippingChildBndInit
