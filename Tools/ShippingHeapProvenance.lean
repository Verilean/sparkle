import Tools.ShippingHeapModel
-- NOT YET BUILT (written without running Lean; round par/heapw, base 37dc265f).
-- No `sorry`, no `axiom`, no `native_decide`, no new law / trusted field.
-- Writing-time guesses (for the integrator), each also marked `-- guess: Hn` at its site:
--   H1 term-mode structural recursion / dependent pattern matching on the `Prop`-valued
--      families `Step`, `Reach`, `FramedW` (indices are variables in every signature);
--      fallback: `induction` / `cases` tactics.
--   H2 defeq closes the per-constructor goals: `(hset (.cache) v h).next` ≡ `h.next`,
--      `(alloc v h).2.next` ≡ `h.next + 1`, `endW (getM r) h` ≡ `h`,
--      `endW (modifyM (.other n) f) h` ≡ `hset (.other n) (f (hget (.other n) h)) h`,
--      `endW (modifyGetM …) h` ≡ `hset (.other n) (f (hget …)).2 h` (all reductions of
--      `bindM`'s match on a constructor, as `endW_modifyM := rfl` in the model file).
--   H3 `runsTo_endW`: `unfold endW; rw [e]` closes (the `first` combinator tries
--      `rfl` / `simp only` as fallbacks).
--   H4 `have e2 : RefId.other n = RefId.cache := e` (defeq through `Ref.id`), then
--      `cases e2` (constructor clash) / `injection e2 with e3` (gives `n = m`).
--   H5 `injection` on `Out.ok … = Out.ok r h1` then `subst` of the two equations (the
--      variable on the right-hand side), as G3 in the model file.
--   H6 `⟨v, rfl⟩ : AllocIn {h with next := 0} (.other 0) _` (the `RunsTo` definition is
--      unfolded by the elaborator when checking `rfl`).

/-! # World-indexed provenance in the pure heap model

**Why this file.** `MkRefd σ r` (`Tools/ShippingChildFresh.lean`) says that
SOME run of `IO.mkRef`, in SOME contexts, from SOME world, returned `r`. It is a
history over ANOTHER world: it does NOT say that `r` is fresh relative to the
refs that exist in the run that uses it, and it does NOT prove non-alias /
`FreshIn` in that run. `MkRefd` is NOT a solution of the provenance item and
this file does not make it one. The model analogue of that gap is proved below
(`history_elsewhere_aliases`): an allocation history in another world returns a
ref that is a pre-existing (valid) ref of the use world.

**What this file does — in the pure model of `Tools/ShippingHeapModel.lean`
only.** It indexes provenance by worlds of ONE run:

* `Step W Tk h h'` — one primitive step (a read; a write to a tracked cell,
  allowed only if `Tk`; a write to `other n`, allowed only if `W n`; an
  allocation). `Reach W Tk` — its reflexive-transitive closure (the worlds of a
  run built from the model's primitives). `FramedW σ W p` — the ref-only framed
  actions of `FramedR` whose writes go to cells in `W`; a run of one is a `Step`
  (`FramedW.step`, `FramedW.step_of_runs`).
* `Reach.next_le` (the allocation pointer is monotone), `Reach.other_below`
  (every cell `< h.next` outside `W` is unchanged: cells of the start world are
  changed only by explicit writes), `Reach.keeps` (no tracked writes ⇒ `cv/sv/dv`
  and the registry kept).
* `AllocIn h r h1` — `r` was returned by `allocM v` run from `h` (THIS world)
  ending in `h1`; `allocIn_spec` (`r = other h.next`, `h1.next = h.next + 1`).
* `Prov W Tk h r h2` — WORLD-INDEXED provenance: from the run's start world `h`
  the run reaches an allocation world `h0`, allocates `r` there (ending in `h1`)
  and reaches the use world `h2` (`Reach h h0`, `AllocIn h0 r h1`,
  `Reach h1 h2`).
* `Valid r h` — `r` exists in `h` (tracked, or `other n` with `n < h.next`);
  `Valid.reach` (preserved from allocation world to use world),
  `prov_valid`.
* DERIVED non-alias: `allocIn_ne_valid` (the allocated id differs from every
  ref valid before the allocation, the three tracked refs included),
  `prov_ne_valid` (a `Prov` ref differs from every ref valid at the run's START
  world — side refs and earlier local refs, if they are valid there),
  `prov_ne_cache/synth/depth`, `prov_alloc_distinct` (two allocations in
  sequence are distinct).
* DERIVED frame at the use world: `prov_set_frame`, `prov_modify_frame` — for a
  `Prov` ref `r` and ANY later use world `h2`, `setM r v` / `modifyM r f` keeps
  `cv/sv/dv`, the registry, and the contents of every ref valid at the start
  world; and reads back `v`. `prov_cell_kept`: the contents of a `Prov` ref
  survive later steps that do not write its cell.

## Table: the new boundary's frame (`RefLawsAOps.frame` / `frameQ` at `FramedA`,
`Tools/ShippingChildInvA.lean:139-204, 263-294`) vs this model

| `FramedA` constructor(s) | model analogue | status |
|---|---|---|
| `cacheGet`, `synthGet`, `depthGet` | `getM` of a tracked ref, `Step.read` | frame derived in the model (HM `FramedR.keeps`) |
| `sideGet/Set/Modify/ModifyGet` (+ `IO` lifts) | `FramedR.other*` on `other n` | `cv/sv/dv` frame derived in the model (HM); non-alias of a side ref with a local ref derived in the model (`prov_ne_valid`) IF the side ref is `Valid` at the run's start world — that the real side refs are such cells is part of the fit, OPEN |
| `mkExprCache`, `localMk` | `allocM`, `Step.allocate`, `AllocIn` | `cv/sv/dv` frame derived in the model (HM); freshness against every ref valid before derived in the model (`allocIn_ne_valid`) |
| `exprCacheGet(IO)`, `localGet(IO)` | `getM` of a `Prov` ref | frame derived in the model (reads leave the heap); provenance not needed for the frame |
| `localSet(IO)`, `localModify(IO)`, `exprCacheModify` | `setM`/`modifyM` of a `Prov` ref | `cv/sv/dv` + registry frame derived in the model (`prov_set_frame`, `prov_modify_frame`); non-alias with every ref valid at the run's start derived in the model, from `Prov` (THIS run's history), not assumed |
| `ioEnv`, `constInfo`, `env`, `fvarThrowUnknown`, `whnf`, `inferType`, `isClass?`, `whnfUntil`, `instantiateForall`, `mkLambdaFVars`, `mkAppM`, `unfoldDefinition?`, `reduce`, `metaGet`, `metaModify`, `coreModifyTrace`, `freshFVar`, `monoMs` | none (Meta primitives) | OPEN — stay assumptions |
| `RefLawsAOps.diag`, `telescope`/`lamTelescope`/`localDecl`/`letDecl` fields, `excOk` on Lean's exceptions (`OkExc`), `quiet` as a runtime predicate, `AdmCtx` | none | OPEN — stay assumptions |

Caveat on the tracked-ref non-alias: in this model the tracked cells and the
`other n` cells are DIFFERENT constructors of `Ref`, so a write to any
`other n` leaves `cv/sv/dv` by construction, with or without provenance. What
`Prov` adds in the model is non-alias among `other` cells (with side refs and
earlier local refs) and the world bookkeeping. That `IO.Ref`s of the real
runtime behave like this typed separation (no re-typed alias of a tracked ref)
is NOT shown here.

**What this file is NOT.** None of this is connected to the real ST runtime:
`ST.Prim.Ref.get/set/mkRef` are `@[extern] opaque` and the world is the opaque
`Void IO.RealWorld`; no statement here mentions `IO.Ref`, `MetaM`, `MkRefd` or
`RefLawsAOps`. The real-runtime fit is a SEPARATE, OPEN item. `MkRefd` remains
NOT a proof of `FreshIn` / non-alias in the run; the provenance item for the
real runtime stays OPEN. No law, field or axiom is added; nothing here
discharges a premise of `RefLawsAOps`.

Audit: `docs/parallel/heap-model-audit.md` §4. -/

namespace Tools.ShippingHeapProvenance

open Tools.ShippingHeapModel

variable {σ : Sig}

/-! ## Steps and reachability -/

/-- One primitive step of a run. Writes to tracked cells need `Tk`; writes to
`other n` need `W n`; reads and allocations are always steps. -/
inductive Step {τ : Sig} (W : Nat → Prop) (Tk : Prop) : Heap τ → Heap τ → Prop
  | read (h : Heap τ) : Step W Tk h h
  | setCache (v : τ.C) (h : Heap τ) : Tk → Step W Tk h (hset (@Ref.cache τ) v h)
  | setSynth (v : τ.S) (h : Heap τ) : Tk → Step W Tk h (hset (@Ref.synth τ) v h)
  | setDepth (v : Nat) (h : Heap τ) : Tk → Step W Tk h (hset (@Ref.depth τ) v h)
  | setOther (n : Nat) (v : τ.O) (h : Heap τ) : W n → Step W Tk h (hset (@Ref.other τ n) v h)
  | allocate (v : τ.O) (h : Heap τ) : Step W Tk h (alloc v h).2

/-- The worlds reached by a run of primitive steps (reflexive-transitive closure). -/
inductive Reach {τ : Sig} (W : Nat → Prop) (Tk : Prop) : Heap τ → Heap τ → Prop
  | refl (h : Heap τ) : Reach W Tk h h
  | step {h1 h2 h3 : Heap τ} : Step W Tk h1 h2 → Reach W Tk h2 h3 → Reach W Tk h1 h3

variable {W : Nat → Prop} {Tk : Prop}

theorem Reach.single {h h' : Heap σ} (s : Step W Tk h h') : Reach W Tk h h' :=
  .step s (.refl h')

-- guess: H1
theorem Reach.trans {h1 h2 h3 : Heap σ} : Reach W Tk h1 h2 → Reach W Tk h2 h3 → Reach W Tk h1 h3
  | .refl _, r => r
  | .step s r1, r => .step s (Reach.trans r1 r)

/-- **The allocation pointer is monotone** along a step. -/
-- guess: H1, H2
theorem Step.next_le {h h' : Heap σ} : Step W Tk h h' → h.next ≤ h'.next
  | .read _ => Nat.le_refl _
  | .setCache _ _ _ => Nat.le_refl _
  | .setSynth _ _ _ => Nat.le_refl _
  | .setDepth _ _ _ => Nat.le_refl _
  | .setOther _ _ _ _ => Nat.le_refl _
  | .allocate _ _ => Nat.le_succ _

/-- **The allocation pointer is monotone** along a run. -/
-- guess: H1
theorem Reach.next_le {h h' : Heap σ} : Reach W Tk h h' → h.next ≤ h'.next
  | .refl _ => Nat.le_refl _
  | .step s r => Nat.le_trans s.next_le (Reach.next_le r)

/-- A step changes a cell `< h.next` only by an explicit write to it. -/
-- guess: H1, H2
theorem Step.other_below {h h' : Heap σ} :
    Step W Tk h h' → ∀ m, m < h.next → ¬ W m → h'.other m = h.other m
  | .read _, _, _, _ => rfl
  | .setCache _ _ _, _, _, _ => rfl
  | .setSynth _ _ _, _, _, _ => rfl
  | .setDepth _ _ _, _, _, _ => rfl
  | .setOther n v h0 hn, m, _, hw => by
      show (if m = n then v else h0.other m) = h0.other m
      exact if_neg (fun e => hw (by rw [e]; exact hn))
  | .allocate v h0, m, hm, _ => by
      show (if m = h0.next then v else h0.other m) = h0.other m
      exact if_neg (Nat.ne_of_lt hm)

/-- **Cells of the start world are changed only by explicit writes**: along a
run, every cell `< h.next` outside `W` keeps its contents. -/
-- guess: H1
theorem Reach.other_below {h h' : Heap σ} :
    Reach W Tk h h' → ∀ m, m < h.next → ¬ W m → h'.other m = h.other m
  | .refl _, _, _, _ => rfl
  | .step s r, m, hm, hw =>
      (Reach.other_below r m (Nat.lt_of_lt_of_le hm s.next_le) hw).trans (s.other_below m hm hw)

/-- Every step keeps the printer registry. -/
-- guess: H1, H2
theorem Step.reg {h h' : Heap σ} : Step W Tk h h' → h'.reg = h.reg
  | .read _ => rfl
  | .setCache _ _ _ => rfl
  | .setSynth _ _ _ => rfl
  | .setDepth _ _ _ => rfl
  | .setOther _ _ _ _ => rfl
  | .allocate _ _ => rfl

/-- A step without tracked writes keeps `cv/sv/dv` and the registry. -/
-- guess: H1, H2
theorem Step.keeps {h h' : Heap σ} :
    Step W False h h' → cv h' = cv h ∧ sv h' = sv h ∧ dv h' = dv h ∧ h'.reg = h.reg
  | .read _ => ⟨rfl, rfl, rfl, rfl⟩
  | .setCache _ _ hf => hf.elim
  | .setSynth _ _ hf => hf.elim
  | .setDepth _ _ hf => hf.elim
  | .setOther _ _ _ _ => ⟨rfl, rfl, rfl, rfl⟩
  | .allocate _ _ => ⟨rfl, rfl, rfl, rfl⟩

/-- A run without tracked writes keeps `cv/sv/dv` and the registry. -/
-- guess: H1
theorem Reach.keeps {h h' : Heap σ} :
    Reach W False h h' → cv h' = cv h ∧ sv h' = sv h ∧ dv h' = dv h ∧ h'.reg = h.reg
  | .refl _ => ⟨rfl, rfl, rfl, rfl⟩
  | .step s r =>
      have a := s.keeps
      have b := Reach.keeps r
      ⟨b.1.trans a.1, b.2.1.trans a.2.1, b.2.2.1.trans a.2.2.1, b.2.2.2.trans a.2.2.2⟩

/-! ## Framed actions with a write set, and their runs as steps -/

/-- The ref-only framed actions of `FramedR` whose writes go to cells in `W`. -/
inductive FramedW (τ : Sig) (W : Nat → Prop) : {α : Type} → M τ α → Prop
  | cacheGet : FramedW τ W (getM (@Ref.cache τ))
  | synthGet : FramedW τ W (getM (@Ref.synth τ))
  | depthGet : FramedW τ W (getM (@Ref.depth τ))
  | otherGet (n : Nat) : FramedW τ W (getM (@Ref.other τ n))
  | otherSet (n : Nat) (v : τ.O) : W n → FramedW τ W (setM (@Ref.other τ n) v)
  | otherModify (n : Nat) (f : τ.O → τ.O) : W n → FramedW τ W (modifyM (@Ref.other τ n) f)
  | otherModifyGet {β : Type} (n : Nat) (f : τ.O → β × τ.O) : W n →
      FramedW τ W (modifyGetM (@Ref.other τ n) f)
  | alloc (v : τ.O) : FramedW τ W (allocM (σ := τ) v)

-- guess: H1
theorem FramedW.toFramedR {α : Type} {p : M σ α} : FramedW σ W p → FramedR σ p
  | .cacheGet => .cacheGet
  | .synthGet => .synthGet
  | .depthGet => .depthGet
  | .otherGet n => .otherGet n
  | .otherSet n v _ => .otherSet n v
  | .otherModify n f _ => .otherModify n f
  | .otherModifyGet n f _ => .otherModifyGet n f
  | .alloc v => .alloc v

-- guess: H1
theorem FramedR.toFramedW {α : Type} {p : M σ α} : FramedR σ p → FramedW σ (fun _ => True) p
  | .cacheGet => .cacheGet
  | .synthGet => .synthGet
  | .depthGet => .depthGet
  | .otherGet n => .otherGet n
  | .otherSet n v => .otherSet n v trivial
  | .otherModify n f => .otherModify n f trivial
  | .otherModifyGet n f => .otherModifyGet n f trivial
  | .alloc v => .alloc v

/-- The end world of a framed action is one step away (no tracked writes). -/
-- guess: H1, H2
theorem FramedW.step {α : Type} {p : M σ α} : FramedW σ W p → ∀ h, Step W False h (endW p h)
  | .cacheGet, h => Step.read h
  | .synthGet, h => Step.read h
  | .depthGet, h => Step.read h
  | .otherGet _, h => Step.read h
  | .otherSet n v hn, h => Step.setOther n v h hn
  | .otherModify n f hn, h => Step.setOther n (f (hget (@Ref.other σ n) h)) h hn
  | .otherModifyGet n f hn, h => Step.setOther n (f (hget (@Ref.other σ n) h)).2 h hn
  | .alloc v, h => Step.allocate v h

/-- A successful run ends in `endW`. -/
theorem runsTo_endW {α : Type} {p : M σ α} {h : Heap σ} {a : α} {h' : Heap σ}
    (hr : RunsTo p h a h') : endW p h = h' := by
  have e : p h = Out.ok a h' := hr
  -- guess: H3
  first
    | (unfold endW; rw [e]; done)
    | (unfold endW; rw [e]; rfl)
    | (simp only [endW, e])

theorem FramedW.step_of_runs {α : Type} {p : M σ α} (hp : FramedW σ W p) {h : Heap σ} {a : α}
    {h' : Heap σ} (hr : RunsTo p h a h') : Step W False h h' := by
  have e := runsTo_endW hr
  subst e
  exact hp.step h

/-! ## Allocation in THIS world -/

/-- `r` was returned by `allocM v` run from `h` (this world), ending in `h1`. -/
def AllocIn (h : Heap σ) (r : Ref σ σ.O) (h1 : Heap σ) : Prop :=
  ∃ v, RunsTo (allocM v) h r h1

theorem allocIn_spec {h : Heap σ} {r : Ref σ σ.O} {h1 : Heap σ} (ha : AllocIn h r h1) :
    r = Ref.other h.next ∧ h1.next = h.next + 1 := by
  obtain ⟨v, hr⟩ := ha
  have e : Out.ok (alloc v h).1 (alloc v h).2 = Out.ok r h1 := hr
  -- guess: H5
  injection e with e1 e2
  subst e1
  subst e2
  exact ⟨rfl, rfl⟩

theorem allocIn_step {h : Heap σ} {r : Ref σ σ.O} {h1 : Heap σ} (ha : AllocIn h r h1) :
    Step W Tk h h1 := by
  obtain ⟨v, hr⟩ := ha
  have e := runsTo_endW hr
  subst e
  exact Step.allocate v h

/-- The fresh-allocation fact: the id is `other n`, `n` at or above the start
world's pointer and below the end world's. -/
def FreshAt (h : Heap σ) (r : Ref σ σ.O) (h1 : Heap σ) : Prop :=
  ∃ n, r = Ref.other n ∧ h.next ≤ n ∧ n < h1.next

theorem allocIn_freshAt {h : Heap σ} {r : Ref σ σ.O} {h1 : Heap σ} (ha : AllocIn h r h1) :
    FreshAt h r h1 := by
  obtain ⟨hr, hn⟩ := allocIn_spec ha
  exact ⟨h.next, hr, Nat.le_refl _, by omega⟩

/-! ## Validity (existence of a ref in a world) -/

/-- `r` exists in `h`: a tracked ref, or `other n` with `n < h.next`. -/
inductive Valid {τ : Sig} : {α : Type} → Ref τ α → Heap τ → Prop
  | cache (h : Heap τ) : Valid (@Ref.cache τ) h
  | synth (h : Heap τ) : Valid (@Ref.synth τ) h
  | depth (h : Heap τ) : Valid (@Ref.depth τ) h
  | other (n : Nat) (h : Heap τ) : n < h.next → Valid (@Ref.other τ n) h

/-- **Valid is preserved** from any world to any world reached from it. -/
theorem Valid.reach {α : Type} {r : Ref σ α} {h h' : Heap σ} (hv : Valid r h)
    (hR : Reach W Tk h h') : Valid r h' := by
  cases hv with
  | cache _ => exact Valid.cache h'
  | synth _ => exact Valid.synth h'
  | depth _ => exact Valid.depth h'
  | other n _ hn => exact Valid.other n h' (Nat.lt_of_lt_of_le hn hR.next_le)

/-- An id at or above a world's pointer differs from every ref valid there
(the tracked refs included). -/
theorem ne_of_valid {β : Type} {r' : Ref σ β} {h : Heap σ} {n : Nat} (hv : Valid r' h)
    (hn : h.next ≤ n) : (@Ref.other σ n).id ≠ r'.id := by
  cases hv with
  | cache _ =>
    intro e
    -- guess: H4
    have e2 : RefId.other n = RefId.cache := e
    cases e2
  | synth _ =>
    intro e
    have e2 : RefId.other n = RefId.synth := e
    cases e2
  | depth _ =>
    intro e
    have e2 : RefId.other n = RefId.depth := e
    cases e2
  | other m _ hm =>
    intro e
    have e2 : RefId.other n = RefId.other m := e
    injection e2 with e3
    omega

theorem allocIn_valid {h : Heap σ} {r : Ref σ σ.O} {h1 : Heap σ} (ha : AllocIn h r h1) :
    Valid r h1 := by
  obtain ⟨hr, hn⟩ := allocIn_spec ha
  subst hr
  exact Valid.other h.next h1 (by omega)

/-- **Non-alias, derived**: the allocated ref differs from every ref valid
before the allocation (tracked refs, side refs, earlier local refs). -/
theorem allocIn_ne_valid {β : Type} {h : Heap σ} {r : Ref σ σ.O} {h1 : Heap σ} {r' : Ref σ β}
    (ha : AllocIn h r h1) (hv : Valid r' h) : r.id ≠ r'.id := by
  obtain ⟨hr, _⟩ := allocIn_spec ha
  subst hr
  exact ne_of_valid hv (Nat.le_refl _)

/-! ## World-indexed provenance: start world → allocation world → use world -/

/-- `r` was allocated DURING the run that starts in `h` and is used in `h2`:
`h` reaches the allocation world `h0`, `allocM` from `h0` returned `r` (ending
in `h1`), and `h1` reaches the use world `h2`. -/
def Prov (W : Nat → Prop) (Tk : Prop) (h : Heap σ) (r : Ref σ σ.O) (h2 : Heap σ) : Prop :=
  ∃ h0 h1, Reach W Tk h h0 ∧ AllocIn h0 r h1 ∧ Reach W Tk h1 h2

theorem prov_of_allocIn {h : Heap σ} {r : Ref σ σ.O} {h1 : Heap σ} (ha : AllocIn h r h1) :
    Prov W Tk h r h1 :=
  ⟨h, h1, .refl h, ha, .refl h1⟩

/-- Provenance extends along later steps of the same run. -/
theorem Prov.extend {h : Heap σ} {r : Ref σ σ.O} {h2 h3 : Heap σ} (hp : Prov W Tk h r h2)
    (hR : Reach W Tk h2 h3) : Prov W Tk h r h3 := by
  obtain ⟨h0, h1, r0, ha, r1⟩ := hp
  exact ⟨h0, h1, r0, ha, r1.trans hR⟩

/-- Provenance gives a fresh id relative to the run's START world. -/
theorem prov_fresh {h : Heap σ} {r : Ref σ σ.O} {h2 : Heap σ} (hp : Prov W Tk h r h2) :
    ∃ n, r = Ref.other n ∧ h.next ≤ n ∧ n < h2.next := by
  obtain ⟨h0, h1, r0, ha, r1⟩ := hp
  obtain ⟨hr, hn⟩ := allocIn_spec ha
  have l0 := r0.next_le
  have l1 := r1.next_le
  exact ⟨h0.next, hr, l0, by omega⟩

/-- A `Prov` ref is valid in the use world. -/
theorem prov_valid {h : Heap σ} {r : Ref σ σ.O} {h2 : Heap σ} (hp : Prov W Tk h r h2) :
    Valid r h2 := by
  obtain ⟨n, hr, _, hlt⟩ := prov_fresh hp
  subst hr
  exact Valid.other n h2 hlt

/-- **Non-alias, derived**: a `Prov` ref differs from every ref valid at the
run's start world. -/
theorem prov_ne_valid {β : Type} {h : Heap σ} {r : Ref σ σ.O} {h2 : Heap σ} {r' : Ref σ β}
    (hp : Prov W Tk h r h2) (hv : Valid r' h) : r.id ≠ r'.id := by
  obtain ⟨n, hr, hn, _⟩ := prov_fresh hp
  subst hr
  exact ne_of_valid hv hn

theorem prov_ne_cache {h : Heap σ} {r : Ref σ σ.O} {h2 : Heap σ} (hp : Prov W Tk h r h2) :
    r.id ≠ (@Ref.cache σ).id := prov_ne_valid hp (Valid.cache h)

theorem prov_ne_synth {h : Heap σ} {r : Ref σ σ.O} {h2 : Heap σ} (hp : Prov W Tk h r h2) :
    r.id ≠ (@Ref.synth σ).id := prov_ne_valid hp (Valid.synth h)

theorem prov_ne_depth {h : Heap σ} {r : Ref σ σ.O} {h2 : Heap σ} (hp : Prov W Tk h r h2) :
    r.id ≠ (@Ref.depth σ).id := prov_ne_valid hp (Valid.depth h)

/-- **Two allocations in sequence are distinct**: a ref allocated in this run
and a ref allocated later from the use world. -/
theorem prov_alloc_distinct {h : Heap σ} {r r' : Ref σ σ.O} {h2 h3 : Heap σ}
    (hp : Prov W Tk h r h2) (ha : AllocIn h2 r' h3) : r.id ≠ r'.id := by
  have hne := allocIn_ne_valid ha (prov_valid hp)
  exact fun e => hne e.symm

/-- A write to a cell at or above the start world's pointer, in ANY later world
`h2`: keeps `cv/sv/dv`, the registry and every ref valid at the start world,
and reads back. -/
theorem fresh_write_frame {h : Heap σ} {n : Nat} (hn : h.next ≤ n) (v : σ.O) (h2 : Heap σ) :
    cv (hset (@Ref.other σ n) v h2) = cv h2 ∧ sv (hset (@Ref.other σ n) v h2) = sv h2 ∧
    dv (hset (@Ref.other σ n) v h2) = dv h2 ∧ (hset (@Ref.other σ n) v h2).reg = h2.reg ∧
    readOf (@Ref.other σ n) (hset (@Ref.other σ n) v h2) = v ∧
    ∀ (β : Type) (r' : Ref σ β), Valid r' h →
      hget r' (hset (@Ref.other σ n) v h2) = hget r' h2 :=
  ⟨rfl, rfl, rfl, rfl, get_set_same _ v h2,
   fun _ r' hv => get_set_other _ r' v h2 (ne_of_valid hv hn)⟩

/-- **The `localSet` / `exprCacheModify` frame, derived in the model** (set
form): for a ref with this run's provenance and ANY use world `h2`. -/
theorem prov_set_frame {h : Heap σ} {r : Ref σ σ.O} {h2 : Heap σ} (hp : Prov W Tk h r h2)
    (v : σ.O) {u : Unit} {h3 : Heap σ} (hr : RunsTo (setM r v) h2 u h3) :
    cv h3 = cv h2 ∧ sv h3 = sv h2 ∧ dv h3 = dv h2 ∧ h3.reg = h2.reg ∧ readOf r h3 = v ∧
    ∀ (β : Type) (r' : Ref σ β), Valid r' h → hget r' h3 = hget r' h2 := by
  obtain ⟨n, hrn, hn, _⟩ := prov_fresh hp
  have e := runsTo_setM r v hr
  subst e
  subst hrn
  exact fresh_write_frame hn v h2

/-- **The `localModify` / `exprCacheModify` frame, derived in the model**
(modify form). -/
theorem prov_modify_frame {h : Heap σ} {r : Ref σ σ.O} {h2 : Heap σ} (hp : Prov W Tk h r h2)
    (f : σ.O → σ.O) {u : Unit} {h3 : Heap σ} (hr : RunsTo (modifyM r f) h2 u h3) :
    cv h3 = cv h2 ∧ sv h3 = sv h2 ∧ dv h3 = dv h2 ∧ h3.reg = h2.reg ∧
    readOf r h3 = f (readOf r h2) ∧
    ∀ (β : Type) (r' : Ref σ β), Valid r' h → hget r' h3 = hget r' h2 := by
  obtain ⟨n, hrn, hn, _⟩ := prov_fresh hp
  have e : h3 = hset r (f (hget r h2)) h2 :=
    (runsTo_endW hr).symm.trans (endW_modifyM r f h2)
  subst e
  subst hrn
  exact fresh_write_frame hn (f (hget (@Ref.other σ n) h2)) h2

/-- The contents of a `Prov` ref survive later steps that do not write its cell. -/
theorem prov_cell_kept {h : Heap σ} {r : Ref σ σ.O} {h2 h3 : Heap σ} (hp : Prov W Tk h r h2)
    {W' : Nat → Prop} {Tk' : Prop} (hR : Reach W' Tk' h2 h3) :
    ∃ n, r = Ref.other n ∧ (¬ W' n → readOf r h3 = readOf r h2) := by
  obtain ⟨n, hrn, _, hlt⟩ := prov_fresh hp
  subst hrn
  exact ⟨n, rfl, fun hw => hR.other_below n hlt hw⟩

/-! ## A history in ANOTHER world is not provenance (the `MkRefd` gap, in the model) -/

/-- **An allocation history over another world does not give freshness**: from
the world `h` with pointer reset to 0, `allocM v` returns `other 0` — and
`other 0` is a PRE-EXISTING (valid) ref of the use world `h` with pointer 1. So
`∃` some world whose allocation returned `r` (the shape of `MkRefd`) does not
imply that `r` is distinct from the refs of the use world. -/
theorem history_elsewhere_aliases (h : Heap σ) (v : σ.O) :
    AllocIn { h with next := 0 } (@Ref.other σ 0) (alloc v { h with next := 0 }).2 ∧
    Valid (@Ref.other σ 0) { h with next := 1 } :=
  -- guess: H6
  ⟨⟨v, rfl⟩, Valid.other 0 _ Nat.zero_lt_one⟩

end Tools.ShippingHeapProvenance
