import Tools.ShippingCacheCoherent
import Tools.ShippingModuleName
import Tools.ShippingCallsSame
import Tools.ShippingDesignWriterRun

/-! # Coherence of the child cache at the run level: provenance, and what is still missing

`Tools.ShippingCacheCoherent` left step (b) (PRESERVATION) as the premise `hE`
of `synthesizeChild_coherent`: "the real entry's result `Fits` the cache its
run ends in". With module names injective in the declaration name
(`Tools.ShippingModuleName.ofDecl_injective`, `ofDecl_ne_ofMem`,
`ofMem_injective`) that premise is no longer false of the compiler, and it
can be cut down to facts that say WHERE a result's modules come from. This
file does the cutting; `docs/parallel/A-cache-coherence-2.md` has the reading
of the compiler behind each statement.

## The invariant that is preserved: `Prov`

`Prov m` (a property of the cache CONTENT alone):

* the module of the entry under `c` is named `ofDecl c`;
* every module of an entry's design is a built memory module (`IsMem`) or
  the module of an entry of `m` (`IsTop m`).

`coherent_of_prov : Prov m → Coherent m` — PURE, and the only place the
injectivity of the names is used: two modules of one name are two memory
modules of the same parameters, or the modules of ONE entry.

## What is proved here (WRITTEN, NOT BUILT)

Pure:
* `prov_empty`, `prov_insert` (a `Fresh` result under an absent key),
  `coherent_of_prov`, `fits_of_fresh` (the old `Fits` from `Fresh`),
  `fresh_post` (the entry's post passes keep `Fresh`: no module of the
  design is named as the declaration, so the design is left as it is).

From the EXISTING run laws (`RefLaws`, `BodyRel` — nothing new assumed):
* `entry_sub`, `child_sub` (+ `_runs`): a run of the real entry / of the
  memoised entry from an invariant world of positive depth keeps EVERY entry
  the cache has, with its value — on every outcome, a throwing run included.
  (The invariance theorem at the auxiliary predicate `SubMap mb`; the one-key
  form is `Tools.ShippingCallsSame.synthesizeChild_pin`.) So: no entry that
  exists when a run starts is removed, replaced or overwritten by that run.
* `full_split`: a returning run of the full entry is a returning run of the
  core entry followed by the post passes, which leave the cache.

Relative to the residual (below):
* `synthesizeChild_prov`: the REAL memoised entry keeps `Prov` on a returning
  run — hit: nothing changes; miss: the core run (`CoreFresh`), the post
  passes (`fresh_post`), the insert (`prov_insert`).
* `synthesizeChild_coherent_run`: hence `Coherent` of the end cache. This is
  `synthesizeChild_coherent` with its premise `hE` replaced by `CoreFresh`.

## The residual: `CoreFresh L c` — a STATEMENT, not derived

A returning run of the CORE entry of `c` from an invariant world of positive
depth whose cache satisfies `Prov` and does not hold `c` ends in a cache
that satisfies `Prov`, does not hold `c`, and for which the result is
`Fresh`. Three facts are inside it, none derivable from the present laws:

1. the result's module is named `ofDecl c` and the modules of its design are
   memory modules or modules of cache entries — a statement about the
   RESULT and the builder state of every arm of the entry; the existing
   `Keeps` theorems speak of worlds only;
2. the run's nested child syntheses keep `Prov` (the recursion: it needs 1
   for every nested child, by the induction on the depth that `entry_keeps`
   does for the invariant `J`);
3. the run does not insert its own key (no declaration is a descendant of
   itself): a property of the environment, which `RunsTo` / `RefLaws` do
   not model. `entry_sub` gives the other half (what was there stays).

`RefLaws.aux` cannot carry `Prov`: `auxInsert` must hold for EVERY inserted
value. -/
namespace Tools.ShippingCacheCoherentRun
open Lean Meta
open Sparkle.Compiler.Elab
open Sparkle.IR.ModuleName (ofDecl ofMem)
open Sparkle.Compiler.MachMemory (memModule)
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingChildInv Tools.ShippingCallsKidsS Tools.ShippingCacheCoherent
open Tools.ShippingModuleName (ofDecl_injective ofDecl_ne_ofMem ofMem_injective)

/-! ## The invariant -/

/-- A built memory module (`MachMemory.memModule`; never compiled, never in
the cache). -/
def IsMem (a : Sparkle.IR.AST.Module) : Prop :=
  ∃ (cb : Bool) (aw dw : Nat), a = (memModule cb aw dw).1

/-- The module of an entry of `m`. -/
def IsTop (m : Std.HashMap Name Res) (a : Sparkle.IR.AST.Module) : Prop :=
  ∃ (c : Name) (y : Res), m.get? c = some y ∧ a = y.1

/-- **Provenance**: an entry's module is named after its key, and every
module of its design is a memory module or the module of an entry. -/
def Prov (m : Std.HashMap Name Res) : Prop :=
  ∀ (c : Name) (y : Res), m.get? c = some y →
    y.1.name = ofDecl c ∧ ∀ a ∈ y.2.modules, IsMem a ∨ IsTop m a

/-- What a result must satisfy to be inserted under `c`: the key is absent,
the module is named after it, the design's modules have a provenance in `m`. -/
def Fresh (m : Std.HashMap Name Res) (c : Name) (r : Res) : Prop :=
  m.get? c = none ∧ r.1.name = ofDecl c ∧ ∀ a ∈ r.2.modules, IsMem a ∨ IsTop m a

/-- Every entry of `mb` is an entry of `m`, with its value. -/
def SubMap (mb m : Std.HashMap Name Res) : Prop :=
  ∀ (k : Name) (y : Res), mb.get? k = some y → m.get? k = some y

theorem memModule_name (cb : Bool) (aw dw : Nat) :
    (memModule cb aw dw).1.name = ofMem cb aw dw := rfl

/-! ## Pure: `Prov` gives `Coherent` -/

/-- A module an entry holds is a memory module or an entry's module. -/
theorem kind_of_mem {m : Std.HashMap Name Res} (h : Prov m) {c : Name} {y : Res}
    (hy : m.get? c = some y) {a : Sparkle.IR.AST.Module} (ha : a ∈ mods y) :
    IsMem a ∨ IsTop m a := by
  rcases List.mem_cons.mp ha with h1 | h1
  · exact Or.inr ⟨c, y, hy, h1⟩
  · exact (h c y hy).2 a h1

/-- **Two modules with a provenance and one name are one module** — here
the names' injectivity is used: memory against memory (`ofMem_injective`),
memory against declaration (`ofDecl_ne_ofMem`), declaration against
declaration (`ofDecl_injective`: one key, one entry). -/
theorem eq_of_kinds {m : Std.HashMap Name Res} (h : Prov m)
    {a b : Sparkle.IR.AST.Module} (ha : IsMem a ∨ IsTop m a) (hb : IsMem b ∨ IsTop m b)
    (hn : a.name = b.name) : a = b := by
  rcases ha with ⟨cb, aw, dw, ea⟩ | ⟨c, y, hy, ea⟩
  · rcases hb with ⟨cb', aw', dw', eb⟩ | ⟨c', y', hy', eb⟩
    · have e : ofMem cb aw dw = ofMem cb' aw' dw' := by
        rw [← memModule_name cb aw dw, ← memModule_name cb' aw' dw', ← ea, ← eb]
        exact hn
      obtain ⟨h1, h2, h3⟩ := ofMem_injective e
      rw [ea, eb, h1, h2, h3]
    · have e : ofDecl c' = ofMem cb aw dw := by
        rw [← memModule_name cb aw dw, ← ea, ← (h c' y' hy').1, ← eb]
        exact hn.symm
      exact absurd e (ofDecl_ne_ofMem c' cb aw dw)
  · rcases hb with ⟨cb', aw', dw', eb⟩ | ⟨c', y', hy', eb⟩
    · have e : ofDecl c = ofMem cb' aw' dw' := by
        rw [← memModule_name cb' aw' dw', ← eb, ← (h c y hy).1, ← ea]
        exact hn
      exact absurd e (ofDecl_ne_ofMem c cb' aw' dw')
    · have e : ofDecl c = ofDecl c' := by
        rw [← (h c y hy).1, ← (h c' y' hy').1, ← ea, ← eb]
        exact hn
      have hcc : c = c' := ofDecl_injective e
      rw [hcc, hy'] at hy
      have hyy : y' = y := Option.some.inj hy
      rw [ea, eb, hyy]

/-- **`Prov` implies `Coherent`.** -/
theorem coherent_of_prov {m : Std.HashMap Name Res} (h : Prov m) : Coherent m := by
  intro c y c' y' hy hy' a ha b hb hn
  exact eq_of_kinds h (kind_of_mem h hy ha) (kind_of_mem h hy' hb) hn

/-! ## Pure: initial, insert -/

theorem prov_empty : Prov ({} : Std.HashMap Name Res) := by
  intro c y h
  simp at h

theorem sub_refl (m : Std.HashMap Name Res) : SubMap m m := fun _ _ h => h

theorem sub_trans {m0 m1 m2 : Std.HashMap Name Res} (h1 : SubMap m0 m1) (h2 : SubMap m1 m2) :
    SubMap m0 m2 := fun k y h => h2 k y (h1 k y h)

/-- An entry's module stays an entry's module in a larger cache. -/
theorem isTop_mono {m m' : Std.HashMap Name Res} (hs : SubMap m m') {a : Sparkle.IR.AST.Module}
    (h : IsTop m a) : IsTop m' a := by
  obtain ⟨c, y, hy, e⟩ := h
  exact ⟨c, y, hs c y hy, e⟩

/-- An insert under an absent key keeps every entry. -/
theorem sub_insert_absent {m : Std.HashMap Name Res} {c : Name} (r : Res)
    (hc : m.get? c = none) : SubMap m (m.insert c r) := by
  intro k y hk
  rw [Std.HashMap.get?_insert]
  split
  · rename_i heq
    have : c = k := by simpa using heq
    rw [this] at hc
    rw [hc] at hk
    cases hk
  · exact hk

/-- **An insert of a `Fresh` result keeps `Prov`.** -/
theorem prov_insert {m : Std.HashMap Name Res} {c : Name} {r : Res}
    (h : Prov m) (hf : Fresh m c r) : Prov (m.insert c r) := by
  obtain ⟨hc, hname, hd⟩ := hf
  have hs : SubMap m (m.insert c r) := sub_insert_absent r hc
  intro c1 y1 h1
  rw [Std.HashMap.get?_insert] at h1
  split at h1
  · rename_i heq
    have hcc : c = c1 := by simpa using heq
    have hry : r = y1 := Option.some.inj h1
    rw [← hry, ← hcc]
    exact ⟨hname, fun a ha => (hd a ha).imp id (isTop_mono hs)⟩
  · obtain ⟨hn1, hd1⟩ := h c1 y1 h1
    exact ⟨hn1, fun a ha => (hd1 a ha).imp id (isTop_mono hs)⟩

/-- `Fits` (the premise of `Tools.ShippingCacheCoherent.coherent_insert`)
from `Prov` and `Fresh`. -/
theorem fits_of_fresh {m : Std.HashMap Name Res} {c : Name} {r : Res}
    (h : Prov m) (hf : Fresh m c r) : Fits m r := by
  have hco : Coherent (m.insert c r) := coherent_of_prov (prov_insert h hf)
  have hs : SubMap m (m.insert c r) := sub_insert_absent r hf.1
  have hr : (m.insert c r).get? c = some r := by simp
  exact ⟨fun a ha b hb hn => hco c r c r hr hr a ha b hb hn,
    fun c' y' hy' a ha b hb hn => hco c r c' y' hr (hs c' y' hy') a ha b hb hn⟩

/-- **The post passes keep `Fresh`.** The full entry's module has the core
module's name, and its design is the core design when no module of that
design is named as the core module (`full_split`) — which holds: a module
with a provenance is named `ofMem …` or `ofDecl c'` with `c'` IN the cache,
and `c` is not. -/
theorem fresh_post {m : Std.HashMap Name Res} {c : Name}
    {M M' : Sparkle.IR.AST.Module} {D D' : Sparkle.IR.AST.Design}
    (h : Prov m) (hf : Fresh m c (M, D)) (hname : M'.name = M.name)
    (hmods : (∀ x ∈ D.modules, x.name ≠ M.name) → D'.modules = D.modules) :
    Fresh m c (M', D') := by
  obtain ⟨hc, hn, hd⟩ := hf
  have hn' : M.name = ofDecl c := hn
  have hno : ∀ x ∈ D.modules, x.name ≠ M.name := by
    intro x hx e
    rcases hd x hx with ⟨cb, aw, dw, ex⟩ | ⟨c', y', hy', ex⟩
    · have e' : ofDecl c = ofMem cb aw dw := by
        rw [← memModule_name cb aw dw, ← ex, ← hn']
        exact e.symm
      exact ofDecl_ne_ofMem c cb aw dw e'
    · have e' : ofDecl c' = ofDecl c := by
        rw [← (h c' y' hy').1, ← ex, ← hn']
        exact e
      have hcc : c' = c := ofDecl_injective e'
      rw [hcc, hc] at hy'
      cases hy'
  have hD : D'.modules = D.modules := hmods hno
  refine ⟨hc, ?_, fun a ha => ?_⟩
  · show M'.name = ofDecl c
    rw [hname]
    exact hn'
  · have ha' : a ∈ D.modules := by
      rw [← hD]
      exact ha
    exact hd a ha'

/-! ## From the existing run laws: every entry is kept -/

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- The closure condition of `RefLaws.aux` for "every entry of `mb` is kept":
a miss inserts under a key the map did not have at the lookup, hence not a
key of `mb`. -/
theorem sub_insert (mb : Std.HashMap Name Res) :
    ∀ (m0 m1 : Std.HashMap Name Res) (n : Name) (r : Res),
      SubMap mb m0 → m0.get? n = none → SubMap mb m1 → SubMap mb (m1.insert n r) := by
  intro m0 m1 n r h0 hn h1 k y hk
  rw [Std.HashMap.get?_insert]
  split
  · rename_i heq
    have hnk : n = k := by simpa using heq
    have h0k : m0.get? k = some y := h0 k y hk
    rw [← hnk, hn] at h0k
    cases h0k
  · exact h1 k y hk

/-- **A run of the real entry keeps every entry of the cache** — returning
or throwing — from an invariant world of POSITIVE depth. (At depth 0 the
entry clears the cache.) -/
theorem entry_sub (L : RefLaws mref cref) (hB : ∀ L' : RefLaws mref cref, BodyRel L')
    {c : Name} {w : Void IO.RealWorld} (hw : InvV L w) (hd : L.dval w ≠ 0) :
    SubMap (L.val w) (L.val (endW mctx mref cctx cref (synthesizeCombinational c) w)) := by
  have hs : SubMap (L.val w) (L.val w) := sub_refl _
  have := entry_keeps_all (mctx := mctx) (cctx := cctx)
    (L.withAux (SubMap (L.val w)) (sub_insert (L.val w))) (hB _) (L.dval w)
    (fun h => absurd h hd) c w ⟨hw, rfl, hs⟩
  exact this.1.2.2

theorem entry_sub_runs (L : RefLaws mref cref) (hB : ∀ L' : RefLaws mref cref, BodyRel L')
    {c : Name} {w w' : Void IO.RealWorld} {r : Res} (hw : InvV L w) (hd : L.dval w ≠ 0)
    (h : RunsTo (synthesizeCombinational c) mctx mref cctx cref w r w') :
    SubMap (L.val w) (L.val w') := by
  have := entry_sub (mctx := mctx) (cctx := cctx) L hB (c := c) hw hd
  rwa [endW_of_runs h] at this

/-- **A run of the memoised entry keeps every entry of the cache** —
returning or throwing — from an invariant world of positive depth. -/
theorem child_sub (L : RefLaws mref cref) (hB : ∀ L' : RefLaws mref cref, BodyRel L')
    {c : Name} {w : Void IO.RealWorld} (hw : InvV L w) (hd : L.dval w ≠ 0) :
    SubMap (L.val w) (L.val (endW mctx mref cctx cref (synthesizeChild c) w)) := by
  have hs : SubMap (L.val w) (L.val w) := sub_refl _
  have := childKeeps_all (L.withAux (SubMap (L.val w)) (sub_insert (L.val w))) (hB _) (L.dval w)
    (fun h => absurd h hd) mctx cctx c w ⟨hw, rfl, hs⟩
  exact this.1.2.2

theorem child_sub_runs (L : RefLaws mref cref) (hB : ∀ L' : RefLaws mref cref, BodyRel L')
    {c : Name} {w w' : Void IO.RealWorld} {y : Res} (hw : InvV L w) (hd : L.dval w ≠ 0)
    (h : RunsTo (synthesizeChild c) mctx mref cctx cref w y w') :
    SubMap (L.val w) (L.val w') := by
  have := child_sub (mctx := mctx) (cctx := cctx) L hB (c := c) hw hd
  rwa [endW_of_runs h] at this

/-! ## The full entry: the core run, then the post passes -/

/-- **A returning run of the full entry**: a returning run of the core entry
from the same world; the post passes (one environment-variable read, two
pure passes) leave the cache; the module keeps its name; the design is the
core design when no module of it is named as the core module. -/
theorem full_split (L : RefLaws mref cref) {c : Name} {w w' : Void IO.RealWorld}
    {M' : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (h : RunsTo (synthesizeCombinational c) mctx mref cctx cref w (M', D') w') :
    ∃ (M : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design) (w1 : Void IO.RealWorld),
      RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1 ∧
      L.val w' = L.val w1 ∧ M'.name = M.name ∧
      ((∀ x ∈ D.modules, x.name ≠ M.name) → D'.modules = D.modules) := by
  unfold synthesizeCombinational synthesizeCombinationalWith at h
  obtain ⟨⟨M, D⟩, w1, hcore, h⟩ := RunsTo.bind h
  refine ⟨M, D, w1, hcore, ?_⟩
  dsimp only at h
  obtain ⟨_, w2, henv, h⟩ := RunsTo.bind h
  have hv2 : L.val w2 = L.val w1 := (L.same (.ioEnv _) henv).1
  rcases RunsTo.ite h with h | h
  · obtain ⟨he, hww⟩ := RunsTo.pure_world h
    simp only [Prod.mk.injEq] at he
    obtain ⟨h1, h2⟩ := he
    subst h1 h2 hww
    exact ⟨hv2, Tools.ShippingDesignWriterRun.fullEntry_name (Or.inl rfl),
      fun hx => Tools.ShippingKidsChildIface.map_other M.name _ D.modules hx⟩
  · obtain ⟨he, hww⟩ := RunsTo.pure_world h
    simp only [Prod.mk.injEq] at he
    obtain ⟨h1, h2⟩ := he
    subst h1 h2 hww
    refine ⟨hv2, Tools.ShippingDesignWriterRun.fullEntry_name (Or.inr rfl), fun hx => ?_⟩
    show (D.modules.map _).map _ = _
    rw [Tools.ShippingKidsChildIface.map_other M.name _ D.modules hx,
      Tools.ShippingKidsChildIface.map_other M.name _ D.modules hx]

/-! ## The residual, and the memoised entry relative to it -/

/-- **THE RESIDUAL — a statement, NOT a theorem of this file.** A returning
run of the core entry of `c`, from an invariant world of positive depth
whose cache satisfies `Prov` and does not hold `c`: the cache it ends in
satisfies `Prov`, and the result is `Fresh` for it (the key still absent,
the module named `ofDecl c`, the design's modules with a provenance). -/
def CoreFresh (L : RefLaws mref cref) (c : Name) : Prop :=
  ∀ (mctx : Meta.Context) (cctx : Core.Context) (w : Void IO.RealWorld)
    (M : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design) (w1 : Void IO.RealWorld),
    InvV L w → L.dval w ≠ 0 → Prov (L.val w) → (L.val w).get? c = none →
    RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1 →
    Prov (L.val w1) ∧ Fresh (L.val w1) c (M, D)

/-- **The real memoised entry keeps `Prov` on a returning run**, relative to
`CoreFresh` of its declaration. A hit leaves the cache. A miss runs the full
entry — the core run (`CoreFresh`), the post passes (`full_split`,
`fresh_post`) — and inserts its result into the cache as it is after that
run (`prov_insert`). -/
theorem synthesizeChild_prov (L : RefLaws mref cref) {c : Name}
    {w w' : Void IO.RealWorld} {y : Res} (hw : InvV L w) (hd : L.dval w ≠ 0)
    (hp : Prov (L.val w)) (hR : CoreFresh L c)
    (h : RunsTo (synthesizeChild c) mctx mref cctx cref w y w') : Prov (L.val w') := by
  unfold synthesizeChild at h
  obtain ⟨m, w1, hget, h⟩ := RunsTo.bind h
  obtain ⟨hm, hv, -⟩ := L.get hget
  have hw1 : InvV L w1 := invV_framed L .cacheGet hget hw
  have hd1 : L.dval w1 ≠ 0 := by
    rw [(L.same .cacheGet hget).2.2]
    exact hd
  have hp1 : Prov (L.val w1) := by
    rw [hv]
    exact hp
  cases hcm : m.get? c with
  | some r =>
    simp only [hcm] at h
    obtain ⟨-, hww⟩ := RunsTo.pure_world h
    rw [hww]
    exact hp1
  | none =>
    simp only [hcm] at h
    obtain ⟨⟨M', D'⟩, w2, hrun, h⟩ := RunsTo.bind h
    obtain ⟨u, w3, hmod, h⟩ := RunsTo.bind h
    obtain ⟨hv3, -, -⟩ := L.cacheModify _ _ _ _ hmod
    obtain ⟨-, hww⟩ := RunsTo.pure_world h
    obtain ⟨M, D, wc, hcore, hval, hname, hmods⟩ := full_split L hrun
    have hc1 : (L.val w1).get? c = none := by
      rw [hv, ← hm]
      exact hcm
    obtain ⟨hp2, hf⟩ := hR mctx cctx w1 M D wc hw1 hd1 hp1 hc1 hcore
    have hfin : Prov ((L.val wc).insert c (M', D')) :=
      prov_insert hp2 (fresh_post hp2 hf hname hmods)
    rw [hww, hv3, hval]
    exact hfin

/-- **Step (b) at the memoised entry, on a returning run**: `Coherent` of the
end cache. `Tools.ShippingCacheCoherent.synthesizeChild_coherent` with its
premise `hE` replaced by the residual `CoreFresh`. -/
theorem synthesizeChild_coherent_run (L : RefLaws mref cref) {c : Name}
    {w w' : Void IO.RealWorld} {y : Res} (hw : InvV L w) (hd : L.dval w ≠ 0)
    (hp : Prov (L.val w)) (hR : CoreFresh L c)
    (h : RunsTo (synthesizeChild c) mctx mref cctx cref w y w') : Coherent (L.val w') :=
  coherent_of_prov (synthesizeChild_prov L hw hd hp hR h)

end Tools.ShippingCacheCoherentRun
