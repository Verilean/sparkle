import Tools.ShippingChildVertA
-- BUILT by the integrator: ca1 exit 0 (first try; peak 1.9 GB), audit ca2 exit 0 (closures without the old boundary) (worker par/ca, base 6a231b89). Isolated: only the audit
-- Tests/Compiler/ChildVertAuditTest.lean imports it).
-- No `sorry`, no `axiom`, no `native_decide`, no new law / boundary field. Law witness:
-- `O : RefLawsAOps Fresh mref cref` at `hA : AdmCtx O.quiet mctx cctx` only (no old law bundle,
-- no old-to-new conversion, no telescope laws; no old `RealChild`/`CacheInv`/`CacheAt`/`InvW`/
-- `QuietAt`/`J L D`). Fields used: `frame`, `frameQ`, `cacheSet`, `cacheSetQ`,
-- `depthSet`, `depthSetQ` (and, through `keepsA_framed`/`keepsA_diag`, `excOk`/`diag`).
-- Reused law-free lemmas (statements and proofs mention no law bundle):
--   ShippingChildKeeps.lean: `Triple`, `keeps_iff`, `Triple.bind`, `Triple.pure`, `Triple.conseq`,
--     `Triple.of_runs`; ShippingEntrySoundness.lean: `RunsTo`, `RunsTo.bind`;
--   ShippingChildInv.lean: `endW_of_runs`, `refSet_runs`, `refModify_runs`, `RunsTo.pure_world`;
--   ShippingChildBndInit.lean: `runsTo_get_readOf`; ShippingChildBndCore.lean: `cv`/`sv`/`dv`,
--     `modify_split`; ShippingChildInvA.lean: `RefLawsAOps.cacheModify'`/`depthModify'`;
--   ShippingChildVCA.lean: `StableA`, `JQ`, `stableA_JQ`, `keepsA_framed`, `keepsA_diag`.
--   `mapM_loop_hoareA`/`mapM_hoareA` are COPIES of the law-free `mapM_loop_hoare`/`mapM_hoare`
--   (ShippingChildRun.lean:234-264, built), not imported (that file is not in this import chain).
-- UNPROVED PREMISES (named, each a hypothesis of the theorem using it; NOT laws):
--   `hentry` (in `synthesizeChild_realA`, `closeInstsM_realA`): a returning NESTED run of the real
--     entry `synthesizeCombinational c` from a `JQC O D` world ends in `JQC O D` — the cache-coherence
--     half of the nested core run (the analogue of the old `entry_inv`); under the new boundary it
--     is NOT proved here;
--   `hentryT` (in `synthesizeChild_tripleC`): the same as a triple, exceptions in the class.
-- Writing-time guesses (marked `-- guess: Cn` below):
--  C1 the inductive `RealChildA` with the header parameter `O` and the section variables
--     `{Fresh mref cref}`: the recursive occurrence is written `RealChildA O c' r'` (section variables
--     omitted, header parameter given), strictly positive under the `∀`;
--  C2 `CacheInvA O m` is accepted for the constructor's `cache` binder by delta (`exact hw.2`);
--  C3 `cacheInvA_empty`: `simp at h` closes `({} : HashMap).get? c = some r` (as `cacheInv_empty`),
--     fallback `Std.HashMap.get?_empty`;
--  C4 `rw [endW_of_runs h] at hk hq` with `h` on `(sparkleChildCache.get : MetaM _)` /
--     `(sparkleChildSynth.get : MetaM _)` rewrites the end world of `O.frame … FramedA.cacheGet`
--     (resp. `synthGet`) (the `RefLawsAOps.cacheModify'` pattern);
--  C5 `(runsTo_get_readOf _ h).trans hw.1.2.1` unifies `readOf sparkleChildSynth w` with `sv w`;
--  C6 `synthesizeChild_realA` copies the BUILT old `synthesizeChild_inv` (ShippingChildRun.lean:203)
--     step by step (`unfold`, `RunsTo.bind`, `cases hc`, `simp only [hc] at h`, `RunsTo.pure_world`);
--     the inserted function `(·.insert n r)` of the compiler unifies with
--     `fun m : Std.HashMap Name Res => m.insert n r`;
--  C7 `synthesizeChild_tripleC`: after `unfold synthesizeChild`, `Triple.bind` takes the cache read;
--     `cases hc : m.get? n` abstracts the discriminant in the goal, `try dsimp only` reduces the
--     match on `some r`/`none` (and zeta-reduces a `__do_jp`, if any), then `Triple.pure` /
--     `Triple.bind` unify with the branch;
--  C8 `closeInstsM_realA` copies the BUILT old `closeInstsM_inv` (ShippingChildRun.lean:319): the
--     `fun (c, _, _) => synth c` step is accepted against `synthesizeChild x.1` (Prod eta), and
--     `heq.symm` closes the `closeInsts` equation with `machNIn shape`.

/-! # The child cache under the admissible boundary

Witness: `O : RefLawsAOps Fresh mref cref` (the restricted operations laws)
at an admissible context `hA : AdmCtx O.quiet mctx cctx`. The old cache half
(`RealChild`/`CacheInv`/`CacheAt`, ShippingChildInv.lean:444-500) quantified
its quietness over an existential old law witness and its cache over every read; here:

* `RealChildA O c r`: `r` is returned by a run of the real entry
  `synthesizeCombinational c` in an ADMISSIBLE context, from a world that is
  quiet for the FIXED witness (`O.quiet w`), whose synthesis ref holds
  `synthesizeChild` (`sv w`), and whose cache VALUE `cv w` has `RealChildA`
  entries only;
* `CacheInvA O m`: every entry of `m` is a `RealChildA`;
* `JQC O D w := JQ O.quiet D w ∧ CacheInvA O (cv w)`: the vertical
  invariant with its cache half.

Proved:
* `stableA_JQC`: `JQC` is stable — every `FramedA`/diag step keeps it
  (`keepsC_framed`, `keepsC_diag`, through `keepsA_framed`/`keepsA_diag`);
* the depth-0 clear establishes it from `JQ` (`tripleC_clear`, `O.cacheSet`:
  the cache value becomes `{}`), the depth set/modify move it
  (`tripleC_depthSet`, `tripleC_depthModify`), the child insert keeps it when
  the inserted entry is a `RealChildA` (`tripleC_insert`, `jqc_insert_runs`:
  `RefLawsAOps.cacheModify'` = read;write);
* `jqc_cacheGet`: the cache read returns `cv w` (`O.frame` at
  `FramedA.cacheGet` + `runsTo_get_readOf`);
* **`synthesizeChild_realA`**: every returning run of `synthesizeChild n`
  from a `JQC O D` world returns a `RealChildA O n` result and ends in
  `JQC O D` — on a cache HIT the returned value is the cached entry, a
  `RealChildA` by the cache half; on a MISS the nested run starts in a `JQC`
  world (so its result is a `RealChildA`, `RealChildA.of_jqc`) and, by the
  premise `hentry`, ends in one, and the insert keeps `JQC`;
  `synthesizeChild_tripleC`: the same as a triple on every outcome;
* **`closeInstsM_realA`** (endpoint): a returning run of the one-output
  closing `closeInstsM` from a `JQC` world closes with children that are,
  call by call, `RealChildA`s of the call's declaration — cache hits included —
  and ends in `JQC`. -/

namespace Tools.ShippingChildCacheA
open Lean Meta
open Tools.ShippingEntrySoundness
open Tools.ShippingMachineEntry
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv
open Tools.ShippingChildBndInit
open Tools.ShippingChildBndCore
open Tools.ShippingChildInvA
open Tools.ShippingChildFresh
open Tools.ShippingChildVCA

section Defs
variable {Fresh : (σ : Type) → IO.Ref σ → Prop} {mref : ST.Ref IO.RealWorld Meta.State}
  {cref : ST.Ref IO.RealWorld Core.State}

/-- **A real child under the admissible boundary.** `r` is returned by a run
of the real entry on `c`, in an admissible context, from a world that is quiet
for the fixed witness `O`, whose synthesis ref holds `synthesizeChild` and
whose cache value has real-child entries only. -/
inductive RealChildA (O : RefLawsAOps Fresh mref cref) : Name → Res → Prop  -- guess: C1
  | run {c : Name} {r : Res} (mctx : Meta.Context) (cctx : Core.Context)
      (w w' : Void IO.RealWorld)
      (adm : AdmCtx O.quiet mctx cctx)
      (cache : ∀ c' r', (cv w).get? c' = some r' → RealChildA O c' r')
      (synth : sv w = some synthesizeChild)
      (quiet : O.quiet w)
      (hr : RunsTo (synthesizeCombinational c) mctx mref cctx cref w r w') : RealChildA O c r

/-- Every entry of the map is a `RealChildA`. -/
def CacheInvA (O : RefLawsAOps Fresh mref cref) (m : Std.HashMap Name Res) : Prop :=
  ∀ c r, m.get? c = some r → RealChildA O c r

/-- The vertical invariant WITH its cache half: quiet, synthesis ref, depth
`D`, and the cache VALUE of the world has real-child entries only. -/
def JQC (O : RefLawsAOps Fresh mref cref) (D : Nat) (w : Void IO.RealWorld) : Prop :=
  JQ O.quiet D w ∧ CacheInvA O (cv w)

/-- `JQC` with the thrown exception in the class. -/
def EQC (O : RefLawsAOps Fresh mref cref) (D : Nat) : Exception → Void IO.RealWorld → Prop :=
  fun e w => JQC O D w ∧ OkExc e

theorem cacheInvA_empty (O : RefLawsAOps Fresh mref cref) : CacheInvA O {} := by
  intro c r h
  first  -- guess: C3
    | simp at h
    | (rw [Std.HashMap.get?_empty] at h; cases h)

/-- The insert of a real child keeps the cache half. -/
theorem cacheInvA_insert {O : RefLawsAOps Fresh mref cref} {m : Std.HashMap Name Res} {c : Name}
    {r : Res} (h : CacheInvA O m) (hr : RealChildA O c r) : CacheInvA O (m.insert c r) := by
  intro c' r' h'
  rw [Std.HashMap.get?_insert] at h'
  split at h'
  · rename_i heq
    have : c = c' := by simpa using heq
    subst this
    cases h'
    exact hr
  · exact h c' r' h'

/-- `JQC` is stable: it implies quietness and survives every world change
leaving the three tracked values (the cache value included) and quietness. -/
theorem stableA_JQC (O : RefLawsAOps Fresh mref cref) (D : Nat) : StableA O.quiet (JQC O D) :=
  ⟨fun _ h => h.1.1, fun w w' hc hs hd hq h =>
    ⟨(stableA_JQ O.quiet D).2 w w' hc hs hd hq h.1, by rw [hc]; exact h.2⟩⟩

end Defs

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
  {Fresh : (σ : Type) → IO.Ref σ → Prop}

/-- **A run of the real entry from a `JQC` world, in an admissible context,
is a `RealChildA`.** -/
theorem RealChildA.of_jqc (O : RefLawsAOps Fresh mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {D : Nat} {c : Name} {r : Res} {w w' : Void IO.RealWorld} (hw : JQC O D w)
    (hr : RunsTo (synthesizeCombinational c) mctx mref cctx cref w r w') : RealChildA O c r :=
  RealChildA.run mctx cctx w w' hA hw.2 hw.1.2.1 hw.1.1 hr  -- guess: C2

/-! ## Steps -/

/-- A provenance-framed operation keeps `JQC` (exceptions in the class). -/
theorem keepsC_framed (O : RefLawsAOps Fresh mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (D : Nat) {α : Type} {p : MetaM α} (hp : FramedA Fresh p) :
    Keeps mctx mref cctx cref (JQC O D) p :=
  keepsA_framed O hA (stableA_JQC O D) hp

/-- A diagnostic operation keeps `JQC`. -/
theorem keepsC_diag (O : RefLawsAOps Fresh mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (D : Nat) {α : Type} {p : MetaM α} (hp : Diag p) :
    Keeps mctx mref cctx cref (JQC O D) p :=
  keepsA_diag O hA (stableA_JQC O D) hp

/-- **The cache read** from a `JQC` world returns the cache value of that
world and ends in `JQC` (`O.frame`/`O.frameQ` at `FramedA.cacheGet`). -/
theorem jqc_cacheGet (O : RefLawsAOps Fresh mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {D : Nat} {w : Void IO.RealWorld} {m : Std.HashMap Name Res} {w' : Void IO.RealWorld}
    (hw : JQC O D w)
    (h : RunsTo (sparkleChildCache.get : MetaM _) mctx mref cctx cref w m w') :
    m = cv w ∧ JQC O D w' := by
  have hk := O.frame hA _ FramedA.cacheGet w hw.1.1
  have hq := O.frameQ hA _ FramedA.cacheGet w hw.1.1
  rw [endW_of_runs h] at hk hq  -- guess: C4
  exact ⟨runsTo_get_readOf _ h, (stableA_JQC O D).2 w w' hk.1 hk.2.1 hk.2.2 (fun _ => hq) hw⟩

/-- The synthesis ref's read from a `JQC` world: `synthesizeChild`. -/
theorem jqc_synthGet (O : RefLawsAOps Fresh mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {D : Nat} {w : Void IO.RealWorld} {s : Option (Name → MetaM Res)} {w' : Void IO.RealWorld}
    (hw : JQC O D w)
    (h : RunsTo (sparkleChildSynth.get : MetaM _) mctx mref cctx cref w s w') :
    s = some synthesizeChild ∧ JQC O D w' := by
  have hk := O.frame hA _ FramedA.synthGet w hw.1.1
  have hq := O.frameQ hA _ FramedA.synthGet w hw.1.1
  rw [endW_of_runs h] at hk hq  -- guess: C4
  exact ⟨(runsTo_get_readOf _ h).trans hw.1.2.1,  -- guess: C5
    (stableA_JQC O D).2 w w' hk.1 hk.2.1 hk.2.2 (fun _ => hq) hw⟩

/-- The cache read as a triple: the value read has real-child entries. -/
theorem tripleC_cacheGet (O : RefLawsAOps Fresh mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (D : Nat) :
    Triple mctx mref cctx cref (JQC O D) (sparkleChildCache.get : MetaM _)
      (fun m w => JQC O D w ∧ CacheInvA O m) (EQC O D) := by
  intro w hw
  have hK := keeps_iff.mp (keepsC_framed O hA D FramedA.cacheGet) w hw
  cases hm : (sparkleChildCache.get : MetaM _) mctx mref cctx cref w with
  | ok a w1 =>
    obtain ⟨ha, hw1⟩ := jqc_cacheGet O hA hw hm
    exact ⟨hw1, by rw [ha]; exact hw.2⟩
  | error e w1 => rw [hm] at hK; exact hK

/-- **The depth-0 clear establishes the cache half** from `JQ` (it cannot
fail): `O.cacheSet` (the cache value becomes `{}`), `O.cacheSetQ`. -/
theorem tripleC_clear (O : RefLawsAOps Fresh mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (D : Nat) {R : Exception → Void IO.RealWorld → Prop} :
    Triple mctx mref cctx cref (JQ O.quiet D) (sparkleChildCache.set {} : MetaM Unit)
      (fun _ => JQC O D) R :=
  Triple.of_runs (refSet_runs _ _) fun w u w' hw h => by
    have hk := O.cacheSet hA _ _ _ _ h hw.1
    refine ⟨⟨O.cacheSetQ hA _ _ _ _ h hw.1, hk.2.1.trans hw.2.1, hk.2.2.trans hw.2.2⟩, ?_⟩
    rw [hk.1]; exact cacheInvA_empty O

/-- The clear from a `JQC` world (the cache half is re-established). -/
theorem tripleC_clear' (O : RefLawsAOps Fresh mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (D : Nat) {R : Exception → Void IO.RealWorld → Prop} :
    Triple mctx mref cctx cref (JQC O D) (sparkleChildCache.set {} : MetaM Unit)
      (fun _ => JQC O D) R :=
  Triple.conseq (tripleC_clear O hA D) (fun _ h => h.1) (fun _ _ h => h) (fun _ _ h => h)

/-- Setting the depth moves `JQC` to that depth (it cannot fail). -/
theorem tripleC_depthSet (O : RefLawsAOps Fresh mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (D v : Nat) {R : Exception → Void IO.RealWorld → Prop} :
    Triple mctx mref cctx cref (JQC O D) (ST.Ref.set sparkleSynthDepth v : MetaM Unit)
      (fun _ => JQC O v) R :=
  Triple.of_runs (refSet_runs _ _) fun w u w' hw h => by
    have hk := O.depthSet hA _ _ _ _ h hw.1.1
    refine ⟨⟨O.depthSetQ hA _ _ _ _ h hw.1.1, hk.2.1.trans hw.1.2.1, hk.2.2⟩, ?_⟩
    rw [hk.1]; exact hw.2

/-- Modifying the depth moves `JQC` to `f D` (it cannot fail). -/
theorem tripleC_depthModify (O : RefLawsAOps Fresh mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (D : Nat) (f : Nat → Nat) {R : Exception → Void IO.RealWorld → Prop} :
    Triple mctx mref cctx cref (JQC O D) (ST.Ref.modify sparkleSynthDepth f : MetaM Unit)
      (fun _ => JQC O (f D)) R :=
  Triple.of_runs (refModify_runs _ _) fun w u w' hw h => by
    have hk := O.depthModify' hA f hw.1.1 h
    have hq' : O.quiet w' := by
      obtain ⟨w1, hg, hs⟩ := modify_split sparkleSynthDepth f h
      have hq1 := O.frameQ hA _ FramedA.depthGet w hw.1.1
      rw [endW_of_runs hg] at hq1
      exact O.depthSetQ hA _ _ _ _ hs hq1
    refine ⟨⟨hq', hk.2.1.trans hw.1.2.1, ?_⟩, ?_⟩
    · rw [hk.2.2, hw.1.2.2]
    · rw [hk.1]; exact hw.2

/-- **The child insert keeps `JQC`** when the inserted entry is a
`RealChildA` (`RefLawsAOps.cacheModify'`: read then write; quietness from
`O.frameQ` of the read and `O.cacheSetQ` of the write). -/
theorem jqc_insert_runs (O : RefLawsAOps Fresh mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {D : Nat} {n : Name} {r : Res} {w : Void IO.RealWorld} {u : Unit} {w' : Void IO.RealWorld}
    (hw : JQC O D w) (hr : RealChildA O n r)
    (h : RunsTo (sparkleChildCache.modify (fun m : Std.HashMap Name Res => m.insert n r) :
      MetaM Unit) mctx mref cctx cref w u w') :
    JQC O D w' := by
  have hk := O.cacheModify' hA (fun m : Std.HashMap Name Res => m.insert n r) hw.1.1 h
  have hq' : O.quiet w' := by
    obtain ⟨w1, hg, hs⟩ := modify_split sparkleChildCache
      (fun m : Std.HashMap Name Res => m.insert n r) h
    have hq1 := O.frameQ hA _ FramedA.cacheGet w hw.1.1
    rw [endW_of_runs hg] at hq1
    exact O.cacheSetQ hA _ _ _ _ hs hq1
  refine ⟨⟨hq', hk.2.1.trans hw.1.2.1, hk.2.2.trans hw.1.2.2⟩, ?_⟩
  rw [hk.1]; exact cacheInvA_insert hw.2 hr

/-- The child insert as a triple (it cannot fail). -/
theorem tripleC_insert (O : RefLawsAOps Fresh mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (D : Nat) (n : Name) (r : Res) (hr : RealChildA O n r)
    {R : Exception → Void IO.RealWorld → Prop} :
    Triple mctx mref cctx cref (JQC O D)
      (sparkleChildCache.modify (fun m : Std.HashMap Name Res => m.insert n r) : MetaM Unit)
      (fun _ => JQC O D) R :=
  Triple.of_runs (refModify_runs _ _) fun _ _ _ hw h => jqc_insert_runs O hA hw hr h

/-! ## The memoised child entry -/

/-- **`synthesizeChild` under `JQC`, cache hit included.** Every returning
run of `synthesizeChild n` from a `JQC O D` world returns a `RealChildA O n`
result and ends in `JQC O D`. Hit: the returned value is the cache's entry
(the read returns `cv w`, `jqc_cacheGet`), a `RealChildA` by the cache half.
Miss: the nested run starts in a `JQC` world, so its result is a
`RealChildA` (`RealChildA.of_jqc`); it ends in `JQC` by the premise `hentry`
(NOT proved here: the nested core run's cache coherence); the insert keeps
`JQC` (`jqc_insert_runs`). -/
theorem synthesizeChild_realA (O : RefLawsAOps Fresh mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {D : Nat} {n : Name}
    (hentry : ∀ w1 r1 w2, JQC O D w1 →
      RunsTo (synthesizeCombinational n) mctx mref cctx cref w1 r1 w2 → JQC O D w2)
    {w w' : Void IO.RealWorld} {y : Res} (hw : JQC O D w)
    (h : RunsTo (synthesizeChild n) mctx mref cctx cref w y w') :
    RealChildA O n y ∧ JQC O D w' := by
  -- (writing-time guess C6: the steps of the built `synthesizeChild_inv`)
  unfold synthesizeChild at h
  obtain ⟨m, w1, hget, h⟩ := RunsTo.bind h
  obtain ⟨hm, hw1⟩ := jqc_cacheGet O hA hw hget
  cases hc : m.get? n with
  | some r =>
    simp only [hc] at h
    obtain ⟨rfl, rfl⟩ := RunsTo.pure_world h
    refine ⟨?_, hw1⟩
    rw [hm] at hc
    exact hw.2 n _ hc
  | none =>
    simp only [hc] at h
    obtain ⟨r, w2, hrun, h⟩ := RunsTo.bind h
    have hr : RealChildA O n r := RealChildA.of_jqc O hA hw1 hrun
    have hw2 := hentry w1 r w2 hw1 hrun
    obtain ⟨u, w3, hmod, h⟩ := RunsTo.bind h
    obtain ⟨rfl, rfl⟩ := RunsTo.pure_world h
    exact ⟨hr, jqc_insert_runs O hA hw2 hr hmod⟩

/-- A triple of a program gives its returning runs. -/
theorem runs_of_triple {α : Type} {P : Void IO.RealWorld → Prop} {m : MetaM α}
    {Q : α → Void IO.RealWorld → Prop} {R : Exception → Void IO.RealWorld → Prop}
    (hT : Triple mctx mref cctx cref P m Q R) {w : Void IO.RealWorld} {a : α}
    {w' : Void IO.RealWorld} (hw : P w) (h : RunsTo m mctx mref cctx cref w a w') : Q a w' := by
  have h1 := hT w hw
  unfold RunsTo at h
  rw [h] at h1
  exact h1

/-- A triple remembers, on return, a start world satisfying the
precondition and the run from it. -/
theorem triple_withRun {α : Type} {P : Void IO.RealWorld → Prop} {m : MetaM α}
    {Q : α → Void IO.RealWorld → Prop} {R : Exception → Void IO.RealWorld → Prop}
    (hT : Triple mctx mref cctx cref P m Q R) :
    Triple mctx mref cctx cref P m
      (fun a w' => Q a w' ∧ ∃ w0, P w0 ∧ RunsTo m mctx mref cctx cref w0 a w') R := by
  intro w hw
  have h1 := hT w hw
  cases hm : m mctx mref cctx cref w with
  | ok a w' => rw [hm] at h1; exact ⟨h1, w, hw, hm⟩
  | error e w' => rw [hm] at h1; exact h1

/-- **`synthesizeChild` as a triple under `JQC`, on every outcome**: a
returned value is a `RealChildA` (hit or miss), the end world is `JQC`,
exceptions in the class. Premise `hentryT`: the nested real entry keeps `JQC`
(NOT proved here). -/
theorem synthesizeChild_tripleC (O : RefLawsAOps Fresh mref cref)
    (hA : AdmCtx O.quiet mctx cctx) {D : Nat} {n : Name}
    (hentryT : Triple mctx mref cctx cref (JQC O D) (synthesizeCombinational n)
      (fun _ => JQC O D) (EQC O D)) :
    Triple mctx mref cctx cref (JQC O D) (synthesizeChild n)
      (fun r w => RealChildA O n r ∧ JQC O D w) (EQC O D) := by
  unfold synthesizeChild
  refine Triple.bind (tripleC_cacheGet O hA D) ?_
  intro m
  cases hc : m.get? n with  -- guess: C7
  | some r =>
    try dsimp only
    exact Triple.pure fun w hw => ⟨hw.2 n r hc, hw.1⟩
  | none =>
    try dsimp only
    refine Triple.conseq (P := JQC O D) ?_ (fun _ hw => hw.1) (fun _ _ h => h) (fun _ _ h => h)
    refine Triple.bind (triple_withRun hentryT) ?_
    intro r
    refine Triple.bind (Q := fun _ w => JQC O D w ∧ RealChildA O n r) ?_
      (fun _ => Triple.pure fun w hw => ⟨hw.2, hw.1⟩)
    refine Triple.of_runs (refModify_runs _ _) fun w u w' hw h => ?_
    obtain ⟨hw2, w1, hw1, hrun⟩ := hw
    have hr : RealChildA O n r := RealChildA.of_jqc O hA hw1 hrun
    exact ⟨jqc_insert_runs O hA hw2 hr h, hr⟩

/-! ## Endpoint: the one-output closing's children, cache hits included -/

/-- A `List.mapM` run whose steps keep `P` and establish `Q` of each result
(a copy of the law-free `mapM_loop_hoare`, ShippingChildRun.lean:234). -/
theorem mapM_loop_hoareA {α β : Type} (f : α → MetaM β) (P : Void IO.RealWorld → Prop)
    (Q : α → β → Prop)
    (hf : ∀ x w y w', P w → RunsTo (f x) mctx mref cctx cref w y w' → Q x y ∧ P w') :
    ∀ (l : List α) (acc r : List β) w w', P w →
      RunsTo (List.mapM.loop f l acc) mctx mref cctx cref w r w' →
      ∃ ys, r = acc.reverse ++ ys ∧ ys.length = l.length ∧
        (∀ k (hk : k < l.length), ∃ y, ys[k]? = some y ∧ Q l[k] y) ∧ P w'
  | [], acc, r, w, w', hp, h => by
    obtain ⟨rfl, rfl⟩ := RunsTo.pure_world h
    exact ⟨[], by simp, rfl, fun k hk => absurd hk (Nat.not_lt_zero k), hp⟩
  | x :: xs, acc, r, w, w', hp, h => by
    obtain ⟨y, w1, hy, h⟩ := RunsTo.bind h
    obtain ⟨hq, hp1⟩ := hf x w y w1 hp hy
    obtain ⟨ys, hr, hlen, hget, hp'⟩ := mapM_loop_hoareA f P Q hf xs (y :: acc) r w1 w' hp1 h
    refine ⟨y :: ys, by simp [hr], by simp [hlen], fun k hk => ?_, hp'⟩
    cases k with
    | zero => exact ⟨y, rfl, hq⟩
    | succ k =>
      obtain ⟨z, hz, hqz⟩ := hget k (by simpa using hk)
      exact ⟨z, by simpa using hz, by simpa using hqz⟩

/-- A copy of the law-free `mapM_hoare` (ShippingChildRun.lean:255). -/
theorem mapM_hoareA {α β : Type} (f : α → MetaM β) (P : Void IO.RealWorld → Prop)
    (Q : α → β → Prop)
    (hf : ∀ x w y w', P w → RunsTo (f x) mctx mref cctx cref w y w' → Q x y ∧ P w')
    (l : List α) (r : List β) {w w'} (hp : P w)
    (h : RunsTo (l.mapM f) mctx mref cctx cref w r w') :
    r.length = l.length ∧ (∀ k (hk : k < l.length), ∃ y, r[k]? = some y ∧ Q l[k] y) ∧ P w' := by
  obtain ⟨ys, hr, hlen, hget, hp'⟩ := mapM_loop_hoareA f P Q hf l [] r w w' hp h
  simp only [List.reverse_nil, List.nil_append] at hr
  subst hr
  exact ⟨hlen, hget, hp'⟩

/-- **The one-output closing's children under the admissible boundary,
cache hits included.** A returning run of `closeInstsM` from a `JQC O D`
world closes with children that are, call by call, `RealChildA`s of the
call's declaration — whether `synthesizeChild` returned a cached entry or ran
the entry — and ends in `JQC O D`. Premise `hentry`: the nested real entry
keeps `JQC` (NOT proved here). -/
theorem closeInstsM_realA (O : RefLawsAOps Fresh mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {D : Nat}
    (hentry : ∀ c w1 r1 w2, JQC O D w1 →
      RunsTo (synthesizeCombinational c) mctx mref cctx cref w1 r1 w2 → JQC O D w2)
    {shape : MachineShape} {t m₀ : Sparkle.IR.AST.Module} {d₀ : Sparkle.IR.AST.Design}
    {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design} {w w' : Void IO.RealWorld}
    (hw : JQC O D w)
    (hr : RunsTo (closeInstsM shape t m₀ d₀) mctx mref cctx cref w (some (m, d)) w') :
    ∃ children, Sparkle.IR.Machine.closeInsts (machNIn shape) shape.insts.length
        shape.layout.slots.length (t.inputs.map (·.name)) (shape.insts.map (·.2.1))
        children (m₀, d₀) = some (m, d) ∧
      children.length = shape.insts.length ∧
      (∀ k (hk : k < shape.insts.length), ∃ y, children[k]? = some y ∧
        RealChildA O (shape.insts[k]).1 y) ∧
      JQC O D w' := by
  -- (writing-time guess C8: the steps of the built `closeInstsM_inv`)
  unfold closeInstsM at hr
  obtain ⟨synth?, w1, hget, hr⟩ := RunsTo.bind hr
  obtain ⟨rfl, hw1⟩ := jqc_synthGet O hA hw hget
  dsimp only at hr
  obtain ⟨children, w2, hch, hr⟩ := RunsTo.bind hr
  obtain ⟨heq, rfl⟩ := RunsTo.pure_world hr
  obtain ⟨hlen, hk, hw2⟩ := mapM_hoareA _ (JQC O D)
    (fun (x : Name × List Nat × MixedGateBinder) y => RealChildA O x.1 y)
    (fun x w y w' hp hy => synthesizeChild_realA O hA (hentry x.1) hp hy)
    shape.insts children hw1 hch
  exact ⟨children, heq.symm, hlen, hk, hw2⟩

end Tools.ShippingChildCacheA
