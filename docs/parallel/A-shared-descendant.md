# A: callees that share a descendant (`mixDeep`) — round par/a-17

Base: `poc/roundtrip-proof` de7d6d4d. Branch `par/a-17`. Everything below
that is not marked BUILT or MEASURED is READ or WRITTEN, NOT BUILT.

## 0. Result in one paragraph

`MachineClosesAt mixDeep` is NOT derived, and no endpoint loses a premise in
this round. The disjointness hypothesis `hdisjD` of `machineClosesAt_of_kidsD`
cannot be replaced by a hypothesis that is decidable from the reader data:
what the closing needs for two different callees is that the MODULES they
both hold under one name are EQUAL, and the only source of such an equality
is the child cache — but `MachineClosesAt` quantifies over every world
satisfying `InvW`, and `InvW` says nothing that relates one cache entry's
design to another entry's module. The round delivers (a) this analysis,
(b) the closing proved RELATIVE to a statement about the cache the run ends
in (`MachineClosesAtS`, weaker than `MachineClosesAt`, three new Tools
files), from which the old theorem's statement follows, (c) the exact
missing statements (§5).

## 1. Where `hdisjD` is used, and for what

`Tools/ShippingCallsKidsD.lean`, theorem `machineClosesAt_of_kidsD` (98–317).

* 131–133: the hypothesis, two conjuncts.
* It is used ONCE, 232–233 (`obtain ⟨hd1, hd2⟩ := hdisjD i hki j hkj hdecl`,
  and the symmetric `⟨hd3, hd4⟩`), inside `hconsV` (209–252): "two VISITED
  modules of one name are equal", in the branch where the two modules were
  reached through entries of DIFFERENT declarations (231). All four uses are
  refutations (`exfalso`, 231):
  * 248: both are the callees' own modules, same printed name → `hsep` gives
    the same declaration, contradiction (`hdisjD` not used).
  * 249 (`hd1`, first conjunct): `a` is callee `i`'s module, `b` a module of
    callee `j`'s design.
  * 251 (`hd3`, first conjunct, symmetric).
  * 252 (`hd2`, second conjunct): `a`, `b` are modules of the two designs.
  * `hd4` is never used.
* `hconsV` has ONE consumer, 302: `design_checks hd0 hconsV …`
  (`Tools/ShippingDesignWithG.lean` 83–110), which passes it to
  `designWith_resolvesG` (37–52): every visited module is found BY ITS NAME
  in the joined design AS ITSELF. That is the antecedent `hdesign` of
  `closeInstsG_of_run` (`Tools/ShippingCallsRunG.lean` 127–134).

So the object keyed by the printed name is none of the caches and none of
the laws (`sparkleSubModuleCache`, `ChildBnd`, `RefLaws` do not occur): it is
the PURE join of the children's designs, `designWith children d` read by
`moduleByName`, inside the pure closing `closeInstsG`
(`Sparkle/IR/MachineInstG.lean` 115–145):

    119   let d' := designWith children d
    140   children.all (fun c => decide (moduleByName d'.modules c.1.name = some c.1) &&
    141     c.2.modules.all (fun m => decide (moduleByName d'.modules m.name = some m))) &&

If two visited modules have one name and are not equal, one of them is not
found as itself, the conjunction is false, `closeInstsG` returns `none` and
the machine route falls back. `hdisjD` excludes the situation by names;
nothing else in the proof depends on it.

## 2. What the compiler does when one declaration is reached twice

`Sparkle/Compiler/Elab.lean` 8845–8849 (READ):

    def synthesizeChild (n : Name) := do
      if let some r := (← sparkleChildCache.get).get? n then return r
      let r ← synthesizeCombinational n
      sparkleChildCache.modify (·.insert n r)
      return r

The cache is cleared only by an entry that starts at synthesis depth 0
(5466–5471) and has no other writer (6249–6255). So in an OUTERMOST compile
of `mixDeep` (the three entries are synthesised in order `mid2`, `midH`,
`cnt` — order READ off the source, see §4): `mid2` misses; inside its run
`midH` misses, is compiled and inserted; the parent's own `midH` entry then
HITS and returns that same pair. The `midH` module inside `mid2`'s design
and the parent's `midH` child are one value, and `rcH` likewise. The task's
expectation is right about the real outermost run.

What is PROVED about this (BUILT):

* `synthesizeChild_post` (`Tools/ShippingCallsSame.lean` 34–63): a run leaves
  its result in the cache under the name, and returns the cached value on a
  hit.
* `synthesizeChild_pin` (126–133): at positive depth a run keeps every entry
  the cache has.
* `mapM_loop_all` (148–199) / `closeInstsGM_run_all`
  (`Tools/ShippingCallsRunG.lean` 56–94): two entries of ONE declaration get
  the same child.

Nothing is proved about two entries of DIFFERENT declarations, and the next
section says why nothing can be, from what exists.

## 3. Why no hypothesis decidable from the reader data can replace `hdisjD`

* `MachineClosesAt` (`Tools/ShippingChildRun.lean` 444–450) is
  `∀ b w r w', InvW mref cref w → DepthPos mref cref w → RunsTo … w r w' → r ≠ none`:
  every world with the invariant and a positive depth.
* `InvW` (`Tools/ShippingChildInv.lean` 477–478) is
  `CacheAt ∧ SynthAt ∧ QuietAt`; `CacheAt`/`CacheInv` (462–468) say only that
  EACH entry is a `RealChild` of its key.
* `RealChild c r` (451–459): `r` is returned by SOME run of
  `synthesizeCombinational c`, in some contexts, from some world whose cache
  entries are `RealChild`s. Two `RealChild`s of one declaration are not known
  to be equal (stated in `Tools/ShippingCallsSame.lean` 5–7): the entry is a
  `MetaM` action and no theorem says its module is a function of the
  declaration.
* A child's interface (`ChildIfaceD`, `Tools/ShippingCallsKidsD.lean` 37–51)
  is derived from ITS `RealChild` witness alone (`kidsChild_of_real`,
  `Tools/ShippingKidsChildIface.lean` 357–393): names, ports, the design's
  names. It contains no equation between a module of its design and anything
  outside it.

The scenario that the hypotheses admit and no existing theorem excludes: a
world `w` with `InvW w`, positive depth, whose cache holds
`mid2 ↦ y_a` and `midH ↦ y_b`, where `y_a` is a `RealChild` of `mid2` whose
run compiled `midH` to a module `g` (so `g ∈ y_a.2.modules`,
`g.name = midH.toString`) and `y_b` is a `RealChild` of `midH` from another
run with `y_b.1 ≠ g`. In `w` the closing's three entries are all HITS,
`children = [y_a, y_b, …]`, the visited modules hold `g` and `y_b.1` under
one name, line 140–141 fails and the result is `none`. I do NOT claim such a
world exists (that would need two runs of `midH`'s entry with different
modules, which is neither proved nor refuted here). The claim is: every
proof of `MachineClosesAt mixDeep` has to exclude it, and it can only be
excluded by (i) an equation between modules of different cache entries —
which `InvW` does not carry — or (ii) module determinism of `midH` and `rcH`
(`RealChild midH y → RealChild midH y' → y.1 = y'.1`), which does not exist.

A condition on names/tables (injectivity of `Name.toString` on the
declarations involved, consistency of the per-callee tables) does not help:
it can show that the two modules are of the SAME DECLARATION; it cannot show
they are the same MODULE. The hypothesis proposed in the task text ("a
printed name met under two callees denotes the same declaration, and its
cached result is the one both use") has a decidable first half and a second
half that is exactly the missing run-level statement.

Also checked: the proof parameter `RefLaws.aux` (`Tools/ShippingChildInv.lean`
336–344), which carries the pin through a child's synthesis, cannot carry a
relation between entries: its closure condition `auxInsert` is asked for
EVERY inserted value `r`
(`aux m0 → m0.get? n = none → aux m1 → aux (m1.insert n r)`), and an
agreement between `r`'s design and other entries is false for an arbitrary
`r`.

## 4. `mixDeep`'s tables, and the hypotheses evaluated on them

Sources: `Tests/Compiler/ShippingChildBoundaryTest.lean` 278–286,
`ShippingDesignSVTest.lean` 26–32, `ShippingMachineDepthHTest.lean` 20–32,
`ShippingMachineSeqTest.lean` 20–25 (READ).

MEASURED (`docs/parallel/verification-a16.md` 110–111, lines truncated in the
log): `mixDeep` has `nDecl = 1`, its first call entry is `mid2`; `midH` is a
call entry of `mixDeep` AND of `mid2`; the distinct callees are exactly
`mid2`, `midH`, `cnt` (asserted by the BUILT `NoPortsMixDeepTest` 129–131).

READ, NOT MEASURED (the full lists are not in any log; the new test logs
them first — `SHARED MIXDEEP DATA` — and the generator logs the pair table):

| | entries (one per projected field) | descendants' declarations (`declsOf`) |
|---|---|---|
| `mixDeep` | `[mid2, midH, cnt]` (fields `a.hit`, `b.n`, `c.n`) | — |
| `mid2` | `midH` once per projected field of `k` (`k.hit`, `k.n`) | `midH`, `rcH` |
| `midH` | `rcH` (one-output gate call) | `rcH` |
| `cnt` | none | none |

`namesK k` = the printed names of the descendants of entry `k`'s callee.

**`hdisjD` on `mixDeep` — FALSE** (given the measured fact that `midH` is an
entry of `mid2`): take `k` = the entry of `midH`, `k'` = the entry of `mid2`.
They are different declarations, and the first conjunct asks
`midH.toString ∉ namesK k'`; but `namesK k'` is the list of printed names of
`mid2`'s descendants and `midH` is one of them, so `midH.toString` IS a
member (`List.mem_map_of_mem`). The second conjunct fails as well with
`x = rcH.toString` (in `namesK` of both). For the pairs with `cnt`
(`namesK = []`) both conjuncts hold.

**The hypotheses the new theorem keeps, on `mixDeep`** (by reading; each is
decided by the kernel in the generated theorem, so a wrong reading is a
build error, not a false premise):

| hypothesis | instance | value |
|---|---|---|
| `hsep` | `mid2`, `midH`, `cnt` print pairwise differently | true (three different last components) |
| `hparent` | none prints as `mixDeep` | true |
| `hparentD` | `mixDeep.toString ∉ {midH, rcH}`, `∉ {rcH}`, `∉ {}` | true |
| `hselfD` | `mid2.toString ∉ {midH, rcH}`; `midH.toString ∉ {rcH}`; `cnt`: `∉ {}` | true |
| `hfieldsNd` | the three entries are of three declarations | true (vacuous) |
| `hfresh` | the output of `mixDeep` does not start with `i` | NOT READ (decided or the command throws) |

**The antecedent of the new conclusion on `mixDeep`** (`Agree [mid2, midH,
cnt] m` for the cache `m` the closing ends in), spelled out:

* `(mid2, midH)`: names in common are `midH.toString` (a module of
  `mid2`'s design / `midH`'s own module) and `rcH.toString` (a module of
  both designs). Asked: the two `midH` modules are equal, the two `rcH`
  modules are equal. TRUE on an outermost run (§2); NOT PROVED.
* `(mid2, cnt)`, `(midH, cnt)`: no name in common (given the interfaces), so
  nothing is asked. (The theorem still states the pair; a refinement that
  discharges such pairs from a per-pair disjointness is §6.)

## 5. New statements (WRITTEN, NOT BUILT)

`Tools/ShippingCallsRunFinal.lean`:

    theorem mapM_loop_final {α : Type} (f : α → MetaM Res) (key : α → Name) (L : RefLaws mref cref)
        (hf : ∀ x w y w', InvV L w → L.dval w ≠ 0 → RunsTo (f x) mctx mref cctx cref w y w' →
          InvV L w' ∧ L.dval w' = L.dval w ∧ (L.val w').get? (key x) = some y ∧
            (∀ c0 y0, (L.val w).get? c0 = some y0 → (L.val w').get? c0 = some y0)) :
        ∀ (l : List α) (acc r : List Res) w w', InvV L w → L.dval w ≠ 0 →
          RunsTo (List.mapM.loop f l acc) mctx mref cctx cref w r w' →
          ∃ ys, r = acc.reverse ++ ys ∧ ys.length = l.length ∧
            (∀ k (hk : k < l.length), ∃ y, ys[k]? = some y ∧ (L.val w').get? (key l[k]) = some y) ∧
            (∀ c0 y0, (L.val w).get? c0 = some y0 → (L.val w').get? c0 = some y0)

    theorem closeInstsGM_run_allF …   -- closeInstsGM_run_all, plus the clause
          (∀ k (hk : k < shape.insts.length), ∃ y, children[k]? = some y ∧
            (L.val w').get? (shape.insts[k]).1 = some y)

`Tools/ShippingCallsKidsS.lean`:

    def Agree (decls : List Name) (m : Std.HashMap Name Res) : Prop :=
      ∀ c ∈ decls, ∀ c' ∈ decls, c ≠ c' → ∀ (y y' : Res), m.get? c = some y → m.get? c' = some y' →
        ∀ a ∈ y.1 :: y.2.modules, ∀ b ∈ y'.1 :: y'.2.modules, a.name = b.name → a = b

    def CacheAgrees (decls : List Name) (w : Void IO.RealWorld) : Prop :=
      ∀ (mctx : Meta.Context) (cctx : Core.Context) m w1,
        RunsTo (sparkleChildCache.get : MetaM _) mctx mref cctx cref w m w1 → Agree decls m

    def MachineClosesAtS (declName : Name) (shape : MachineShape) (decls : List Name) : Prop :=
      ∀ (b : Bool) w r w', InvW mref cref w → DepthPos mref cref w →
        RunsTo (synthesizeMachineCertified
          (fun e hint top named => translateExprToWire e hint top named) (profLogIO b) declName shape)
          mctx mref cctx cref w r w' → CacheAgrees mref cref decls w' → r ≠ none

    theorem closes_of_agree … (the hypotheses of machineClosesAt_of_kidsD up to hselfD, no hdisjD) :
        ∀ (b : Bool) w r w', InvW mref cref w → DepthPos mref cref w → RunsTo (…) … w r w' →
          (InvW mref cref w' → CacheAgrees mref cref (d.shape.insts.map (·.1)) w') → r ≠ none

    theorem machineClosesAtS_of_kids … (the same hypotheses) :
        MachineClosesAtS mctx mref cctx cref declName d.shape (d.shape.insts.map (·.1))

    theorem machineClosesAt_of_kidsD_again … (the same hypotheses) (hdisjD : … as in the old theorem) :
        MachineClosesAt mctx mref cctx cref declName d.shape

    theorem MachineClosesAtS.of_closes (decls) : MachineClosesAt … → MachineClosesAtS … decls

`closes_of_agree` is the old proof with ONE change: the different-declaration
branch of `hconsV` is closed by `hcross` (the two children are the end
cache's values under their declarations — `closeInstsGM_run_allF` — and the
end cache agrees) instead of the four name refutations. `hsep`, `hselfD`,
`hparentD` are used exactly where the old proof uses them.

The old theorem FOLLOWS from the core: `machineClosesAt_of_kidsD_again` has
the old statement and derives `CacheAgrees` of the end world from `hdisjD`
(the cache's entries are `RealChild`s by the end world's invariant, `hkid`
gives their names, and the four refutations of the old proof show that two
different callees have no name in common). The old file is not edited and
the generators keep using the old theorem.

`Tools/ShippingCallsKidsSGen.lean`: `#machine_closes_shared f` generates
`f.closes_shared : reflections → MachineClosesAtS … f f.machineData.shape
(f.machineData.shape.insts.map (·.1))`, reading each callee by the BUILT
`Tools.ShippingChildIfaceGen.ifaceDeep`; it throws instead of leaving a name
premise, and logs the pair table of §4.

`Tests/Compiler/CallsKidsSharedMixDeepTest.lean`: logs the reader data, runs
the command on `mixDeep`, audits (standard axioms; every premise a
reflection; the conclusion is `MachineClosesAtS`; the open endpoint still
asks `MachineClosesAt`; no `_closed` constant). The BUILT
`NoPortsMixDeepTest` audit throws if `mixDeep.machine_design_noPortsNR2_closed`
exists in its own environment; this file is downstream and does not create
that constant either. `Tests/Compiler/NoPortsMixDeepClosedTest.lean` (task
step 4) is NOT written: there is nothing to close with.

## 6. What is missing, exactly

**M1 (the statement that would close `mixDeep` with the new theorem).** For
a run of `mixDeep`'s machine synthesis from a world with `InvW` and positive
depth, ending in `w'`:

    CacheAgrees mref cref [mid2, midH, cnt] w'

NOT derivable from `InvW w` (§3). It splits into

* M1a — per callee with calls, from ITS run (true on a miss, by the argument
  of §2; not proved): for `y` returned by a run of `synthesizeChild mid2`
  from `w0` to `w1` in which `mid2` was NOT cached at `w0`,
  `∃ y', (L.val w1).get? midH = some y' ∧ ∀ g ∈ y.2.modules, g ∈ y'.1 :: y'.2.modules`.
  Needs: the decomposition of `mid2`'s entry run that `kidsChild_iface`
  (`Tools/ShippingKidsChildIface.lean` 129–355) already does, with the inner
  closing's `closeInstsGM_run_allF` (new) for the cache clause, and the pin
  of the `midH` entry from the inner closing's end to the entry's end (the
  suffix of `synthesizeFromConst`'s machine arm, the `finally`, the post
  passes — frames; no existing theorem states the pin for a SUFFIX of an
  entry run, `synthesizeChild_pin` is for whole runs).
* M1b — the hit case: when `mid2` IS cached at the closing's start, the
  same relation between the cached `mid2` value and the cache's `midH`
  entry. This is a property of the START world and is not implied by
  `InvW`. It needs one of:
  1. a stronger invariant: `CacheInv` extended by a coherence clause of the
     kind `Agree`, kept by `synthesizeChild` because every inserted value
     satisfies M1a against the cache it is inserted into. Not expressible
     through `RefLaws.aux` (`auxInsert` is for every `r`); it means a second
     pass over `child_keeps` / `core_keeps` / `entry_keeps`
     (`Tools/ShippingChildKeeps.lean` 282, 364, 451) and the relative laws,
     and a change of the boundary: `StartV`'s nested alternative
     (`dval ≠ 0 ∧ CacheInv`, `Tools/ShippingChildInv.lean` 507–508) would have
     to carry the clause, i.e. `ChildBnd` changes. A general coherence
     clause is moreover false without name separation of ALL cached
     declarations (two declarations printing alike), so the clause has to
     be relative to a declared finite set.
  2. module determinism of the shared descendants
     (`RealChild midH y → RealChild midH y' → y = y'`, same for `rcH`): then
     `hcross` follows from `RealChild` and names alone, with no cache
     statement and no boundary change. Not available.
  3. a restriction of the worlds: a closing predicate asked only where the
     callees with calls are not yet cached. Then every consumer of
     `MachineClosesAt` on the path to the endpoint needs a variant
     (`Tools.ShippingKidFacts.kids_runFacts`, `kids_outsCheck`,
     `kids_maskedN`, `kids_designCheck` take `closes : MachineClosesAt …`),
     and the freshness has to be established at the closing's start, which
     again needs a start at depth 0 (a boundary stronger than `ChildBnd`)
     and a statement that the harness inserts none of them.

Each of the three is a design decision (invariant/boundary change, or a new
kind of theorem about the translator) and not a lemma of this round. I did
not assume any of them under a new name: `MachineClosesAtS` is stated as a
weaker predicate and nothing consumes it.

**M2 (consumers).** Even with M1, `MachineClosesAtS` is not `MachineClosesAt`:
the four `kids_*` theorems and `generateX` take the latter. With route 1 or
2 above `MachineClosesAt` itself becomes provable (the antecedent is
discharged inside, as `machineClosesAt_of_kidsD_again` does for the disjoint
case) and no consumer changes.

**Refinement not done.** `Agree` is asked for every pair of different
callees. Pairs with disjoint descendants could be discharged by a per-pair
`hdisjD` (the argument of `machineClosesAt_of_kidsD_again`), leaving
`CacheAgrees` only over the pairs that share. Not written: it changes
nothing about M1.

## 7. Endpoint — premise — predicted state

| endpoint | premise | state |
|---|---|---|
| `mixDeep.machine_design_noPortsNR2` (OPEN, BUILT) | `MachineClosesAt mixDeep` | STAYS — not removed |
| | the unreduced boundary | STAYS |
| `mixDeep.machine_design_noPortsNR2_closed` | — | does not exist; not created |
| `mixDeep.closes_shared` (new, not an endpoint) | `hdisjD` | not a hypothesis (WRITTEN, NOT BUILT) |
| | — | conclusion carries `CacheAgrees … w'`, NOT derived |
| every other endpoint | — | unchanged |

## 8. Build queue (integrator)

`lakefile.lean`:

    lean_lib «Tools.ShippingCallsRunFinal» where
      roots := #[`Tools.ShippingCallsRunFinal]

    lean_lib «Tools.ShippingCallsKidsS» where
      roots := #[`Tools.ShippingCallsKidsS]

    lean_lib «Tools.ShippingCallsKidsSGen» where
      roots := #[`Tools.ShippingCallsKidsSGen]

`Tests/AllTests.lean` (optional — it proves no endpoint; it owns
`mixDeep.closes_shared` only):

    import Tests.Compiler.CallsKidsSharedMixDeepTest

Order: (1) `Tools.ShippingCallsRunFinal`; (2) `Tools.ShippingCallsKidsS`;
(3) `Tools.ShippingCallsKidsSGen`; (4)
`Tests.Compiler.CallsKidsSharedMixDeepTest`. (1)–(2) are independent of the
generator and the test and are worth building alone.

## 9. UNVERIFIED, in risk order

1. `Tools/ShippingCallsKidsSGen.lean` — nothing elaborated: the selective
   `open Tools.ShippingChildIfaceGen (… ifaceDeep)` of a `partial def` of a
   `mutual` block; `ifaceDeep` called outside `closesDeep` (it re-enters
   `closesDeep k` for callees with calls: BUILT constants are kept, by its
   `unless contains` guards — READ); the spliced `$hpD $hsD` (copied from
   the BUILT `namesSep` branch); the kernel `decide`s of `hparentD` /
   `hselfD` over `declsOf mid2.machineData …` (the same terms are BUILT for
   `topD2`, not for three callees); the string interpolations.
2. `CallsKidsSharedMixDeepTest`: the first `run_cmd`'s assertion that `rcH`
   is among `midH`'s call entries (READ, not measured); the audit's
   `forallTelescope` returning the body.
3. `machineClosesAt_of_kidsD_again`: the long `intro` through `CacheAgrees`
   and `Agree` (definitions unfolded by `intro`); `List.getElem_of_mem` on
   `insts.map (·.1)` and the two `simp`s that read the index back;
   `hinv.1 …` as `CacheAt`.
4. `closes_of_agree`: `hAg` (`refGet_runs` with named contexts, then
   `rw [hmE] at hA` under the definition `Agree`); `hcross`'s application of
   `hAg` (a definition applied as a function); the rest is the text of the
   BUILT proof.
5. `closeInstsGM_run_allF`: the two `subst`s after the two `mapM` lemmas on
   the same run (`children = ys`, then `children = zs`); the clause
   `(L.val w').get? (shape.insts[k]).1` against the lemma's
   `key shape.insts[k]` (definitional).
6. `mapM_loop_final`: the text of the BUILT `mapM_loop_all` with fewer
   clauses.

## Build record (integrator, 2026-10-13)

Built on poc 4a0d8356 + this round's files (worker files unchanged): `Tools.ShippingCallsRunFinal`,
`Tools.ShippingCallsKidsS`, `Tools.ShippingCallsKidsSGen`, `Tests.Compiler.CallsKidsSharedMixDeepTest`
(target-only, not in AllTests). NO endpoint loses a premise: `mixDeep.closes_shared` concludes
`MachineClosesAtS` — the closing RELATIVE to `CacheAgrees` of the run's end world, which is not derived —
and nothing consumes it; `mixDeep.machine_design_noPortsNR2` still asks `MachineClosesAt mixDeep`.
The route to derive `CacheAgrees` (§6: cache-coherence clause in the invariant / module determinism /
fresh-world closing) is an open decision put to the user; not started.

```
20261013-060405-a17-tests: lake build Tools.ShippingCallsRunFinal Tools.ShippingCallsKidsS Tools.ShippingCallsKidsSGen Tests.Compiler.CallsKidsSharedMixDeepTest 
result=success
exit=0
memory_peak_file=828772352
Build completed successfully (581 jobs).
20261013-060508-a17-alltests: lake build Tests.AllTests Tests.Compiler.CallsKidsSharedMixDeepTest 
result=success
exit=0
memory_peak_file=130756608
Build completed successfully (1209 jobs).
Test.lean:91:0: CLOSES SHARED Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.closes_shared: MachineClosesAtS (the closing RELATIVE to CacheAgrees of the run's end world over the callees — NOT MachineClosesAt); 4 premises, all reflections: [hR_Sparkle_Tests_Compiler_ShippingDesignSVTest_mid2,
Test.lean:96:0: SHARED MIXDEEP AUDIT Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep: Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.closes_shared on standard axioms, 4 premises, all reflections; its conclusion is MachineClosesAtS over the callees — MachineClosesAt with the antecedent CacheAgrees of the run's end world, which is NOT derived. Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machine_design_noPortsNR2 still asks MachineClosesAt of Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep; Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machine_design_noPortsNR2_closed does not exist. NO endpoint loses a premise. Not derived and not assumed: that the end world of a real run of Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep's machine synthesis satisfies CacheAgrees (docs/parallel/A-shared-
```
