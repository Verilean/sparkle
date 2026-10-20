# Cache coherence (rounds par/a-33 … a-42): summary for the reviewer

No new claim is made here. BUILT = built and integrated on poc by the
integrator (HEAD `2858bca5`); "written" = par/a-42, not built.

## The problem

A parent machine with a SHARED descendant (`mixDeep → {mid2 → midH → rcH,
midH → rcH, cnt}`) closes only if the modules of the same name it finds in
the child cache (`sparkleChildCache`, keyed by declaration name) are equal.
Its endpoint `mixDeep.machine_design_noPortsNR2` therefore carries the
premise `MachineClosesAt mixDeep`: the machine synthesis returns a module at
EVERY invariant world of positive depth. The invariant of the laws
(`CacheInv`: each entry is the result of SOME real compile of its key) does
not give that equality. Reviewer ruling kept throughout: injective names are
not coherence; a stronger premise is not progress.

## The invariant, and the chain

`Prov m` (`Tools/ShippingCacheCoherentRun.lean`): every entry of the cache is
named after its key, and every module of its design is a memory module or
the module of another entry. `Prov` implies coherence (`coherent_of_prov`),
which is what the relative closing asks.

| step | statement | theorem (file under `Tools/`) |
|---|---|---|
| initial | an outermost entry clears the cache; the empty cache satisfies `Prov` | `core_reads_val0`, `coreVia0_of` (`ShippingCacheCoherentOuter`) |
| preserved, memoised entry | a hit leaves the cache; a miss inserts a fresh result | `prov_insert`, `full_split` (`…Run`), `synthesizeChild_ok` (`…Cert`) |
| preserved, one declaration | `EntryOk L c K`: a returning run of `c`'s entry from a `Prov` world without `c` ends in a `Prov` world, the added keys in `K` | `entryOk_leaf`, `machine_all`, `entryOk_machine` (`…Cert`) |
| … its ingredients | the core run IS the machine synthesis, with its worlds | `core_reads_val`, `sfc_machine_val`, `coreVia_of` (`…Via`) |
| | the certified walk leaves the cache (10 constructors; then all 21) | `walk_still` (`ShippingWalkStill`), `walk_still_all` (`ShippingWalkStillMore`) |
| | the harness shell and the leaf / gate entries leave the cache | `harnessStill_frag`, `entryStill_leaf`, `entryStill_gate` (`ShippingHarnessStill`); `harnessStill_all`, `entryStill_gate_all` (`ShippingWalkStillMore`) |
| | the harness's result facts from the declaration's data | `hout_of_data` (`…Data`) |
| consumed | from a `Prov` world the relative closing fires | `machine_closes_of_prov` (`…Close`), `machine_closes_of_entryOk` (`…Cert`) over `MachineClosesAtS` (`ShippingCallsKidsS`) |

For the family (target-only tests, BUILT): `midH_entryOk_closed`,
`cnt_entryStill`, `rcH_entryStill` (`Tests/Compiler/CacheChainClosedTest`);
`cnt_entryOk`, `mid2_entryOk`, `mixDeep_closes_prov`, and
**`mixDeep_closes_outermost`** (`Tests/Compiler/MixDeepOutermostTest`): for a
core run of `mixDeep` that STARTS at depth 0 the machine synthesis returns a
module — premises the reflections of the five declarations only. A
separately scoped theorem; the endpoint and its premise are unchanged.

Generators (BUILT, par/a-41): `#entry_ok f` adds `f.entry_ok` for a gate
leaf, a machine leaf, a parent whose callees have it — statement check
(premises reflections only) and axiom audit
(`ShippingEntryOkCommand`). The four of the family reproduce the hand-written
statements (`isDefEq`).

Reduction (BUILT, par/a-39): `machineClosesAt_of_det`
(`ShippingDetReduce`) — `MachineClosesAt` at all worlds from the relative
closing, `DetN` (two real compiles of one declaration return the same
module) on the descendants, and a provenance fact about the callees'
designs. `DetN` is a hypothesis there, not a theorem.

## Measured

| what | result |
|---|---|
| own-key / cycle probes (`CacheOwnKeyProbe`) | a run inserting its own key would need a cycle; in every row, cyclic sources included, the run's own key is absent at its end (`ownKey=F`) |
| `SingleOutStaleProbe` (a CONSTRUCTED state: pre-set depth 1, legacy route) | the same declaration, two modules: instances 1 vs 0 — **Finding I**: `DetN` is false in general |
| `NoRepeatFamilyTest` | `noRepeat` true for `rcH`, `cnt`, `midH`, `mixDeep`, FALSE for `mid2` (the literals of two packed Bool fields) |
| `FragCensusTest` | 129 declarations with a reflected term (126 machine: 88 without a call, 38 with; 3 gate); first fragment `wfrag` T 92, F 37; all 129 inside the walk now |
| `EntryOkFamilyTest` | `rcH`, `cnt`, `midH`, `mid2` generated (1, 1, 2, 3 premises), statements equal to the hand-written ones; `mixDeep` not generated (no closing at all worlds) |
| `fix/singleout-nested` in isolation | builds; AllTests 1325 green there; five sims; `SINGLEOUTFIX` equal=T; no stale hit on real commands; a 28-file text sample identical to poc |

Written, not built (par/a-42): `#entry_ok_all` — the sweep of `EntryOk`
over all 129, leaves first (`ShippingEntryOkWide`); machine leaves without a
closing constant and parents whose closing has another name are no longer
refused; memory parents are attempted, outcome unknown.

## Open

1. **`MachineClosesAt mixDeep` at NESTED starts** (an arbitrary invariant
   world of positive depth). `Prov` is established by the depth-0 clear; a
   nested start has no such anchor. The all-worlds form needs determinism of
   the descendants' compiles (`DetN`), which for the certified route is
   neither proved nor refuted: the one uncontrolled dependency is what a
   read of the run-local translation cache returns — no law speaks of it.
2. **Finding I** (legacy route): an unvalidated hit of the single-output
   instance cache, not reset at a nested entry. Not reachable by a real
   compile, by reading (eight ways examined) and by the two real-command
   rows of the regression test. Fix proposed and verified in isolation.
3. **Memory call entries**: `entryOk_machine` admits them; no `EntryOk` of a
   memory parent is built.
4. **The legacy route** and declarations without generated data: outside
   the unit (`EntryOk` is proved through the certified walk only).
5. `EntryOk mixDeep` (it goes through `CoreVia`, hence item 1).

## What each open ruling would buy

| ruling | buys | costs |
|---|---|---|
| **Option 3**: a NEW endpoint for `mixDeep` at outermost starts, on `mixDeep_closes_outermost` | `mixDeep` closed for every run a command can start, from reflections only; no boundary change. The same technique reaches `mixDeep` as a child of a larger top (anchored at the top's depth-0 start) | siblings of the consumers that take `closes : MachineClosesAt …` (they use it at the run in hand); must be reported as a depth-0 endpoint, not as the existing one losing a premise; item 1 stays open |
| **Option 1**: a value law for run-local translation caches (an extension of `RefLaws`, like `RefLawsM`) | then `DetN` for the certified route is provable, and with it item 1 in full | a larger trusted boundary (`ChildBnd` must carry it) AND a relational two-run walk of about the size of the two walk files; covers starts no real compile has |
| Option 2 (side condition `noRepeat`) | nothing: ruled out by the measurement (`mid2`) | — |
| **Finding I fix** (`fix/singleout-nested`): reset / restore the single-output map at a nested entry | removes the one measured counterexample to determinism on the legacy route; no output change expected or observed on the sample | a compiler change (three ref operations) with three proof follow-ups, already built in isolation |
| `par/a-35-aux` (run-aware `auxInsert`; changes `RefLaws` and its audit; NOT built) | was meant to derive "a run does not insert its own key" from the laws | the key-bounded `EntryOk` reached that without a law change; my assessment: it can be dropped unless wanted for its own sake |

## Scope of every statement above

Depth ≥ 1 invariant worlds unless "outermost" is said; returning runs
(partial correctness); the module LIST of the design, not the SV string and
not `#sim`; the reflections (`MachineDefines`, `EntryDefines`) and the
runtime laws (`RefLaws`) stay premises.
