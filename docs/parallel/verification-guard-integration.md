# Verification record: the two compiler guards INTEGRATED into poc, with the leaf `cnt` connection (2026-10-13)

Integrated tree: `880321590b5ace204923c19c87a09df6d74b3fb4` = poc 02d38ad0 merged with be0c5bbc (guard candidate; conflict in
`lakefile.lean` only, both sides kept) + integrator changes of NAMES / WORDING only: the theorem
`mergeChecked_keeps_reg` renamed `mergeChecked_keeps_nonAssign`; "register guard" → "non-assignment guard"
in a doc comment of `Sparkle/IR/RefineCheck.lean`, in `Tools/ShippingGuardsLeaf.lean`, in the firing test
and in the candidate note; two imports in `Tests/AllTests.lean`. cgrun 3 GiB, swap 0, one job.
GitHub CI: 0 runs for this HEAD — no CI result is claimed.

## The compiler change (`Sparkle/IR/RefineCheck.lean` only)

1. `checkedOptimize`, instance-free branch: the optimizer's candidate is shipped only if
   `refineCheck m o && PrintGuard.printOk o`; otherwise the INPUT module is shipped.
2. `mergeChecked`, last branch: the merged module is accepted only if, in addition, its body is not
   assignment-only — "a non-assignment statement remains". This is NOT a statement that a particular register
   is kept, and it is not claimed for general modules beyond that.
Both are fallbacks to the input module: no source is rejected, the set of accepted inputs is unchanged. The
raw-side print condition is still derived from the run (`leaf_entry_raw`), not assumed.

## Runs

```
20261013-140725-guard-int: bash -c lake\ build\ Tests.AllTests\ Tests.Compiler.OptPrintCensusTest\ Tests.Compiler.NestedLetCacheTest\ Tests.Compiler.SubInstanceKeyTest\ Tests.Compiler.OptPrintSourceTest\ Tests.Compiler.LeafEntryCexProbe\ \&\&\ scripts/shipping-coverage/optprint_sim.sh\ \&\&\ scripts/shipping-coverage/nested_let_sim.sh\ \&\&\ scripts/shipping-coverage/subinst_key_sim.sh\ \&\&\ scripts/shipping-coverage/writer_sim.sh 
memory.max=3221225472
memory.swap.max=0
verified=yes
result=success
exit=0
memory_peak_file=2618953728
events: low 0 high 0 max 0 oom 0 oom_kill 0 oom_group_kill 0 
Build completed successfully (1262 jobs).
```
```
20261013-144728-guard-final: lake build Tests.AllTests 
memory.max=3221225472
memory.swap.max=0
verified=yes
result=success
exit=0
memory_peak_file=464203776
events: low 0 high 0 max 0 oom 0 oom_kill 0 oom_group_kill 0 
Build completed successfully (1260 jobs).
```

(The first run was on tree 24e8457a6d8a1b2b4bb2d2d8c341456f919bc159, before the wording change of three
files; the last run is on the committed tree.)

## What the runs show

- AllTests + census + probes: 1262 jobs green; final AllTests 1260 jobs green.
- `cnt.machine_ships_leafC` (in AllTests): premises exactly `ChildBnd`, the run, `MachineDefines cnt` — all
  ALLOWED; against `cnt.machine_ships_wired` the premises `simpleBody b = false`, `seqCheck … (checkedOptimize
  b).body`, the declWidth/weOf agreement and `MachineCloses cnt` are gone, and the two NOT-ALLOWED binders
  `hmergeReg`, `hoptPrint` of `cnt.machine_ships_leafB` are discharged by the two guard theorems
  (`mergeChecked_keeps_nonAssign`, `checkedOptimize_instFree_print`); standard axioms. One declaration; a
  leaf register machine as an entry; conclusion `MachineShips` of one module, not the SV string, not `#sim`.
- Guard firing, with the guarantee (in AllTests): on `optCex` the print guard fires and the input module is
  shipped and passes `printOk`; on `mergeCex` the non-assignment guard fires and the input module is kept;
  on the real source `shlAdd32` the print guard fires and the shipped top passes `printOk`.
- Real sources (`OptPrintSourceTest`): shipped modules with `printOk` false: 0 (6 before).
- Census on 362 returned declarations: would-fire list empty for the print guard, FIRES 0 for the merge
  guard; digests of shipped texts equal to the pre-guard ones: 361 declarations 1444467916182415447, 362
  declarations 8149634735370364912; `WIREWIDTH` 361: 11874691237837614088; `NESTEDLET` 84:
  2141260620024790681.
- Simulations: optprint 12/12 equal to the Lean source (shipped top with `printOk` false: 0); nested-let
  3/3, sub-instance key 5/5, writer 7/7 equal.

## Not established

All successful inputs. Texts of sources outside the measured population: the six constructed 32/64-bit
shift declarations now ship the unoptimised module (measured equal to the source on one stimulus).
The merge-keeps THEOREM for leaf-shaped modules (par/a-30) is not built yet; the guard stays regardless.

## Log excerpts

```
n:157:0: OPTPRINT D TOTAL: 0 occurrences, 0 distinct module names
n:157:0: OPTPRINT DIGEST today [legacy+machine+mixed (the MemoHitCensusTest population)]: 361 declarations, combined digest 1444467916182415447
n:157:0: OPTPRINT DIGEST guarded [legacy+machine+mixed (the MemoHitCensusTest population)]: 361 declarations, combined digest 1444467916182415447
n:157:0: OPTPRINT DIGEST changed [legacy+machine+mixed (the MemoHitCensusTest population)]: 0 declarations []
n:157:0: OPTPRINT DIGEST today [all four routes]: 362 declarations, combined digest 8149634735370364912
n:157:0: OPTPRINT DIGEST guarded [all four routes]: 362 declarations, combined digest 8149634735370364912
n:157:0: OPTPRINT DIGEST changed [all four routes]: 0 declarations []
n:157:0: OPTPRINT MERGE: tops measured 362 (before the merge, after the zero-width cleanup); body not assignment-only 13; of them the merge changes the module 6; of them accepted today (refineCheck && masksKept && printOk) 6; FIRES (accepted today and the merged body is assignment-only: the candidate conjunct would refuse it) 0 []
.lean:110:0: LEAFENTRYC PREMISE Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machine_ships_leafC: ALLOWED     binder hbnd : Tools.ShippingChildInv.ChildBnd mref cref w
.lean:110:0: LEAFENTRYC PREMISE Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machine_ships_leafC: ALLOWED     binder hr : Tools.ShippingEntrySoundness.RunsTo
.lean:110:0: LEAFENTRYC PREMISE Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machine_ships_leafC: ALLOWED     binder entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref `Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt
n:222:0: OPTPRINT SRC SUMMARY: 12 of 12 declarations ran (not run: []); hits (branch seq, printOk b, candidate accepted, printOk of the shipped module false) 0 []; predictions of printOk(checkedOptimize b) right 6, wrong 6 [Tests.Compiler.OptPrintSourceTest.shlAdd32 (predicted F, got T),
.lean:75:0: GUARDFIRES OPT VERDICT: the print guard FIRES on optCex (candidate accepted by refineCheck, outside the print fragment); the input module is shipped and passes printOk — the disjunction of opt_guard_guarantee holds by BOTH disjuncts here
.lean:100:0: GUARDFIRES MERGE VERDICT: the register guard FIRES on mergeCex (merge accepted by refineCheck, masksKept and printOk, merged body assignment-only); the input module is kept and is not assignment-only — the conclusion of merge_guard_guarantee
.lean:125:0: GUARDFIRES SRC VERDICT: on the real source Tests.Compiler.OptPrintSourceTest.shlAdd32 the print guard FIRES; the shipped top is the unoptimised module of the full entry and passes printOk (on poc: the optimised module, printOk false). Whether the text equals the source is measured by scripts/shipping-coverage/optprint_sim.sh, not here
OPTPRINTSIM TOTAL: 12 declarations; command==source T=12 F=0 not-compared=0; shipped top with printOk false: 0; text changes under the guard: 0 (one stimulus; not a proof)
.lean:100:0: GUARDFIRES MERGE VERDICT: the non-assignment guard (a non-assignment statement must remain) FIRES on mergeCex (merge accepted by refineCheck, masksKept and printOk, merged body assignment-only); the input module is kept and is not assignment-only — the conclusion of merge_guard_guarantee
```
