# Verification record: findings F and G fixes INTEGRATED into poc (2026-10-13)

Integrated tree: `a89aa0130f13ecd2aaa25dc048ccf505ef50ae57` = poc edd9496c merged with 0b881693 (findings F and G fixes; conflicts in
`Tests/Compiler/SubInstanceKeyTest.lean` → the fix branch's version with the fixed-flag, and
`docs/parallel/G-subinst-key.md` → poc's) + ONLY `Tests/Compiler/NestedFailRestoreTest.lean` and
`docs/parallel/F-nested-fail-restore.md` from par/b-22 (e195d57d; that branch has an old base — nothing else
taken) + one import in `Tests/AllTests.lean`. Compiler change: `Sparkle/Compiler/Elab.lean` only (a nested
entry saves the parent's let / loop / canon caches and the sub-instance output map, starts with them empty,
restores them in the `finally`; depth 0 unchanged). All runs: cgrun 3 GiB, swap 0, one job.
GitHub CI: 0 runs for this HEAD — no CI result is claimed.

## Runs

```
20261013-132354-fg-int: bash -c lake\ build\ Tests.AllTests\ Tests.Compiler.NestedLetCacheTest\ Tests.Compiler.SubInstanceKeyTest\ Tests.Compiler.SingleOutHitTest\ \&\&\ scripts/shipping-coverage/nested_let_sim.sh\ \&\&\ scripts/shipping-coverage/subinst_key_sim.sh\ \&\&\ scripts/shipping-coverage/writer_sim.sh 
memory.max=3221225472
memory.swap.max=0
verified=yes
result=success
exit=0
memory_peak_file=2427318272
events: low 0 high 0 max 0 oom 0 oom_kill 0 oom_group_kill 0 
Build completed successfully (1255 jobs).
```
```
20261013-140621-fg-nestfail: lake build Tests.Compiler.NestedFailRestoreTest 
memory.max=3221225472
memory.swap.max=0
verified=yes
result=success
exit=0
memory_peak_file=323162112
events: low 0 high 0 max 0 oom 0 oom_kill 0 oom_group_kill 0 
Build completed successfully (208 jobs).
```
```
20261013-140630-fg-final: lake build Tests.AllTests 
memory.max=3221225472
memory.swap.max=0
verified=yes
result=success
exit=0
memory_peak_file=448483328
events: low 0 high 0 max 0 oom 0 oom_kill 0 oom_group_kill 0 
Build completed successfully (1251 jobs).
```

(The first run was on tree 2e9188097dde727a4342bcffeb1904a1974d4d6b, i.e. before the nested-failure test and
its import were added; the last run is on the committed tree.)

## What the runs show

- AllTests + the three probes: 1255 jobs green; final AllTests 1251 jobs green.
- Finding F: `NESTEDLET: fixed=T; failing rows []`; simulation `fTop`, `fMid`, `lPlain` equal to the Lean
  source, x-cycles 0 (before the fix: X on all 94 cycles for `fTop` and `lPlain`).
- Finding G: `SUBINSTKEY: fixed=T; collisions []`; simulation `hTopWR`, `gTopWR`, `gTopRW`, `gW`, `gR` equal
  to the source (before: `hTopWR` got 14 / want 24).
  - sibling order: WR and RW both `collision=F`;
  - same / different arguments: hWR (`hW`: the same call twice; `hR`: `kSD y x` then `kSD x y`) `collision=F`.
- Nested entry that FAILS (`NestedFailRestoreTest`, asserting): two failing children — an undeclared name
  (early failure, child not reached) and `fBadW` (reaches the child `kSD`, then the intended
  "if-then-else expressions cannot be synthesized to hardware") — and a succeeding control, each through
  `synthesizeChild` and `synthesizeCombinationalCore` at depth 1: the four saved refs
  (`sparkleLetWireCache`, `sparkleLoopWireCache`, `sparkleWireCanon`, `sparkleSubInstanceOutputs`) equal
  their seeds exactly afterwards and the depth is back; reachability asserted through a ref outside the fix
  (`kSD` absent from the sub-module / child caches before the run, present after for `fBadW` and the
  control, absent for the undeclared name).
- writer simulation 7/7 equal to the source; combined digests equal to the pre-integration ones:
  361 declarations 11874691237837614088, 84 declarations 2141260620024790681.

## Not established

All successful inputs; a corpus declaration with either pattern (none found by reading); the port-map
entries written before the failure are not observable after the restore (the intended exception shows the
second leaf was being translated); the refs outside the fix (single-output map, zeta marks, sub-module and
child caches) are neither cleared nor restored by a nested entry — logged, unchanged by this integration.

## Log excerpts

```
n:241:0: SUBINSTKEY RW DETECT: children whose nested module differs from their alone module or reads undeclared names: [] => collision=F
n:241:0: SUBINSTKEY WR DETECT: children whose nested module differs from their alone module or reads undeclared names: [] => collision=F
n:241:0: SUBINSTKEY hWR DETECT: children whose nested module differs from their alone module or reads undeclared names: [] => collision=F
n:241:0: SUBINSTKEY: fixed=T; collisions []
n:261:0: NESTEDLET: fixed=T; failing rows []
NESTEDLETSIM Tests.Compiler.NestedLetCacheTest.fMid: command==source T nofe==source T command==nofe T x-cycles command=0 nofe=0 cycles=94
NESTEDLETSIM Tests.Compiler.NestedLetCacheTest.fTop: command==source T nofe==source T command==nofe T x-cycles command=0 nofe=0 cycles=94
NESTEDLETSIM Tests.Compiler.NestedLetCacheTest.lPlain: command==source T nofe==source T command==nofe T x-cycles command=0 nofe=0 cycles=94
SUBINSTKEYSIM Tests.Compiler.SubInstanceKeyTest.gR: command==source T nofe==source T command==nofe T x-cycles command=0 nofe=0 cycles=94
SUBINSTKEYSIM Tests.Compiler.SubInstanceKeyTest.gTopRW: command==source T nofe==source T command==nofe T x-cycles command=0 nofe=0 cycles=94
SUBINSTKEYSIM Tests.Compiler.SubInstanceKeyTest.gTopWR: command==source T nofe==source T command==nofe T x-cycles command=0 nofe=0 cycles=94
SUBINSTKEYSIM Tests.Compiler.SubInstanceKeyTest.gW: command==source T nofe==source T command==nofe T x-cycles command=0 nofe=0 cycles=94
SUBINSTKEYSIM Tests.Compiler.SubInstanceKeyTest.hTopWR: command==source T nofe==source T command==nofe T x-cycles command=0 nofe=0 cycles=94
WRITERSIM Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2: new==source T old==source T new==old T cycles=142 outputs=1 (lines simulated: 142; modules besides the top: 3
WRITERSIM Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH: new==source T old==source T new==old T cycles=142 outputs=1 (lines simulated: 142; modules besides the 
WRITERSIM Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH: new==source T old==source T new==old T cycles=142 outputs=2 (lines simulated: 142; modules besides the to
WRITERSIM Sparkle.Tests.Compiler.ShippingMachineSeqTest.chained: new==source T old==source T new==old T cycles=142 outputs=1 (lines simulated: 142; modules besides the to
WRITERSIM Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand: new==source T old==source T new==old T cycles=142 outputs=1 (lines simulated: 142; modules besides the top:
WRITERSIM Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid: new==source T old==source T new==old T cycles=142 outputs=2 (lines simulated: 142; modules besides the top: 1
WRITERSIM Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent: new==source T old==source T new==old T cycles=142 outputs=1 (lines simulated: 142; modules besides the top
lean:359:0: NESTEDFAIL CASE FAILING missing declaration via synthesizeChild: threw=T intended=T reachedKid=F [expected reachedKid=F; kSD cached before the run=F; after: sparkleSubModuleCache=F sparkleChildCache=F]
lean:359:0: NESTEDFAIL CASE FAILING missing declaration via synthesizeCombinationalCore: threw=T intended=T reachedKid=F [expected reachedKid=F; kSD cached before the run=F; after: sparkleSubModuleCache=F sparkleChildCache=F]
lean:359:0: NESTEDFAIL CASE FAILING fBadW (writes, then if-then-else) via synthesizeChild: threw=T intended=T reachedKid=T [expected reachedKid=T; kSD cached before the run=F; after: sparkleSubModuleCache=T sparkleChildCache=T]
lean:359:0: NESTEDFAIL CASE FAILING fBadW (writes, then if-then-else) via synthesizeCombinationalCore: threw=T intended=T reachedKid=T [expected reachedKid=T; kSD cached before the run=F; after: sparkleSubModuleCache=T sparkleChildCache=T]
lean:359:0: NESTEDFAIL CASE SUCCEEDING okW via synthesizeChild: threw=F intended=T reachedKid=T [expected reachedKid=T; kSD cached before the run=F; after: sparkleSubModuleCache=T sparkleChildCache=T]
lean:359:0: NESTEDFAIL CASE SUCCEEDING okW via synthesizeCombinationalCore: threw=F intended=T reachedKid=T [expected reachedKid=T; kSD cached before the run=F; after: sparkleSubModuleCache=T sparkleChildCache=T]
lean:359:0: NESTEDFAIL sparkleSubInstanceOutputs: threw=T restored=T depthBack=T [FAILING missing declaration via synthesizeChild; entries after=2, seeded=2; depth before=1 after=1]
lean:359:0: NESTEDFAIL sparkleSubInstanceOutputs: threw=T restored=T depthBack=T [FAILING missing declaration via synthesizeCombinationalCore; entries after=2, seeded=2; depth before=1 after=1]
lean:359:0: NESTEDFAIL sparkleSubInstanceOutputs: threw=T restored=T depthBack=T [FAILING fBadW (writes, then if-then-else) via synthesizeChild; entries after=2, seeded=2; depth before=1 after=1]
lean:359:0: NESTEDFAIL sparkleSubInstanceOutputs: threw=T restored=T depthBack=T [FAILING fBadW (writes, then if-then-else) via synthesizeCombinationalCore; entries after=2, seeded=2; depth before=1 after=1]
lean:359:0: NESTEDOK sparkleSubInstanceOutputs: threw=F restored=T depthBack=T [SUCCEEDING okW via synthesizeChild; entries after=2, seeded=2; depth before=1 after=1]
lean:359:0: NESTEDOK sparkleSubInstanceOutputs: threw=F restored=T depthBack=T [SUCCEEDING okW via synthesizeCombinationalCore; entries after=2, seeded=2; depth before=1 after=1]
```
