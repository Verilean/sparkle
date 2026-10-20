# Finding I fix — INTEGRATED on poc (2026-10-14)

Ruling: reviewer 2026-10-14, item 2. NOT a reachable miscompile: Finding I was shown on a constructed state
(depth pre-set, one memo emptied); by reading (docs/parallel/I-singleout-stale.md, eight cases) no real
compile reaches a stale hit. The fix makes the nested entry save / clear / restore
`sparkleSingleOutInstanceCache` like the let / loop / wire caches (the F/G pattern).
cgrun 3 GiB swap 0, one job at a time. GitHub CI: 0 runs.

| run | what | result |
|---|---|---|
| `i-int` | on the poc tree: `lake build Tests.AllTests` + SingleOutNestedFixTest, SingleOutHitTest, NestedLetCacheTest, SubInstanceKeyTest, NestedFailRestoreTest, DesignCoverageTest | exit 0, 1345 jobs, peak 2.74 GB |
| `i-int` | sims nested_let, subinst_key, writer, optprint, module_name | each exit 0 |
| `i-int` | census | unchanged: 134 declarations, 133 covered |
| `i-reg` | `SingleOutNestedRegressionTest` (first attempt, worker's file unchanged), then `Tests.AllTests` with it imported | exit 0, 1343 jobs, peak 0.47 GB |
Earlier, in isolation (verification-i-fix-isolated.md): 28-file sampled text comparison poc vs candidate —
no emitted-text difference.

`SingleOutNestedRegressionTest` (in AllTests; NO skip path — `fixed=F` is itself a failing check), measured:
```
A: returned=T hIrr insts=1 stmts=3;  STALE: keys left by A under the pTop and hIrr prefix=1
B: returned=T hIrr insts=1 stmts=3;  RESULT: equal=T B built=T (pTop memoised before B=F)
R1–R3 (return; foreign / poisoned seed; via synthesizeCombinational and synthesizeChild):
   reachedKid=T selfBuilt=T seedRestored=T depthBack=T; R2, R3: poison in module=F equals A=T
R4, R5 (pBad: writes, then if-then-else; via synthesizeChild / synthesizeCombinationalCore):
   threw=T intended=T ("if-then-else expressions cannot be synthesized to hardware") reachedKid=T
   selfBuilt=F seedRestored=T depthBack=T
R6, R7 (missing declaration): threw=T intended=T ("Unknown constant") reachedKid=F seedRestored=T
FIXED: restores=T child starts empty=T => fixed=T
pOuter: nested==alone=T;  pMach: stale hit on a real command=F
7 nested runs; failing checks []
```
Roles: `SingleOutNestedRegressionTest` — suite. `SingleOutNestedFixTest` — target-only comparison probe
(asserts only when fixed). `SingleOutStaleProbe` — BEFORE evidence ("the two modules must differ"),
never in a suite; on this tree it throws "the two modules are EQUAL", as expected.

NOT claimed: that a real compile ever took the stale hit; that the legacy route is deterministic (the
legacy sub-module memo and the type cache are still read at nested entries); the corpus (sample only).
