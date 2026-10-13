# Finding I: the INTEGRATION regression test

Branch `par/f-1` (base poc `f1ed620f` + the fix candidate's six files from
`fix/singleout-build`). **WRITTEN, NOT BUILT, NOT RUN.** Every "PREDICTED"
is from reading `Sparkle/Compiler/Elab.lean` and from the lines the
comparison probe gave on the candidate
(`docs/parallel/verification-i-fix-isolated.md`: `A 1/3`, `B 1/3`,
`equal=T`, `pOuter nested=1 alone=1 nested==alone=T`, `pMach machine shape=F
real=1 cold=1`), not an observation of the new file.

Finding I was shown on a CONSTRUCTED state (a pre-set depth, an emptied
memo). By reading, no real compile reaches it
(`docs/parallel/I-singleout-stale.md` §2). Nothing here changes that.

Reviewer's ruling (2026-10-14) this file answers: the integration regression
must REQUIRE `fixed=true`, assert equality / instance presence / parent-seed
restoration unconditionally, assert the reachability of the failing path as
the F / G tests do, and keep the old "must differ" probe as before-evidence
outside the normal suite.

## 1. The three tests of finding I

| file | role | where | on a tree WITH the fix | on a tree WITHOUT |
|---|---|---|---|---|
| `Tests/Compiler/SingleOutNestedRegressionTest.lean` (NEW) | regression, asserts unconditionally | SUITE: to be imported by `Tests/AllTests.lean` | green (PREDICTED) | THROWS (PREDICTED) |
| `Tests/Compiler/SingleOutNestedFixTest.lean` (unchanged) | comparison probe: measures `fixed`, asserts only when it is true | target-only | green, `fixed=T` (MEASURED in isolation) | green, `fixed=F` (PREDICTED) |
| `Tests/Compiler/SingleOutStaleProbe.lean` (unchanged) | BEFORE evidence: asserts that the two modules DIFFER | never in a suite; target-only, run on purpose | THROWS "the two modules are EQUAL" (MEASURED in isolation) | green (MEASURED on poc) |

For the integrator: add ONE line to `Tests/AllTests.lean`,

    import Tests.Compiler.SingleOutNestedRegressionTest

No `lakefile.lean` change (the file is in the `Tests` library; its only
project import is `Tests.Compiler.CallWidthHuntTest`, already in the suite).
`cleanLegacy` is copied locally (eight lines) so that
`MachineFallThroughCensusTest` does not enter the closure of the suite.

## 2. What each assertion checks, and what would make it fail

The command collects failing checks in one list, logs it, and throws when it
is not empty. There is no branch that skips a check.

### (b) the scenario of the finding

Run A: full entry on `pTop` (`hIrr x + x`, `hIrr` an untagged
`@[irreducible]` helper), reset refs, depth 0. Run B: the full entry again,
depth pre-set to 1, refs as A left them, `sparkleSubModuleCache` emptied.

| check | fails when |
|---|---|
| A returns and B returns | either entry throws |
| A has ≥ 1 `hIrr` instance | the legacy single-output path is no longer the one `pTop` takes (the test would exercise nothing) |
| B has ≥ 1 `hIrr` instance | B took the stale hit — the finding |
| `A == B` (module values) | any difference between the two modules |
| after A the map holds ≥ 1 key with prefix `<pTop module>#<hIrr module>#` | the stale entry B would hit is not there: the state of the finding is not constructed (e.g. the key format changed, or a depth-0 exit started clearing the map) |
| `pTop` absent from `sparkleSubModuleCache` before B, present after | B was a memo hit, not a build |

### (c) parent seed restoration — seven nested entries

Each: `resetRefs`, the map seeded, depth 1, the entry inside `try … catch`,
then the map and the depth read back.

| run | declaration | entry | seed | outcome required |
|---|---|---|---|---|
| R1 | `pTop` | `synthesizeCombinational` | a foreign key | returns |
| R2 | `pTop` | `synthesizeCombinational` | foreign + POISONED keys | returns |
| R3 | `pTop` | `synthesizeChild` | foreign + POISONED keys | returns |
| R4 | `pBad` | `synthesizeChild` | foreign + POISONED keys | throws, late |
| R5 | `pBad` | `synthesizeCombinationalCore` | foreign + POISONED keys | throws, late |
| R6 | undeclared name | `synthesizeChild` | foreign + POISONED keys | throws, early |
| R7 | undeclared name | `synthesizeCombinationalCore` | foreign + POISONED keys | throws, early |

`pBad` (tagged, two result leaves, the pattern of
`NestedFailRestoreTest.fBadW`): first leaf `hIrr x + x` — the child's builder
instantiates `hIrr` and writes its own map entry — second leaf
`if (0 : Nat) = 0 then x else y`, refused by `Rec.handleErrorPatterns`.

| check (every run) | fails when |
|---|---|
| `seedRestored`: the map holds EXACTLY the seed afterwards (same size, every seeded key at its seeded value) | the `finally` does not put the saved map back (after a return OR a throw); the child's entries leak to the parent; a seeded value was overwritten |
| `depthBack`: `sparkleSynthDepth` reads 1 | the decrement is not in the `finally` |
| `intended`: a throwing run's message contains the intended text, lower case ("if-then-else expressions cannot be synthesized to hardware" for `pBad`, "unknown constant" for the undeclared name); a returning run does not throw | the run fails EARLIER or elsewhere than meant, or a returning run throws, or a throwing run returns |
| `hIrr` cached before the run = F | reachability could be a cache hit (it cannot: `resetRefs` empties both module caches just before, and the absence is read) |
| `reachedKid`: `hIrr` is a key of `sparkleSubModuleCache` or `sparkleChildCache` afterwards — required T for R1–R5, F for R6, R7 | `pBad` threw BEFORE reaching the helper's instance (the write-then-throw path is not exercised), or the early failure was not early |
| declaration cached before the run = F | the run could be a memo hit |
| `selfBuilt`: the declaration is in a module cache afterwards — required T for R1–R3, F for R4–R7 | a returning run was not a build; a throwing run memoised something |
| returning runs: ≥ 1 `hIrr` instance | the instance was skipped |

Neither module cache is cleared or restored by a NESTED entry (READ: cleared
at depth 0 only), so the reachability keys survive a failing run. The entry
`pBad`'s builder wrote before throwing cannot be seen after a restore; the
intended message says the SECOND leaf was being translated, `emitLeaves`
translates leaves in order (READ, as in `NestedFailRestoreTest`), and
`reachedKid` says the helper's module was built.

### (d) the child does not see the parent's entries — how it is observed

Without editing the compiler: the seed of R2–R5 contains every key run A left
under `<pTop module>#<hIrr module>#` — the exact key the nested builder of
`pTop` looks up — bound to `POISON_single_out_wire_of_the_parent`, a wire
name no builder makes. A child that read the parent's map would take the hit
in the legacy handler: it would return the poison wire, declare no wire, emit
no instance, and the poison name would occur in the module.

| check (R2, R3) | fails when |
|---|---|
| ≥ 1 `hIrr` instance | the child hit the parent's entry |
| the poison name does not occur in `repr` of the module | the child used the parent's wire |
| the module EQUALS run A's | the child's result depends on the parent's map in any way |
| (from (c)) the poisoned key still holds the poison afterwards | the child's entry under the SAME key replaced the parent's |

### (a) fixed — REQUIRED

`fixed = restores && child starts empty`, with `restores` = R1 returned and
the map is exactly the foreign seed afterwards, `child starts empty` = at
least one poisoned key was seeded and R2's module has an `hIrr` instance and
no poison. `fixed=F` is itself a failing check ("NOT FIXED: …"), whatever
the other rows say.

### (e) real commands — unconditional

| row | check | fails when |
|---|---|---|
| `pOuter` (calls the tagged `pMid`, whose body instantiates `hIrr`) | the entry returns; the nested `pMid` is in its design; `pMid` alone returns; `nested == alone`; nested has ≥ 1 `hIrr` instance | a run throws; the nested module differs from the alone one; the instance is missing |
| `pMach` (register machine with `hIrr` in its body; row 5 of `I-singleout-stale.md` §2) | the real entry (`synthesizeCombinationalCore`, depth 0) and the clean legacy arm both return; the same number of `hIrr` instances; ≥ 1 | a run throws; the counts differ (a stale hit on a REAL command — a finding on either tree); the path is not exercised |

`machine shape` of `pMach` is LOGGED, not asserted (PREDICTED and measured
`F`: `unifiedGateRoot` refuses the call). If a later compiler accepts the
shape, the row still compares the real entry with the clean legacy arm; the
line shows that the hole it was written for is no longer the one exercised.

## 3. PREDICTED log lines on a tree with the fix

```
SINGLEOUTREG START A (depth 0, reset refs)
SINGLEOUTREG A: returned=T hIrr insts=1 stmts=3
SINGLEOUTREG STALE: keys left by A under the pTop and hIrr prefix=1 map size=1
SINGLEOUTREG START B (depth 1, refs as A left them, the sub-module memo emptied)
SINGLEOUTREG B: returned=T hIrr insts=1 stmts=3
SINGLEOUTREG RESULT: equal=T B built=T (pTop memoised before B=F)
SINGLEOUTREG START RUN R1 RETURN pTop (foreign seed) via synthesizeCombinational (depth 1, reset refs, 1 seeded entries)
SINGLEOUTREG RUN R1 RETURN pTop (foreign seed) via synthesizeCombinational: threw=F intended=T reachedKid=T selfBuilt=T seedRestored=T depthBack=T hIrr insts=1 poison in module=F equals A=- [entries after=1, seeded=1; expected reachedKid=T selfBuilt=T; cached before the run: hIrr=F self=F; depth before=1 after=1]
SINGLEOUTREG RUN R2 RETURN pTop (poisoned seed) via synthesizeCombinational: threw=F intended=T reachedKid=T selfBuilt=T seedRestored=T depthBack=T hIrr insts=1 poison in module=F equals A=T [entries after=2, seeded=2; …]
SINGLEOUTREG RUN R3 RETURN pTop (poisoned seed) via synthesizeChild: threw=F intended=T reachedKid=T selfBuilt=T seedRestored=T depthBack=T hIrr insts=1 poison in module=F equals A=T [entries after=2, seeded=2; …]
SINGLEOUTREG RUN R4 THROW pBad (writes, then if-then-else) via synthesizeChild: threw=T intended=T reachedKid=T selfBuilt=F seedRestored=T depthBack=T hIrr insts=0 poison in module=- equals A=- [entries after=2, seeded=2; …]
SINGLEOUTREG THREW [R4 …]: … if-then-else expressions cannot be synthesized to hardware. …
SINGLEOUTREG RUN R5 THROW pBad (writes, then if-then-else) via synthesizeCombinationalCore: threw=T intended=T reachedKid=T selfBuilt=F seedRestored=T depthBack=T …
SINGLEOUTREG RUN R6 THROW missing declaration via synthesizeChild: threw=T intended=T reachedKid=F selfBuilt=F seedRestored=T depthBack=T …
SINGLEOUTREG RUN R7 THROW missing declaration via synthesizeCombinationalCore: threw=T intended=T reachedKid=F selfBuilt=F seedRestored=T depthBack=T …
SINGLEOUTREG FIXED: restores=T child starts empty=T => fixed=T
SINGLEOUTREG pOuter: returned=T pMid nested found=T hIrr insts nested=1 alone=1 nested==alone=T
SINGLEOUTREG pMach: machine shape=F real=T cold=T hIrr insts real=1 cold=1 => stale hit on a real command=F
SINGLEOUTREG: 7 nested runs; failing checks []
```

(Each `START` line is also on standard error, flushed, before its run; each
`RUN` is preceded by its `START RUN` line.)

PREDICTED on a tree WITHOUT the fix: `B: … insts=0 stmts=2`, `equal=F`; R1
`seedRestored=F` (`entries after=2`: the seed and `pTop`'s own entry); R2,
R3 `hIrr insts=0`, `poison in module=T`, `equals A=F`; R4, R5
`seedRestored=F` (`pBad`'s entry left behind); R6, R7 all `T` (the map is
neither cleared nor written: these two do not tell the trees apart);
`fixed=F`; the command throws.

## 4. NOT determined by reading

* That `pBad` fails at the intended place. Its first leaf differs from
  `fBadW`'s (an untagged irreducible helper instead of a tagged
  two-output child). PREDICTED: the entry takes the legacy arm (as `pTop`,
  measured), `emitLeaves` translates `a` (building `hIrr`), then throws the
  `if-then-else` text on `b`. If the front end rejects `pBad` earlier, or a
  certified gate takes it, R4 / R5 fail with `intended=F` or `reachedKid=F`
  and the exact message is on the `THREW` line.
* That R2 / R3's module EQUALS run A's. The comparison probe measured
  `A == B` with the child cache KEPT between the runs; R2 / R3 start from
  reset refs, so `hIrr` is rebuilt at depth 2. No wire name depends on the
  depth or on `sparkleCallCounter` (READ: the counter is a runaway backstop
  only), so equality is PREDICTED. If it fails while `poison in module=F`
  and `hIrr insts=1`, the difference is not a stale hit; the row then needs
  the two modules printed, not a weaker assertion.
* The exact number of keys run A leaves (`1` PREDICTED: one instance, and
  the helper's own nested entries are dropped by the restore). The test
  requires ≥ 1.
* The text of the `getConstInfo` error in this Lean version ("unknown
  constant", lower case, as measured by `NestedFailRestoreTest`).

## 5. NOT claimed

That finding I is reachable by a real compile; that any design changes; that
the legacy route is deterministic in general (`sparkleSubModuleCache` and
`sparkleTypeCache` are still read at a nested entry as the world holds
them); anything built.
