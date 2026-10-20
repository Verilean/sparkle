# Findings F and G: a nested entry that FAILS still restores its parent's caches

Worker B, branch `par/b-22` from `fix/fg-on-poc-build` (`41a835f4`). **WRITTEN, NOT BUILT, NOT
RUN: no `lean`, `lake` or `iverilog` was started. Nothing below is measured by me.** Line
numbers are `Sparkle/Compiler/Elab.lean` at `41a835f4`.

Kinds of statement: **READ** (what the code says), **PREDICTED** (what a run should print),
**NOT ESTABLISHED**.

New files: `Tests/Compiler/NestedFailRestoreTest.lean`, this note. Nothing else touched.

## 1. The acceptance condition

"When a NESTED entry FAILS, the `finally` still restores the parent's caches." No existing test
exercises it: the two `fixedProbe`s (`NestedLetCacheTest` §0 with `kCount`,
`SubInstanceKeyTest.fixedProbe` with `hW`) run a nested entry that RETURNS; their `catch`
only turns a throw into `nestedRan=F`, i.e. `fixed=F` and no assertion.

## 2. READ

`synthesizeCombinationalCoreWith`:

| Line | What |
|---|---|
| 5430–5432 | `depth ← sparkleSynthDepth.get`; throw at the depth limit (BEFORE any save) |
| 5445, 5460 | saves that existed before: `savedFvarMap`, `savedWireWidthCache` |
| 5472–5480 | finding F: `savedLetWireCache`, `savedLoopWireCache`, `savedWireCanon` (`pure {}` at depth 0, `.get` otherwise) |
| 5489–5491 | finding G: `savedSubInstanceOutputs` |
| 5510–5515 | nested entry: the six refs set to `{}` |
| 5516 | `sparkleSynthDepth.set (depth + 1)` |
| 5521–5528 | `doSynth`; its first statement is `getConstInfo declName` (5522) |
| 5529–5540 | `try doSynth finally` — `sparkleSynthDepth.modify (· - 1)`, then under `if depth != 0` the six `.set saved…` (F: 5537–5539, G: 5540) |

Between the last save (5491) and the `try` (5529) there are only `IO.Ref.set`s and one
`let`: no `throwError`, no `MetaM` call that can fail.

Entry functions a test can call: `synthesizeCombinationalCore` (8865, the function above with
the real translator) and `synthesizeChild` (8876: `sparkleChildCache` lookup, else
`synthesizeCombinational`, i.e. `synthesizeCombinationalWith` 5546 = the core entry plus pure
clean-up; the result is recorded only when it returns). A call site reaches `synthesizeChild`
through `childSynthEntry` (5574).

Deterministic throws inside the `try`:

* an undeclared name: `getConstInfo` (5522) throws;
* `Rec.handleErrorPatterns` (5661–5676), the first thing `translateExprToWireApp` does for an
  application with a constant head (6771): head `ite` / `dite` ⇒
  `throwError "if-then-else expressions cannot be synthesized to hardware. …"`;
* `emitLeaves` (2153–2190) translates the result leaves in list order and has no `catch`;
  `splitReturnLeavesStep` (1859–1963) splits a single-constructor record result into its
  fields, a `Signal` field being one leaf as written.

Callers of a nested entry (6538–6563): both `try … catch _ =>` arms re-throw another error
("Sub-module synthesis failed for …", "Cannot synthesise …: not inlinable and not a hardware
module."); neither goes on with the parent after a failed nested entry. `tryInlineUnfold`
(6299–6331) is the place that does go on after a failure of a translation that may contain
nested entries; it restores its own snapshot (`restoreWireCaches`, 5643), which includes the
four refs.

## 3. The test

Self-contained (`import Lean.Elab.Command`, `import Sparkle`); local declarations `kSD`
(two-output child, as in `SubInstanceKeyTest`), `okW` (`(kSD x y).sm + (kSD x y).df`, the body
of `SubInstanceKeyTest.hW`), `fBadW`:

    @[hardware_module]
    def fBadW (x y : Signal defaultDomain (BitVec 5)) : SumDiff defaultDomain :=
      { sm := (kSD x y).sm + (kSD x y).df, df := if (0 : Nat) = 0 then x else y }

Six runs = {`missing` (undeclared name), `fBadW`, `okW`} × {`synthesizeChild`,
`synthesizeCombinationalCore`}. Each run (`probe`):

1. every per-synthesis ref reset;
2. seeded, two entries each, with keys and wires no run writes: `sparkleLetWireCache`,
   `sparkleLoopWireCache`, `sparkleWireCanon`, `sparkleSubInstanceOutputs`; one entry each in
   refs outside the fix: `sparkleFvarValueMap`, `sparkleWireWidthCache`,
   `sparkleSingleOutInstanceCache`, `sparkleFvarZetaVisited`;
3. `sparkleSynthDepth.set 1` (what a nested entry reads);
4. the entry inside `try … catch`, the message kept;
5. read back: the depth; for each of the four refs `restored` = same size as the seed and every
   seeded key at its seeded value; the other refs as they are.

Lines: `NESTEDFAIL <ref>: threw=<T/F> restored=<T/F> depthBack=<T/F> [<case>; entries after=<n>,
seeded=<k>; depth before=1 after=<d>]` for the failing runs, `NESTEDOK <ref>: …` for the
control, `NESTEDFAIL THREW [<case>]: <message>`, `NESTEDFAIL OTHER [<case>]: …` (log only),
last `NESTEDFAIL: 6 runs; failing checks […]`.

ASSERTED (one `throwError` at the end, after all lines, listing every failed check by ref and
case): failing runs `threw=T`; control runs `threw=F`; all runs `restored=T` for the four refs
and `depthBack=T`.

### 3a. Reachability and the intended exception (reviewer finding, P2)

Per run one line `NESTEDFAIL CASE <case> via <entry>: threw= intended= reachedKid= […]`, ASSERTED:

* `intended` — `fBadW`: the message contains (lower case)
  `if-then-else expressions cannot be synthesized to hardware` (READ: 5665); `missing`: it
  contains `unknown constant` (lower case: the capital differs between Lean versions; the text
  is Lean's, PREDICTED); `okW`: no throw. Another error fails the test, message printed.
* `reachedKid` — `kSD` is a key of `sparkleSubModuleCache` or of `sparkleChildCache` after the
  run. READ: both are cleared at depth 0 only (5496–5497) and are not in the `finally`, so they
  are not among the restored refs and keep what a failed nested run wrote; `probe` empties them
  (`resetAll`) and reads `kSD`'s absence just before the run (`kSD cached before the run=F`,
  asserted), so the key is neither a seed nor a cache hit; `kSD` is local to the test file.
  Required `T` for `fBadW` and `okW`, `F` for `missing`.

`intended=T` for `fBadW` means the second leaf was being translated, which `emitLeaves` does
only after the first leaf returned. The port-map entries themselves are not observable after
the restore.

PREDICTED: `fBadW` and `okW` `reachedKid=T`, `missing` `reachedKid=F`, `intended=T` in all six.
NOT established: that no earlier stage rewords or wraps the if-then-else error on this route.

## 4. PREDICTED

On `41a835f4` (with the fixes): the 24 ref lines all `restored=T depthBack=T`, `threw=T` in the
16 `NESTEDFAIL` lines and `threw=F` in the 8 `NESTEDOK` lines; no throw from the test.
`THREW` messages: an unknown-constant message for `missing`; for `fBadW` the if-then-else
message of 5665. `OTHER`: `sparkleFvarValueMap=T sparkleWireWidthCache=T`; the single-out seed
and the zeta seed kept; for `fBadW` and `okW` `the run synthesised kSD … =T` (`sparkleChildCache`
keeps `kSD`: it is not part of any restore, and a failed run leaves it), for `missing` `=F`.

On a tree without the fixes (e.g. `c46b309c`): the test FAILS.

* `sparkleLetWireCache`, `sparkleLoopWireCache`, `sparkleWireCanon`: `restored=F` in all six
  runs (cleared — 5512–5514 in this tree's numbering — and never written back); `entries after=0` in the `missing` runs.
* `sparkleSubInstanceOutputs`: `restored=F`, `entries after=4` in the `fBadW` and `okW` runs
  (the seed and the two entries of `kSD x y`; the two-entry count is what `G-subinst-key.md`
  measured for `hW`); **`restored=T` in the two `missing` runs** — without the fix that entry
  neither clears nor writes the map, so these two lines do not distinguish the trees.
* `depthBack=T` everywhere (the decrement was already in the `finally`).

The reviewer's other two points are not duplicated: sibling order is `SubInstanceKeyTest` rows
`WR` / `RW` (`collision` flags, asserted `F` when `fixed=T`); same / different arguments is its
row `hWR`, `hW` (`kSD x y` twice) against `hR` (`kSD y x` then `kSD x y`), line
`CHILD …hR: nested==alone …`. That file is not imported here because its closure contains the
census of `NestedLetCacheTest`, which is not in `Tests.AllTests`.

## 5. NOT established

* Everything in §4 (nothing was run), including that `fBadW` throws at its SECOND leaf after
  the first leaf wrote: if an earlier stage refuses `fBadW` (a gate reader, the record result),
  the run still throws and the assertions still hold on the fixed tree, but the
  `sparkleSubInstanceOutputs` line of `fBadW` then says no more than that of `missing`. The
  `OTHER` flag `the run synthesised kSD` is the only evidence of how far the child got; whether
  the child wrote port-map entries before throwing cannot be seen after a restore.
* An exception between the saves and the `try`: by reading there is none (§2), and the depth
  limit throws before the saves; not tested.
* Exceptions `try … catch` / `finally` do not see as ordinary errors: heartbeat and
  recursion-depth (runtime) exceptions, interrupts, a panic, a stack overflow. `finally` in
  `MetaM` is expected to run for runtime exceptions and interrupts; not tested here.
* The two older refs of the same `finally` are logged, not asserted; the refs outside it
  (`sparkleSingleOutInstanceCache`, `sparkleFvarZetaVisited`, `sparkleSubModuleCache`,
  `sparkleChildCache`, `sparkleTypeCache`, the per-run expression cache) are logged or not
  looked at. A failed child leaving `kSD` in `sparkleChildCache` is predicted and not judged.
* The Meta state (metavariable context, local context) after a failed nested entry.
* Depth ≥ 2 as the STARTING depth, and a failing entry nested in a failing entry.
* What a PARENT emits after a failed nested entry: by reading no caller continues (§2), so no
  design is produced to compare; the inline `catch` path is the business of
  `LegacyCacheRollbackTest`.
* That a failing run logs no error message of its own (an `logError` besides the throw would
  fail the file's build): the sites read only throw.

## 6. For the integrator

Target: `lake build Tests.Compiler.NestedFailRestoreTest`. For AllTests:
`import Tests.Compiler.NestedFailRestoreTest`.

What may not elaborate, most likely first:

1. `sameMap` (`Std.HashMap.get?` under bare `[BEq α] [Hashable α] [BEq β]`, `{α β : Type}`);
2. `Std.HashMap.ofList seed…` as the argument of `.set` (expected type from the ref);
3. `fBadW`: the record result with `if (0 : Nat) = 0 then x else y`, and `@[hardware_module]`
   on a failing body (read as a plain tag attribute);
4. `` ``kSD `` etc. resolved in the test's namespace; `for (a, b, c, d) in …` over 4-tuples;
5. `sparkleFvarZetaVisited.set {}` / the `Std.HashSet` seed.

What may FAIL at run although it elaborates: `fBadW` not throwing (then the line
"…expected to THROW and returned"); an unexpected route for `okW`.
