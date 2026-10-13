# Finding I: the legacy single-output instance hit at a nested entry — reachability and a fix PROPOSAL

Branch `fix/singleout-nested`, from poc `e6f68394`. **ISOLATED PROPOSAL.
WRITTEN, NOT BUILT**: nothing here was compiled or run by its author. The
only measured facts are the ones poc's integration recorded (§1). "READ" =
read at `e6f68394`; line numbers are `Sparkle/Compiler/Elab.lean` at that
commit unless a file is named. "PREDICTED" = expected from reading.

## 1. The finding (MEASURED on poc, `Tests/Compiler/SingleOutStaleProbe.lean`)

`sparkleSingleOutInstanceCache : String ↦ String`, key
`<module being built>#<child module>#<port=connection;…>` (6638–6641), value
the instance's output wire.

* The LEGACY handler (`Rec.handleDefinitionUnfold`, the `[singleOut]`
  branch) returns a hit as it is (6642–6644): no wire declared, no instance
  emitted, no check that the wire belongs to the builder at work. The
  certified arm validates a hit against the builder's record
  (`instHitValid`, 8588–8589).
* The map is cleared at depth 0 only (5500). A nested entry reset the other
  wire-name maps (5511–5516, findings F and G) and not this one.

Measured: the same declaration (`pTop x := hIrr x + x`, `hIrr` an untagged
`@[irreducible]` helper) compiled a second time at a PRE-SET depth 1 with
the map as the first compile left it (and the legacy memo emptied by hand):
`A: insts=1 stmts=3`, `B: insts=0 stmts=2`, `equal=F`. A CONSTRUCTED state.

## 2. Reachability by a REAL compile

A stale hit needs an entry under the SAME parent module name (the key's
first component; `ofDecl` is injective in the declaration) whose wire the
builder at work did not make — i.e. a SECOND builder of one module name
inside one outermost synthesis with the map surviving in between. Builders
start at three places only: `CircuitM.init (ofDecl declName)` at 2941
(gate harness), 2966 (mixed / machine harness), 5358 (legacy arm).

| | way to a second builder of one name | READ | verdict |
|---|---|---|---|
| 1 | the same declaration entered twice as a child (two callers, two calls, projections) | every nested entry from the translator is `Rec.synthesizeCombinational` = `childSynthEntry` = `synthesizeChild` (6287–6289, 8877–8881), and `closeInstsM` / `closeInstsGM` read the same entry (5193, 5210): a child that RETURNED is in `sparkleChildCache` and is never built again in this synthesis | NOT reachable |
| 2 | a child that THREW (nothing memoised), built again later | its exception leaves through 6542–6544 / 6554–6564 (re-thrown), `closeInstsM` has no `catch`. The only `catch`es that go on translating are the two of `tryInlineUnfold` (6313, 6329), and both `restoreWireCaches saved` (6314, 6330), which puts THIS map back to the snapshot (5651): the failed child's entries are gone before anything is retried. The other `catch`es (752, 1925, 1954, 2019, 2140, 6363, 6428, 6975–6980, 7112–7117, 7290, 7784, 7890, 8473, 9311) wrap a type inference, a constant lookup, a literal extraction or a reduction — no translation, no nested entry — or (7117) end in a plain re-translation with no rollback | NOT reachable |
| 3 | a parent that fails as inline and is then built as a module, or the reverse | the inline attempt builds in the CALLER's builder (key prefix = the caller), the module in its own; and (2) restores the map after the failed inline attempt | NOT reachable (different key prefix; restored) |
| 4 | `cfe` true and false for one declaration | no call with `certifiedFrontEnd := false` under `Sparkle/` (5549 and 7987 use the default; the others are tests) | NOT reachable |
| 5 | the certified attempt, then the legacy arm of the SAME declaration (`synthesizeFromConst`, 5270–5366) | the gate arm (5273) and the mixed arm (5280) return or throw: no fall-through. The machine arm falls through when `synthesizeMachineCertified` returns `none` (5297–5302), and then the legacy arm builds under the same name with NO reset in between. Does the machine harness write this map under the parent's name? Only the legacy `[singleOut]` branch and the certified instance arm write it. The transition the harness walks is accepted by `unifiedGateRoot` (5170), a closed syntactic fragment (2518–2629): every arm ends in `| _ => false`, an application of an unknown constant is refused, and `@[hardware_module]` calls are not in the transition at all — the machine reader turns them into binders (`machInstCall?`, 3939–3945) closed afterwards by `closeInsts*`. So the harness emits no instance and writes nothing to this map (consistent with the BUILT harness theorems: a returning harness run's module is the pure lowering of the transition, which has no instance statement) | NOT reachable BY READING. This is the one place where the argument is "the harness never gets there" and not "the map is put back". Measured check: `SINGLEOUTFIX pMach` (§5) and the existing `SINGLEOUT sMach DETECT` line of `Tests/Compiler/SingleOutHitTest.lean` |
| 6 | several tops in one command / several commands | every depth-0 entry clears the map (5500); the depth is brought back by the `finally` (5533) on every exit; the design commands call the entry once (8906, 8953, 9011, 9065) | NOT reachable |
| 7 | the same builder, a second leaf pass or a repeated call | not a second builder: equal key ⇒ same child, same argument wires, a wire this builder declared — the dedupe the map exists for (Issue #107) | sound, intended |
| 8 | the retained-parameter entry (`synthesizeCombinationalWithParameters`, 7984) | a top-level entry at depth 0; its children go through `synthesizeChild` | as 1, 6 |

**Verdict: no real compile reaches a stale hit, by reading.** No probe on
real commands shows one, because none is predicted; the regression test
carries two REAL-command rows that would show it (§5). Not excluded: a
long-lived process whose Lean state is rewound without the `IO.Ref`s — the
depth returns to 0 there too, so the next entry clears.

(The earlier reading `docs/parallel/B-cache-keys.md` §2 reached the same
bound and left row 5 "NOT ESTABLISHED"; row 5 is closed here by reading
`unifiedGateRoot`.)

## 3. The fix (smallest diff; the pattern of F and G)

`synthesizeCombinationalCoreWith`:

```diff
     else sparkleSubInstanceOutputs.get
+  let savedSingleOutInstanceCache ←
+    if depth == 0 then pure ({} : Std.HashMap String String)
+    else sparkleSingleOutInstanceCache.get
   if depth == 0 then
 …
     sparkleWireCanon.set {}
     sparkleSubInstanceOutputs.set {}
+    sparkleSingleOutInstanceCache.set {}
   sparkleSynthDepth.set (depth + 1)
 …
       sparkleSubInstanceOutputs.set savedSubInstanceOutputs
+      sparkleSingleOutInstanceCache.set savedSingleOutInstanceCache
```

(plus a comment, and one sentence in the ref's doc comment). The depth-0
block is unchanged.

### Why this and not validating the legacy hit

Validating (`instHitValid` on the legacy lookup) changes the behaviour of
the SAME builder: the legacy hit is today honoured on the key alone, and two
syntactically different expressions with the same child and the same
argument wires (a `let`-bound call met again after instantiation, Issue
#107's pattern) share one instance. With validation the second one would
miss and a second instance would be emitted — different text for designs
that have no stale hit at all. The reset / restore cannot do that (below),
is the pattern already reviewed twice, and needs no change in the handler
the legacy-semantics proofs follow.

What the reset does NOT cover: a second builder inside ONE entry (row 5).
By reading it does not occur; if `SINGLEOUTFIX pMach` ever shows it, the
place to treat it is the fall-through of `synthesizeFromConst` (a rollback
at a declined machine arm, a separate decision), not this entry.

### It never rejects a source

Three `IO.Ref` operations that cannot throw are added. The only change of
behaviour is that a lookup may MISS where it hit; a miss takes the path
every first lookup takes (declare the wire, emit the instance).

### It does not change the output where no stale hit occurs

Call an entry of the map FOREIGN to a builder when its key's first component
is that builder's module name and the wire was not made by that builder.

* A lookup in a builder of module `P` reads only keys starting with `P#`.
* With the change, a nested entry for `C` starts with the empty map. What it
  no longer sees: entries of other modules (never read by a builder of `C`),
  and entries with prefix `C#` from an EARLIER builder of `C` — foreign ones.
* When the nested entry ends, the parent's map is put back as it was at the
  call: the parent keeps every entry it made before the call; it loses the
  entries the child's builder made (prefix `C#`, or deeper), which a builder
  of `P` never reads (`C ≠ P`: a recursive call ends at the depth limit).
* Entries a builder makes after a nested call returned are written into the
  restored map and stay until that builder ends.

So for every lookup: the result differs from before only if before it hit a
foreign entry. A run without such a hit returns the same wires, the same
statements, the same names. For the rollback of `tryInlineUnfold` nothing
changes: its snapshot and restore happen inside one builder's walk, and a
nested entry in between leaves the map as it found it.

This is an argument by reading; the integrator's sampled text comparison
(§6) is the check.

## 4. Proof files that follow the entry step by step (changed on this branch)

| file | change |
|---|---|
| `Tools/ShippingChildKeeps.lean` | `fin_triple`: one more map (`m7`) and one more framed set (`.singleOut`); `core_keeps`: the `finally` text, `m7`, one more `tpure` (depth 0), one more `tget` and `tset` (nested), `body` with seven arguments |
| `Tools/ShippingMemoLaws.lean` (`outer_reset_reaches`), `Tools/ShippingMemoLawsWith.lean` (`outer_reset_reaches_with`) | one more peeled `pure` in the depth-0 prefix |

Unchanged BY READING, because they peel the prefix and the `finally` with a
repeating tactic: `Tools/ShippingEntrySoundness.lean`
(`synthesizeCombinationalCore_reads`, `iterate 40`),
`Tools/ShippingChildRun.lean` (`core_reads_inv`, `peel_inv`),
`Tools/ShippingCacheCoherentVia.lean` (`core_reads_val`, `peel_val`, the
`finally` with `iterate 10` and a framed last step),
`Tools/ShippingCacheCoherentOuter.lean` (`core_reads_val0`). The side ref is
already a `SideRef` / `MemoOther` constructor (`singleOut`), so no law and
no structure changes: `RefLaws`, `RefLawsM`, the audits and every endpoint
are untouched.

## 5. The regression test — `Tests/Compiler/SingleOutNestedFixTest.lean`

Target-only, builds on poc and on the candidate, asserts only when it
MEASURES the entry as fixed (`SINGLEOUTFIX FIXED: … fixed=<T/F>`: a seeded
map is exactly the seed again after a nested entry).

| row | poc (PREDICTED) | candidate (PREDICTED) |
|---|---|---|
| `FIXED` | `fixed=F` | `fixed=T` |
| `A` / `B` / `RESULT` (the probe turned around, a constructed state) | `1/3`, `0/2`, `equal=F` (the finding, as measured) | `1/3`, `1/3`, `equal=T` — ASSERTED |
| `pOuter` (real entry: the nested `pMid` against `pMid` alone) | `nested==alone=T` | `nested==alone=T` — ASSERTED |
| `pMach` (real entry against the clean legacy arm; row 5 of §2) | `machine shape=F`, `stale hit=F` | the same — a `stale hit=T` THROWS on either tree |

The old probe `Tests/Compiler/SingleOutStaleProbe.lean` is left as it is:
it asserts the DIFFERENCE and is the record of the finding on poc. On the
candidate it throws with "the two modules are EQUAL" — the expected outcome
there; do not put it in a build that must be green on the candidate.

Other log-only tests whose lines move with the fix (PREDICTED):
`SingleOutHitTest` §1 `sIrr … honoured` `T → F` (its seeded run is a nested
entry, which now starts from the empty map); `NestedFailRestoreTest` `OTHER`
line: `seed kept=T` as before, the size may be smaller.

## 6. What the integrator must run (separate worktree)

1. `lake build Tools.ShippingChildKeeps Tools.ShippingMemoLaws
   Tools.ShippingMemoLawsWith` — the three changed proof files — then
   `Tests.AllTests`.
2. `lake build Tests.Compiler.SingleOutNestedFixTest` on poc and on the
   candidate; keep the `SINGLEOUTFIX` lines. Then
   `Tests.Compiler.SingleOutStaleProbe` on the candidate: expected to THROW.
3. `Tests.Compiler.SingleOutHitTest`, `NestedLetCacheTest`,
   `SubInstanceKeyTest`, `NestedFailRestoreTest` on the candidate (the F / G
   assertions must still hold; the `DIGEST` lines of `NestedLetCacheTest` /
   `MemoHitCensusTest` against poc's: expected identical).
4. The simulations of the F / G integration (`nested_let_sim.sh`,
   `subinst_key_sim.sh`, `writer_sim.sh`) and the JIT / hierarchy sims
   (hierarchy changed: `sim-only-for-hierarchy` applies).
5. A sampled text comparison against poc (`compare_outputs.py` /
   the corpus measurement `status.txt` diff): expected NO difference in any
   emitted text. A difference is either a stale hit in a real design (a
   finding) or an error in §3.

## 7. NOT claimed

* That the finding is reachable by a real compile (it is not, by reading).
* That the fix is needed for any existing design, or changes any.
* Anything about row 5 beyond reading and the two logged rows.
* That the fix restores determinism of the legacy route in general: the
  legacy memo (`sparkleSubModuleCache`, 5311–5315) and `sparkleTypeCache`
  are still read at a nested entry as the world holds them
  (`docs/parallel/A-determinism.md`, items E and G).
* Any proof about the legacy handler's hit. Nothing here is built.
