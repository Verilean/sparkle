# Worker F (wrapper / driver), `par/r-9`: fuel `machineShape?` + doubling driver + GRID

Base poc `22908c5f`. **WRITTEN, NOT BUILT, NOT RUN.** No file under
`Sparkle/` changed; production still calls the `partial` `machineShape?`
(no switch). No `sorry`, no new axiom, no `native_decide`, no Mathlib.

## 1. `Tools/ShippingReaderFuelShape.lean` — `machineShapeF`

* One call type `WCall` (`norm e` | `blk c`) and ONE table
  `wtab senv n` (`machNormF n` / `readF n`): the wrapper's six reader calls
  (`machNorm`, `machConv` ×2, `machLoopRoot`, `machChain`, all at one fuel `n`).
  The wrapper is `shapeW : FM WCall WCall.Res (Option MachineShape)`,
  monotone by construction; `machineShapeF n … := (shapeW …).run (wtab senv n)`.
  It consumes no fuel itself.
* Three-valued: `none` = OUT, `some none` = FAIL, `some (some s)` = OK.
* Source text kept as pure fragments: `shapePre` (Elab 5061–5072),
  `shapeMid` (5075–5096), `shapePost` (5132–5185); the reader part
  (`shapeStart` 5097–5104, `shapeRootLet` 5106–5120, `shapeBody` 5122–5131) in
  the old order (`foldO` = `foldlM`, first FAIL wins).
* Lemmas: `wtab_mono`; `machineShapeF_stable` (via `readF_stable` /
  `machNormF_stable`), `machineShapeF_det`, `machineShapeF_out_le`;
  `machineShapeF_of_pre_none` (FAIL before any reader call is FAIL at every
  fuel, `0` included), `machineShapeF_zero` (otherwise fuel 0 is OUT).
* OUT propagation in the sharing searches: `findSomeO_out_cons`,
  `findSomeO_out_append` (an OUT probe after FAILED probes is OUT of the
  search — never skipped), `findSomeO_fail_all` (a FAILED search FAILED every
  probe — "not shared" is never read off an OUT), `findSomeO_fail_cons`,
  `findSomeO_hit_cons`, `nestedStep_out_of_search` (`machNested`: an OUT search
  makes the call OUT; the fresh-sub-machine branch is not taken); generic
  `FM.bind_run_out`, `bindO_run_out`, `bindO_run_ok`.

## 2. `Tools/ShippingReaderFuelDriver.lean` — the driver

* `driveLoop step rounds n k` — a **fuel-bounded total `def`** (structural on
  `rounds`), generic in the three-valued `step`; `driveShape rounds start …`
  runs it on `machineShapeF` from `max start 1` (> 0) with `doublings = 0`.
  Retries (`2 * n`) ONLY on OUT; FAIL / OK stop at once; at the bound the last
  answer is returned unchanged (OUT stays OUT). `defaultRounds = 64`.
* Why it never returns FAIL for OUT: `driveShape_res` — the answer IS
  `machineShapeF finalFuel …`; no line of the driver produces `some none`.
  `driveShape_fail_sound` (FAIL ⇒ no fuel gives OK), `driveShape_fail_stable`,
  `driveShape_ok_stable`, `driveShape_ok_sound` (OK ⇒ no fuel FAILs),
  `driveShape_out_sound` (OUT ⇒ all rounds used, every fuel ≤ final is OUT),
  `driveShape_fuel` (`finalFuel = 2^doublings * max start 1`,
  `doublings ≤ rounds`).
* Why bounded and not `partial`: theorems; `Nat` cannot overflow; OUT after
  64 doublings means the readers did not finish within depth `2^64`, where
  the real `partial` reader would not return either (modulo O1 coverage).

## 3. `Tests/Compiler/ReaderFuelGridTest.lean` — GRID (target-only)

18 cases, one `run_cmd` each, `GRID CASE START <label>` then

    GRID <label>: real=… driver=… at0=… at1=… equal=… fuel=… doublings=…

logged BEFORE the comparison; a case errors after its line iff
`equal=false`. Declarations are copies of NestTest / InstTest / LoopTest /
MemLinkedTest declarations (no import of those tests). Predictions in the
file header (12 machine cases OK/OK with OUT at fuel 0/1; `twoLoops`,
`opaqueInit` FAIL after doubling; 4 pre-refusals FAIL at every fuel with 0
doublings). `twoLoops`/`opaqueInit` classes are predictions from reading;
whatever the real reader says, the grid checks the driver says the same.

## 4. Build order, lean_lib lines

1. `lake build Tools.ShippingReaderFuelShape`
2. `lake build Tools.ShippingReaderFuelDriver`
3. `lake build Tests.Compiler.ReaderFuelGridTest` (target-only, via the `Tests` lib)

```
lean_lib «Tools.ShippingReaderFuelShape» where
  roots := #[`Tools.ShippingReaderFuelShape]

lean_lib «Tools.ShippingReaderFuelDriver» where
  roots := #[`Tools.ShippingReaderFuelDriver]
```

## 5. Risks

* Elaboration of `shapePost` / `shapePre` (verbatim `do` text moved out of
  the `match`); `WCall.Res` defeq in `wtab` / `wNorm` (same pattern as the
  BUILT `Call.Res`).
* Proof steps that rely on defeq unfolding (`show` + `rw` + `all_goals rfl`
  in `FM.bind_run_out`, `findSomeO_*`, `machineShapeF_zero`); each `findSomeO`
  lemma has a `simp` fallback under `first`.
* `nestedStep_out_of_search`: `rw [if_neg hc, bindO_run_ok hconv]` on the
  unfolded body (pattern-lambda continuation reduced by `exact`).
* `driveLoop_succ_*` by `simp only [driveLoop, h]` (equation lemma + match
  reduction).
* GRID cost: each case runs the wrapper `doublings + 1` times plus fuel 0/1;
  tiny for these declarations. Interpreted (`run_cmd`) unless the Tools
  modules are precompiled.

## Integration (integrator, 2026-10-15) — BUILT as written, grid MEASURED
Applied on poc 36d6b5ef (lakefile conflict on appended lean_libs: kept both). Run `f1` (cgrun, 3 GiB, swap 0,
`-j 1`): `Tools.ShippingReaderFuelShape`, `Tools.ShippingReaderFuelDriver`, `Tests.Compiler.ReaderFuelGridTest`
exit 0, no fix. Axioms: `findSomeO_out_append`, `findSomeO_fail_all`, `nestedStep_out_of_search`
[propext, Quot.sound]; `machineShapeF_stable`, `machineShapeF_det`, `driveShape_res`, `driveShape_fail_sound`,
`driveShape_ok_sound`, `driveShape_out_sound`, `driveShape_fuel` [propext, Classical.choice, Quot.sound].
GRID (MEASURED, 18 cases, real `machineShape?` vs the doubling driver over `machineShapeF`; equal = same class
and, on OK, the same binders / body / layout / runs / insts / loops / instFields):
* OK, OUT at fuels 0 and 1, OK after doubling: accLoop (fuel 16, 4 doublings); caller, callerInner,
  callerNested, callerTwice, counterLoop, front, latch, loopBack, memCounter, stage, twoMems (fuel 32, 5) — all
  equal.
* FAIL after OUT at small fuel (OUT → FAIL by doubling): opaqueInit (fuel 16, 4), twoLoops (fuel 32, 5) — equal.
* FAIL at once (fuel 1, no doubling): latchParams, latchSymbolic, natInductive, notHw — equal.
`READER FUEL GRID DONE: 18 cases`. Production is NOT switched (the compiler still calls the partial reader).
This grid is 18 declarations, not the corpus; it is evidence of agreement on these inputs only.

## CORRECTION (integrator, 2026-10-16, reviewer P2)
The driver header claimed that with `defaultRounds = 64` a final OUT means "the real partial reader would not
have returned either". That is WRONG: a finite execution deeper than `2^64 · start` cannot be excluded, and even
assuming O1 the conclusion does not follow. OUT means only "undecided within this trial budget";
`defaultRounds` is a test budget, not an acceptance guarantee. Header corrected (comment only; no statement
changed).

## SHADOW over a fixed list (worker I, `par/r-13`, reviewer ruling 2026-10-16) — WRITTEN, NOT BUILT
`Tests/Compiler/ReaderFuelShadowTest.lean` (target-only: `lake build Tests.Compiler.ReaderFuelShadowTest`; not
in `Tests.AllTests`). No compiler change, production NOT switched, no corpus, no environment sweep. 40 cases,
listed explicitly; START FUEL 1 (so OUT→OK and OUT→FAIL actually happen), round bound `defaultRounds`.

**Sources.** IMPORTED (no endpoint generation in these modules): `Tests.Compiler.ReaderFuelGridTest` (`G.`, BUILT;
its own grid cases are not re-run on import), `Tests.Compiler.MultiInstanceTest` (`MI.`, in AllTests),
`Tests.Compiler.Issue107LetBoundInstanceDup` (`I107.`, imported by ShippingHierOptRunTest). COPIED (their home
modules run `#machine_endpoint` / `#machine_composed*` / `#machine_ships_hier*` / `generate`, which a stale olean
would re-run): ShippingMachineSeqTest (CntOut, cnt, parent, chained, mid, grand), ShippingMachineDepthHTest (rcH,
midH, grandH), ShippingDesignSVTest (mid2, topD2, mixD1), ShippingChildBoundaryTest (mixDeep),
ShippingMachineNestTest (latch2, Pair, pair, Out, source, consumer), ShippingMachineTeleTest (PulseOut, CountOut,
detect, countOn, chain3), ShippingMachineFuseTest (innerCnt, siblings, withMemory), ShippingMachineLinkedTest
(pickByteH, counterB, callerLN), ShippingMachineInstTest (pickD, callerD), ShippingMachineLoopTest (wholeLoop,
loopPair), ShippingMachineMemLinkedTest (mixedMems). Written here: `loopCall`, `natSig`.

**The list.**

| # | label | group | declaration |
|---|---|---|---|
| 1 | counterLoop | loop | G.counterLoop |
| 2 | accLoop | loop | G.accLoop |
| 3 | wholeLoop | loop | wholeLoop (copy) |
| 4 | loopPair | loop | loopPair (copy) |
| 5 | toggle107 | loop | I107.toggle |
| 6 | latch2 | nested | latch2 (copy) |
| 7 | pair | nested | pair (copy) |
| 8 | consumer | nested | consumer (copy) |
| 9 | chain3 | nested-shared | chain3 (copy; `countOn` twice) |
| 10 | siblings | nested-shared | siblings (copy; `innerCnt` twice) |
| 11 | caller | calls | G.caller |
| 12 | callerNested | calls | G.callerNested |
| 13 | callerInner | calls | G.callerInner |
| 14 | callerD | calls | callerD (copy) |
| 15 | callerLN | calls | callerLN (copy) |
| 16 | threeInstances | calls | I107.threeInstances |
| 17 | parent | instS | parent (copy) |
| 18 | chained | instS | chained (copy) |
| 19 | grand | instS-callers | grand (copy) |
| 20 | grandH | instS-callers | grandH (copy) |
| 21 | topD2 | instS-callers | topD2 (copy) |
| 22 | mixD1 | instS-callers | mixD1 (copy) |
| 23 | mixDeep | instS-callers | mixDeep (copy) |
| 24 | twinCalls | instS | MI.twinCalls |
| 25 | mesh2x2 | instS | MI.mesh2x2 |
| 26 | cnt | multi-output | cnt (copy) |
| 27 | mid2 | multi-output | mid2 (copy) |
| 28 | pe | multi-output | MI.pe |
| 29 | source | multi-output | source (copy) |
| 30 | memCounter | memory | G.memCounter |
| 31 | twoMems | memory | G.twoMems |
| 32 | mixedMems | memory | mixedMems (copy; comb + sync read) |
| 33 | withMemory | memory | withMemory (copy; dead memory, inner loop) |
| 34 | twoLoops | refusal | G.twoLoops |
| 35 | opaqueInit | refusal | G.opaqueInit |
| 36 | loopCall | refusal | loopCall (here; loop alone calling `pick`) |
| 37 | notHw | refusal | G.notHw |
| 38 | natSig | refusal | natSig (here; `Signal Nat` binder) |
| 39 | gridInit | refusal | G.gridInit (an `opaque`) |
| 40 | latchSymbolic | refusal | G.latch in symbolic mode |

**Lines.** Per case two commands: `SHADOW CASE START <label>` (its own command, also written to stderr and
flushed, so it is reported before the work starts), then the work on a dedicated task under a wall-clock guard
(`caseBudgetMs = 60000`, a polling sleeper task; `IO.waitAny`) and ONE line, logged before the verdict is acted on:

    SHADOW <label> [<group>]: real=<OK|FAIL> driver=<OK|FAIL|OUT> path=<OK@1|FAIL@1|OUT→OK|OUT→FAIL|OUT(budget)> fields=<all-equal|differ:…|n/a> equal=<bool> doublings=<k> fuel=<n> realMs=<t> driverMs=<t>

`fields` compares EVERY field of both `MachineShape`s by `BEq` (binders, body, layout.slots, layout.outs,
layout.resetKind, layout.lets, runs, insts, loops, instFields) and names each differing one. A case errors after
its line iff `equal=false`. If the work does not return within the guard: `SHADOW <label> [<group>]: TIMEOUT after
60000 ms …` as a WARNING — a separate class, never OUT. A hang the guard cannot catch is a START with no result
line (the integrator's cgrun timeout is the backstop). Peak memory: the integrator's cgrun.

**PREDICTED (by reading; NOT observed).**
* rows 1–33: `real=OK driver=OK path=OUT→OK fields=all-equal equal=true`, doublings 4–6, fuel 16–64 (grid:
  4–5 / 16–32; the deeper `mixDeep`, `topD2`, `chain3`, `siblings`, `withMemory`, `mesh2x2` may need one more).
  Lowest confidence in the OK CLASS of `mesh2x2`, `twinCalls` (slotless parents of structure children) and
  `pair`, `source` (structure results without an enclosing machine / with an unascribed constructor); whatever
  the class, the prediction is `equal=true`.
* rows 34–36 (`twoLoops`, `opaqueInit`, `loopCall`): `real=FAIL driver=FAIL path=OUT→FAIL fields=n/a equal=true`.
* rows 37–40 (`notHw`, `natSig`, `gridInit`, `latchSymbolic`): `real=FAIL driver=FAIL path=FAIL@1 fields=n/a
  equal=true doublings=0 fuel=1` (`machineShapeF_of_pre_none`).
* no TIMEOUT; realMs / driverMs ≤ 100 each; `READER FUEL SHADOW DONE: 40 cases`.

**Risks.** (1) A TIMEOUT task cannot be cancelled (pure code): it keeps a dedicated thread and CPU, and process
exit may wait for it — the cgrun timeout then ends the run AFTER all lines are printed. (2) Elaboration of the
copies (opens differ slightly from their home modules: name resolution prefers this namespace). (3) `IO.waitAny`'s
default length proof on the literal list. (4) Importing `MultiInstanceTest` / `Issue107…` builds them if stale
(cheap: synthesis asserts only). (5) Timing: the answer is forced by branching on an unfoldable key
(`shapeKey`: the body's hash) before the second clock read; interpreted run (`run_cmd`), so absolute ms include
interpreter overhead for the harness only (the readers are compiled Sparkle code if precompiled, else interpreted).

## Shadow (worker I, 7399c6d5) — MEASURED, built as written
Applied on poc fe65d4c5. Run `i1` (cgrun, 3 GiB, swap 0, `-j 1`, peak 0.35 GB):
`Tests.Compiler.ReaderFuelShadowTest` exit 0. `READER FUEL SHADOW DONE: 40 cases`, start fuel 1, round bound 64,
guard 60000 ms per case. Result: 40 / 40 `equal=true` with ALL shape fields equal on every OK case; no TIMEOUT.
* OUT→OK (33): loops (accLoop, counterLoop, wholeLoop, loopPair, toggle107), nested / shared (latch2, pair,
  consumer, chain3, siblings), calls (caller, callerNested, callerInner, callerD, callerLN, threeInstances —
  6 doublings, fuel 64), instS / instS callers (parent, chained, grand, grandH, topD2, mixD1, mixDeep, twinCalls,
  mesh2x2), multi-output (cnt, mid2, pe, source), memory (memCounter, twoMems, mixedMems, withMemory);
  4–6 doublings, final fuel 16–64; real ≤ 2 ms, driver ≤ 10 ms per case.
* OUT→FAIL (3): twoLoops, opaqueInit, loopCall.
* FAIL at fuel 1 (4): notHw, natSig, gridInit, latchSymbolic.
Scope: these 40 declarations (fixed list), not the corpus; evidence of agreement on them only.
