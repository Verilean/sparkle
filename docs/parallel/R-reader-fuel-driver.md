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
