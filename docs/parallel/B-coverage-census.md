# B — a coverage census of the environment: which declarations have a check-free design-level endpoint (round par/b-34)

Branch `par/b-34` from `poc/roundtrip-proof` 7d8d56b1. Worker B.

**NOTHING HERE IS BUILT OR RUN.** No `lean`, `lake` or simulator was started.
The census tool is a MEASUREMENT, not a proof; every number below is
PREDICTED by reading and is asserted nowhere.

Marks: **[R]** read at 7d8d56b1; **[M]** measured by the integrator's builds
(their records, not re-run); **[P]** PREDICTED.

## 0. Commits and files

| unit | commit | files |
|---|---|---|
| 1 | 4373c3d9 | `Tools/ShippingCombLeafClosedExpect.lean` (new); the five `Tests/Compiler/CombClosedSweep{Raw,ApplicativeA,ApplicativeB,Comb,SignOps}Test.lean` (assertions appended) |
| 2 | the commit after 4373c3d9 | `Tools/ShippingDesignCoverage.lean` (new), `Tests/Compiler/DesignCoverageTest.lean` (new, target-only) |
| 3 | the last commit | this file |

## 1. Unit 1

`#comb_closed_sweep_expect f "CLASS" ["reason"]`, the form of
`#leaf_sweep_expect` [M: built at 4103e86f]: an error when the row
`#comb_closed_sweep f` left has another class, when a GENERATED row's audit
is not `OK` / it has a NOT ALLOWED line / `f.machine_design_comb0` is absent.
Appended to the five files in `AllTests`: `"GENERATED"` for the 32 [M: 7d8d56b1].
`lakefile.lean`: `lean_lib «Tools.ShippingCombLeafClosedExpect» where roots := #[`Tools.ShippingCombLeafClosedExpect]`.
Expected log: 32 lines `COMBCLOSED EXPECT f: GENERATED, as measured`.

## 2. The census tool

`#design_coverage` (`Tools/ShippingDesignCoverage.lean`), run in
`Tests/Compiler/DesignCoverageTest.lean` (imports `Tests.AllTests`).

### 2.1 Which constants mark a declaration (suffix lists, with evidence)

The census is keyed on TWO marker suffixes — one per route — and on the
design-level prefix:

| suffix | meaning | evidence [R] |
|---|---|---|
| `f.machineData` | the machine route's reflected data: `#machine_endpoint f` ran (or `Tools.ShippingMachineCommand.generate f`) | `Tools/ShippingMachineCommand.lean` (`++ \`machineData`); every later generator starts from it (`scan`: `Tools/ShippingLeafEntryCommand.lean` 178–181, 203–205) |
| `f.gateValue` | `#gate_child f` ran: `f` is a certified-gate child | `Tools/ShippingGateChildCommand.lean` 60 (`gateValue`), with `gateDom` 61, `gateBinders` 62, `gateSort` 64–65, `gateTerm` 65, `gateBpos` 66, `gateVpos` 67, `gateVw` 68, `gate_peel` 81, `gate_old` 89, `gate_wf` 93, `gate_binders` 99 |
| `f.machine_design_…` | a design-level theorem of `f` | below |

The other artifact suffixes are NOT markers (each of them exists only where
a marker does) but are reported in an OPEN row when present: `machine_sound`,
`machine_ships`, `machine_ships_wired`, `machine_ships_comb` (2590–2664 of
`ShippingMachineCommand.lean`), `machine_closes` (`ShippingMachineClosesGen`),
`machine_closes_at` (`ShippingMachineClosesAtGen`), `closes_deep`
(`ShippingChildIfaceGen`), `machine_linked`, `machine_composed`
(`ShippingGateChildCommand.lean` 209–222 and the linked / composed commands),
`machine_ships_hier`, `machine_ships_hierR`. Further reflected-data suffixes
exist (`machineSource`, `machineSourceDecl`, `machineInits`, `machineExt`,
`machineExtB`, `machineResult`, `machineBody`, `machineSigma`, `machineRes`,
`machineInners`, `machine_src_causal`, `machine_ext_causal`); none is used.

A declaration compiled only by the LEGACY route has neither marker: it is not
in the census (it has no machine / gate artifact).

### 2.2 COVERED: decided by a re-check, not by a name list

A declaration is COVERED when SOME constant `f.machine_design_…` (not ending
in `_gap`, `_regen`, `_expected`) passes, on its stored statement:

1. every proposition binder is allowed by
   `Tools.ShippingFinalGoalCommand.allowed` [R 49–54: `RunsTo`,
   `MachineDefines`, `EntryDefines`, `ChildBnd`, conjunctions];
2. every antecedent under the leading existentials (`∃ …, P ∧ (A₁ → … → C)`)
   is allowed;
3. no checker / closing constant: `Tools.ShippingLeafDesignCommand.checkers`
   (`portsMatchB`, `kidsPass`, `designCheck`, `shipsHierCheck`, `outsCheck`,
   `kidsMaskedN`, `hierCheck` — the seven every family's audit bans) ∪
   {`MachineCloses`, `MachineClosesAt`, `ChildRanIn`}. The further constants
   only the memory route's audits ban
   (`Tools.ShippingNoPortsMemCommand.forbiddenMem`: `kidsMixed`, `kidsMem`,
   `kidsMasked`, …) are REPORTED in the row of a passing endpoint that
   mentions one, and do not fail it;
4. `Tools.ShippingDesignSV.DesignSV` occurs.

So a new closed form is counted without touching the tool, and a
`machine_design_…` constant that is not check-free (the open forms, the
forms with check premises) is listed with what failed.

The check-free forms known at 7d8d56b1 [R: `grep` of the generators and
tests] — the tool does not depend on this list:

| form | made by | declarations [M / records] |
|---|---|---|
| `machine_design_leaf0` | `#machine_leaf_design` / `#leaf_sweep` (`Tools/ShippingLeafDesignCommand.lean`) | 7 + 48 register leaves |
| `machine_design_comb0` | `#machine_comb_design0` / `#comb_closed_sweep` (`Tools/ShippingCombLeafClosedCommand.lean`) | 32 slotless leaves |
| `machine_design_svH_full_closed` | `#machine_design_svH_full` + the closing (`Tools/ShippingOneOutFullCommand.lean`) | one-output parents |
| `machine_design_noPortsNR{n}_closed` | `#machine_no_ports`, `#machine_no_ports_kids`, `#machine_no_ports_deep`, `#machine_no_ports_seq` (`ShippingNoPorts{,Kids,Deep,Slotless}Command.lean`) | group / deep / slotless parents |
| `machine_design_noPortsNR{n}_closedB` | the hand `…BTest` files | the same parents with `Bnd` discharged |
| `machine_design_noPortsR0_closed` (`…_closedB`, `…_closedN`) | `#machine_no_ports_mem`, `#machine_no_ports_memseq`, the hand memory tests, `NameDischargeTest` | memory parents |

Forms that are PREDICTED not to pass (they keep a check or a closing
premise): `machine_design_sv{n}`, `…svR{n}`, `…svNR{n}` and `…svNR{n}_closed`,
`…svH`, `…svHR`, `…svHR_closed`, `…svH_free`, `…svH_full`, `…noPortsNR{n}`
(open: `MachineClosesAt`), `…noPortsR0` (open), `…noKids…`, `…noDesign…`,
`…noOuts…`, `…noShips…`, `…comb0_open`.

### 2.3 OPEN: the reason, read at the Meta level

For an uncovered machine-route declaration the tool runs the compiler's
reader on the SOURCE declaration,
`Tools.ShippingMachineCommand.readMachine f` (what every scope scan uses),
and reads `shape.insts` (the callees BY NAME), `Sparkle.Compiler.MachMemory.
memChild?` of each, `shape.layout.slots`, `shape.instFields`,
`shape.layout.outs`; the depth is the reader applied to the callees (to
depth 6). **The reflected data `f.machineData` is never evaluated**: not by
compiled code, not by `whnf` / `reduce`. (The instruction asked for the
callee names "if obtainable at Meta level": they are, from the reader, so no
"has calls: unknown" row is expected; a reader failure gives `OPEN reader`.)

Classes: `COVERED`; `OPEN gate-route`; `OPEN memory`; `OPEN calls` (callees
with their kind — machine / gate / no artifact —, one-output or general
closing, depth); `OPEN register-leaf`; `OPEN slotless-leaf`; `OPEN reader`;
`OPEN design-only`; `ERROR` (an exception on that declaration, recorded).

### 2.4 Output, cost, robustness

    DESIGN COVERAGE START                       (also on stderr)
    DESIGN COVERAGE SCAN: <N> constants scanned; declarations with f.machineData: …; with f.gateValue: …; machine_design_… constants: …; declarations in the census: …
    COVERAGE ROW f: COVERED — by [<last components>]; other design-level constants, not check-free: […]
    COVERAGE ROW f: OPEN <class> — <reason>; design-level constants, not check-free: [<name> (<k> NOT ALLOWED of … binders + … antecedents; checker constants […]; DesignSV …)]
    DESIGN COVERAGE TOTALS of <n> declarations: [<class>: <count>, …]. Covering endpoints by form: […]. <ms> ms.

Cost model: ONE fold over all constants of the environment (`N` is logged;
per constant a comparison on the last name component) — expected well under
a second per 10⁵ constants; per `machine_design_…` constant one
`forallTelescope` and three `Expr.find?` on its statement, no
pretty-printing; per UNCOVERED machine-route declaration one reader run on it
and on its callees (the reader is what `scan` runs in every generator: tens
of milliseconds on the test declarations [M: the sweeps' 110–640 ms per
declaration include it]). Nothing is elaborated or added. Progress goes to
stderr every 25 declarations. An exception on a declaration is caught and
its row says `ERROR`; the command itself has no `throwError`.

## 3. PREDICTED totals (nothing measured)

The 125 of the integrator's count are: 38 parents (the check-free
design-level endpoints of the 2026-10-13 status log) + 7 register leaves
(`cnt`, `acc`, `pe`, `twoHW`, `toggle`, `loopPair`, `toggleL`) + 48 register
leaves of the sweep + 32 slotless leaves.

| quantity | PREDICTED | why a mismatch would be informative |
|---|---|---|
| COVERED by `machine_design_leaf0` | 55 (7 + 48) | fewer: a sweep file is not in `AllTests`; more: a leaf I did not list |
| COVERED by `machine_design_comb0` | 32 | — |
| COVERED parents (the other forms) | ≤ 38 | [R] the Keccak design tests (`OneOutWKeccakFTest`, `NoPortsKeccakSpongeTest`, `DepthSwitchSpongeTest`) and the generator-family tests (`NoPortsMemGenFamilyTest`) are NOT imported by `Tests/AllTests.lean`; the parents covered ONLY there are absent from this environment. I could not determine how many of the 38 that is (the memory parents have their hand tests in `AllTests`; `wKeccakF` / `keccak256SpongeHW` do not) |
| COVERED total | 125 minus the target-only parents: PREDICTED 120–125 | below 120: an endpoint fails the re-check (e.g. a form whose body is not `∃ …, P ∧ (A → C)`, or mentions a constant of my checker list that its own audit does not ban) — look at the "not check-free" part of its row |
| a declaration COVERED by two forms | some (a parent with `…_closed` and `…_closedB`; `mixedMems` with `…_closed` and `…_closedN`) | counted once per declaration, each form in the form totals |
| OPEN gate-route | the gate children: `pick`, `pickD`, `rcH`, `keccakRcHW` if in the environment, … (PREDICTED 3–8) | — |
| OPEN calls / memory | the parents without a closed check-free form: `mixDeep` (shared descendant), `callerBad`, parents only at `svHR` / `svNR`, `withMemory`-like memory parents without the hand test, … NOT PREDICTED as a number | this row is the worklist |
| OPEN register-leaf / slotless-leaf | PREDICTED 0 or few: every leaf with an endpoint I found was swept; a positive count names leaves the sweeps missed (e.g. helper machines endpointed inside other tests) | — |
| OPEN reader | PREDICTED 0 | a declaration whose reflected data exists but which the reader refuses now would be a finding |

The number of declarations with `f.machineData` in `AllTests`' environment:
NOT PREDICTED (roughly 150–200 by the `#machine_endpoint` lines I counted
earlier plus the programmatic ones).

## 4. For the integrator

`lakefile.lean` (not edited):

```lean
lean_lib «Tools.ShippingCombLeafClosedExpect» where
  roots := #[`Tools.ShippingCombLeafClosedExpect]

lean_lib «Tools.ShippingDesignCoverage» where
  roots := #[`Tools.ShippingDesignCoverage]
```

`Tests/AllTests.lean`: nothing to add (`DesignCoverageTest` imports it and
must stay target-only).

Build order: (1) `Tools.ShippingCombLeafClosedExpect`, `Tests.AllTests`;
(2) `Tools.ShippingDesignCoverage`; (3) the target
`Tests.Compiler.DesignCoverageTest` (it needs every olean of `AllTests`;
its own work is the scan).

To include target-only declarations (Keccak): a second census file importing
`Tests.AllTests` AND the target-only test — if the two do not generate the
same names.

Read the log:

    grep -E "DESIGN COVERAGE (START|SCAN|TOTALS)|COVERAGE ROW"
    grep "COVERAGE ROW" log | grep -v ": COVERED" | sort -t: -k3      # the worklist, by class

## 5. Risks (unbuilt)

1. `env.constants.fold` with a structure accumulator (API shape of
   `SMap.fold`); `NameSet` conversions (`toList`, `size`, `insert`).
2. the re-check's antecedent reader is my own (the built `inner` /
   `innerAntecedents` THROW on a body that is not `∃ …, P ∧ …`; mine accepts
   `A → C` too and counts) — a covered form with another body shape (e.g. a
   conjunction on the left that hides antecedents) would be counted with 0
   antecedents: it would pass if its binders are allowed and it has no
   checker constant. I know of no such form.
3. the failing checker list is the parents' seven plus the closings (the
   common denominator of the audits); the memory route's extra constants are
   only reported. A MEMORY endpoint mentioning `kidsMem` would therefore pass
   here although its own audit bans it — its own audit is in `AllTests` [M:
   green], and the row would show the mention.
4. `readMachine` on every uncovered declaration, including large IP ones:
   time not measured.
5. the `try … catch` around `liftTermElabM`, and `while (← …) do` with
   mutable counters (the pattern of the built `inner`).
6. Unit 1: as for `#leaf_sweep_expect` [M: built].

## 6. What I could not determine by reading

* How many of the 38 parents are in `AllTests`' environment (§3).
* The number of machine-route declarations in that environment.
* Whether every covered parents' form has the body shape `∃ …, P ∧ (A → C)`
  (the leaf, comb and memory forms do; `svH_full_closed` and
  `noPortsNR{n}_closed` are audited by tools that assume it).
* The run time of the census.

## Integrator's build record (2026-10-13) — MEASURED

BUILT on tree `17eab0e0ab64d5a9347152856cc6e8513d367c0b` (poc 2f9211ff + these files), cgrun 3 GiB swap 0, run `b34` (exit 0, peak 0.97 GB),
worker's files unchanged, first attempt: `Tests.AllTests` green with the 32 `COMBCLOSED EXPECT … as
measured` assertions; `Tools.ShippingDesignCoverage`; `Tests.Compiler.DesignCoverageTest` (target-only;
the census itself 1.5 s). Full log: `~/sparkle-work/coverage-census.log`.

Census of the AllTests environment: 258580 constants scanned; declarations with `f.machineData` 129, with
`f.gateValue` 3; 136 rows.
* COVERED 124 — by form (a declaration may have several): `machine_design_leaf0` 55, `machine_design_comb0`
  32, `machine_design_noPortsNR{n}_closed` 9, `…_closedB` 6, `machine_design_noPortsR0_closed` 9 (+1
  `_closedN`), `machine_design_svH_full_closed` 14. So 124 − 55 − 32 = 37 parents in this environment.
* OPEN 5 real declarations: `mixDeep` (calls: shared descendants — the cache-coherence item);
  `pickByteH` (slotless leaf, has `machine_ships_comb`, simply not swept); `rcH`, `pick`, `pickD`
  (gate route: no design-level endpoint form for a gate-route entry).
* 7 rows "design-only" are not declarations: they are the namespaces of general theorems named
  `machine_design_…` (`Tools.ShippingNoPorts` …) picked up by the third marker.

Against the reported 125 (38 parents + 7 + 48 + 32): the census finds 124 in the AllTests environment;
the difference is the parents covered only in target-only tests that AllTests does not import (the Keccak
sponge). No covered endpoint failed the re-check.
