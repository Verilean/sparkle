# `mixDeep` at outermost starts: a second endpoint, and the split that makes it possible

Round par/g-1, branch `par/g-1`, base poc `f1ed620f`. **WRITTEN, NOT BUILT**: nothing here was
compiled or run by its author; every "the script asserts" below is a Python check on text, not a
Lean check. Implements item 1 of the reviewer's ruling of 2026-10-14.

**What stays open, first.** This round does NOT close `mixDeep`. The built endpoint
`mixDeep.machine_design_noPortsNR2` still asks `MachineClosesAt mixDeep` (the machine synthesis
returns from EVERY invariant world of positive depth), that premise is still not derived for
callees sharing a descendant, and the census still counts 134 declarations / 133 covered with
`mixDeep` open. What is added is a SECOND endpoint, `mixDeep.machine_design_noPortsNR2_outermost`,
which holds only from depth-0 starts (`Start0`). At NESTED starts — a start world of positive
depth with an invariant cache, which `ChildBnd` also allows — nothing is proved. `Start0` is not
an ALLOWED premise of the goal's classifier and was not made one; the new endpoint is tallied in
its own table. No `RefLawsX` / `ChildBndX` is introduced.

## 0. Result, plainly

| | state |
|---|---|
| the split of the base lemmas | WRITTEN: 12 lemmas that USE the closing split in place (10 built files), statements unchanged; one threading theorem split in place; `MachineRan` moved to an early file |
| the threading theorems over `MachineRan` | WRITTEN as siblings in two NEW files (17 theorems) |
| `mixDeep.machine_design_noPortsNR2_outermost` | WRITTEN (generated in a target-only asserting test by three new term builders); its statement is known only up to what the builders compute — see §4 |
| the separate tally | WRITTEN: `#outermost_coverage` |
| depth 0 at a public entry | argued by READING for one thread of control; ONE FINDING (the depth ref is a cell of the process, and by reading of the toolchain two elaborations of one process can overlap in the language server) with a logging probe — §5 |
| of the thirteen lemmas of `A-outermost-form.md` | 9 split; 4 NOT split (not on the endpoint's path) — §2.3 |
| base lemmas the list of thirteen MISSED | 3, all on the endpoint's path, all split — §1 |

## 1. The inventory: where the closing is USED and where it is only passed on

Read in full (every proof line): the thirteen base lemmas of `A-outermost-form.md` and every
theorem between them and `kids_*`; the wired endpoint's chain
(`Tools/ShippingMachineTraceX.lean`, `Tools/ShippingMachineSeqLinkedR.lean`); the generators that
make `mixDeep`'s `soundL` and `composed` (`Tools/ShippingMachineDepthCommandR.lean` 538–994,
`Tools/ShippingMachineSeqCommand.lean` 71–91); the head and its callers.

**Three corrections to `A-outermost-form.md` §1.**

1. Its list of thirteen is the list of base lemmas under `kids_*` AND under the kids' own facts
   (`GenKid.facts`, `factsN`). Four of them — `kidsDesign_real`, `core_hierGate_any`,
   `core_calls_ports₁`, `core_calls_portsG` — are reached only through the KID's facts, where the
   closing passed is the kid's (`mid2.closes_deep`, …: a theorem, all worlds). `mixDeep`'s own
   closing never reaches them. They are not needed for the endpoint.
2. Two base lemmas that `mixDeep`'s closing DOES reach are missing from it:
   `Tools.ShippingLinkedFresh.core_linkedWF` (under `core_runFacts` and `core_outsExtracted`) and
   `Tools.ShippingPortsMatchRaw.core_callConns` (under `kids_maskedN` and `kids_designCheck`).
3. "Where `soundL` / `composed` use the closing" (not traced there): both reach exactly one
   more base lemma, `Tools.ShippingMachineTraceX.synthesizeCombinationalCore_machine_soundRA`
   (line 490), through `machine_trace_lets_of_streamBRA` (625) and the wired head
   `machine_traceL_of_{loop_causal,comb_calls,data_causal}RA`. `soundL` is that head applied
   (`generateShipsNR`, `soundA`, lines 975–984); `composed` is the GENERATED theorem
   `mixDeep.machine_composedNR2`, whose proof term is `machine_linkedT_callsRN n h …` with
   `h := <head>RA args … hr entry closes hsyn` (`generateCoreNR`, lines 548, 569, 702) — by
   reading, the only place its closing binder is used.

So the endpoint's path has **12 lemmas that use the closing** and **19 theorems that thread it**,
with **39 call sites** that pass it on (table), plus the generated sites: `soundA` and `h`
(above), the four per-declaration theorems of `Tests/Compiler/NoPortsMixDeepTest.lean`
(`mixDeep_runFacts` 286–296, `mixDeep_outsG2` 325–333, `mixDeep_maskedG` 359–368,
`mixDeep_designP2` 396–408) and the four applications in
`Tests.Compiler.NoPortsTopD2Test.generateX` (528, 536, 544, 552).

Every one of the 12 uses is the same lines: `obtain … := machine_run_of_core hcore entry hB`,
`have hne := closes bb _ _ _ hw9 hd9 hrun9`, `cases r`, `subst`. After them — read line by line
in all twelve — the TAIL never mentions `closes`, `hcore`, `entry` or `hB` except to pass all
four to another theorem of this list (`hpost` is used).

| file (at `f1ed620f`) | line | theorem | the closing | proof lines | calls that pass the closing on (line: callee) |
|---|---|---|---|---|---|
| `Tools/ShippingChecksCore.lean` | 72 | `core_kids_facts` | USED at line 97 | 130 | — |
| `Tools/ShippingChecksCore.lean` | 449 | `core_kids_factsM` | USED at line 474 | 132 | — |
| `Tools/ShippingChecksCoreGate.lean` | 41 | `core_outsCheck_all_gate` | threaded only | 23 | 69: `core_kids_facts` |
| `Tools/ShippingChecksWidths.lean` | 111 | `core_hierGateM` | USED at line 134 | 33 | 130: `core_kids_factsM` |
| `Tools/ShippingChecksWidths.lean` | 168 | `core_callPortsM` | USED at line 218 | 134 | 198: `core_kids_factsM` |
| `Tools/ShippingChecksWidths.lean` | 357 | `core_callPorts` | threaded only | 9 | 388: `core_callPortsM` |
| `Tools/ShippingChecksWidths.lean` | 401 | `core_instOutWidthsOk` | threaded only | 18 | 430: `core_callPorts` |
| `Tools/ShippingChecksWidths.lean` | 495 | `core_hierGate` | threaded only | 2 | 514: `core_hierGateM` |
| `Tools/ShippingLinkedFresh.lean` | 162 | `core_linkedWF` | USED at line 182 | 60 | 236: `core_kids_facts` |
| `Tools/ShippingLinkedFresh.lean` | 243 | `core_instOuts_not_assigned` | threaded only | 2 | 263: `core_linkedWF` |
| `Tools/ShippingChecksRaw.lean` | 155 | `core_raw_factsM` | USED at line 178 | 87 | 235: `core_kids_factsM` |
| `Tools/ShippingChecksRaw.lean` | 289 | `core_raw_facts` | threaded only | 2 | 311: `core_raw_factsM` |
| `Tools/ShippingChecksOuts.lean` | 86 | `core_outsExtracted` | USED at line 132 | 143 | 111: `core_kids_facts`, 113: `core_instOuts_not_assigned` |
| `Tools/ShippingChecksRunFacts.lean` | 42 | `core_runFacts` | threaded only | 15 | 72: `core_raw_facts`, 75: `core_hierGate`, 77: `core_linkedWF`, 81: `core_outsExtracted`, 84: `core_instOutWidthsOk` |
| `Tools/ShippingPortsMatchRaw.lean` | 247 | `core_callConns` | USED at line 304 | 155 | 284: `core_kids_facts` |
| `Tools/ShippingPortsMatchRaw.lean` | 441 | `core_portsMatch_raw` | threaded only | 56 | 485: `core_closed_typedIn`, 487: `core_callConns` |
| `Tools/ShippingKidsSelf.lean` | 78 | `core_kids_self` | USED at line 98 | 42 | — |
| `Tools/ShippingKidsSelf.lean` | 144 | `core_kidsPass_deep` | threaded only | 27 | 174: `core_kids_facts`, 176: `core_kids_self`, 178: `core_hierGate` |
| `Tools/ShippingKidsSelf.lean` | 206 | `core_kidsMaskedN_top` | threaded only | 7 | 228: `core_callConns` |
| `Tools/ShippingCoreClk.lean` | 57 | `core_clk` | USED at line 89 | 98 | — |
| `Tools/ShippingClosedTyped.lean` | 95 | `core_closed_typedIn` | USED at line 134 | 215 | 117: `core_kids_facts` |
| `Tools/ShippingTextShipped.lean` | 131 | `core_designCheck_run` | threaded only | 6 | 168: `core_runFacts`, 170: `core_closed_typedIn` |
| `Tools/ShippingKidFacts.lean` | 106 | `kids_runFacts` | threaded only | 5 | 130: `core_runFacts` |
| `Tools/ShippingKidFacts.lean` | 138 | `kids_outsCheck` | threaded only | 5 | 160: `core_outsCheck_all_gate` |
| `Tools/ShippingKidFacts.lean` | 168 | `kids_maskedN` | threaded only | 3 | 190: `core_kidsMaskedN_top` |
| `Tools/ShippingKidFacts.lean` | 199 | `kids_designCheck` | threaded only | 26 | 229: `core_portsMatch_raw`, 236: `core_clk`, 241: `core_hierGate`, 244: `core_kidsPass_deep`, 248: `core_designCheck_run` |
| `Tools/ShippingMachineTraceX.lean` | 467 | `synthesizeCombinationalCore_machine_soundRA` | USED at line 490 | 64 | — |
| `Tools/ShippingMachineTraceX.lean` | 562 | `machine_trace_lets_of_streamBRA` | threaded only | 104 | 625: `synthesizeCombinationalCore_machine_soundRA` |
| `Tools/ShippingMachineSeqLinkedR.lean` | 25 | `machine_traceL_of_loop_causalRA` | threaded only | 25 | 89: `machine_trace_lets_of_streamBRA` |
| `Tools/ShippingMachineSeqLinkedR.lean` | 117 | `machine_traceL_of_comb_callsRA` | threaded only | 7 | 157: `machine_trace_lets_of_streamBRA` |
| `Tools/ShippingMachineSeqLinkedR.lean` | 167 | `machine_traceL_of_data_causalRA` | threaded only | 28 | 232: `machine_trace_lets_of_streamBRA` |

(Generated by script from `git show f1ed620f:<file>`.) There are 45 applications of
`machine_run_of_core` in `Tools/` in all; the other 33 are in files this endpoint does not reach (the memory route, the
leaf route, the one-output route, the slotless route, the kids' facts) and are not touched.

## 2. The split

### 2.1 Its form: ONE consumer statement, two producers

    def MachineRan mctx mref cctx cref c shape M D : Prop :=            -- BUILT (par/a-43), moved
      ∃ b w9 w10, RunsTo (synthesizeMachineCertified … (profLogIO b) c shape) mctx mref cctx cref
                    w9 (some (M, D)) w10 ∧ InvW mref cref w9 ∧ DepthPos mref cref w9

A base lemma `X` with statement `S` and proof `PRE ; (the eight lines) ; TAIL` becomes

    theorem X_ran  <S without {w w1}, hB, hcore, entry; closes ↦ (ran : MachineRan mctx mref cctx cref c d.shape M D)> := by
      PRE'
      have ran0 := ran
      obtain ⟨bb, w9, w10, hrun9, hw9, -⟩ := ran0
      TAIL'
    theorem X  <S, character for character> :=
      X_ran <the explicit binders of S in order, without hB hcore entry>
        (Tools.ShippingMachineRan.machineRan_of_closes hcore entry hB closes)

`PRE'` / `TAIL'`: every call `Y … hB hcore hpost entry closes …` of a theorem of the table
replaced by `Y_ran … hpost ran …`.

**Which of `hcore` / `entry` / `hB` a tail really needs: NONE, in all twelve.** The script
asserts, per `_ran` proof (comments removed), that the identifiers `closes`, `hcore`, `entry`,
`hB`, `hd9` do not occur, and that the number of rewritten call sites equals the number of
renamed callees. So the `_ran` forms take `ran` (and `hpost` where the statement has it) and
nothing else of the run; `{w w1 : Void IO.RealWorld}` goes with them. `ran0` exists because
`obtain` clears its argument and some tails pass `ran` on.

The two producers of `MachineRan` are BUILT: `machineRan_of_closes` (all-worlds closing) and
`machineRan_outermost` (`Start0` + a closing at `Prov` worlds). A `_ran` lemma does not know
which one it was given.

### 2.2 Imports (every change)

`Tools/ShippingMachineRan.lean` imports `Tools.ShippingKidsSelf`, so the base lemmas cannot
import it. Resolved by a move:

* NEW `Tools/ShippingMachineRanBase.lean` (`import Tools.ShippingChildRun` only): `MachineRan`
  and `machineRan_of_closes`, under their old full names (`namespace Tools.ShippingMachineRan`),
  texts verbatim.
* `Tools/ShippingMachineRan.lean`: `+ import Tools.ShippingMachineRanBase`; the two declarations
  removed; everything else it declares keeps its name and statement.
* `+ import Tools.ShippingMachineRanBase` in each of: `ShippingChecksCore`, `ShippingLinkedFresh`,
  `ShippingChecksRaw`, `ShippingClosedTyped`, `ShippingChecksOuts`, `ShippingChecksWidths`,
  `ShippingPortsMatchRaw`, `ShippingCoreClk`, `ShippingKidsSelf`, `ShippingMachineTraceX`.
  (Seven of these would get it transitively; each has it explicitly so that a file's commit
  names its own dependency.)

No cycle: the transitive imports of `Tools.ShippingMachineRanBase` (computed by script over the
`import` lines) contain none of the edited files and not `Tools.ShippingMachineRan`.

### 2.3 Per file (one commit each; `git diff --numstat f1ed620f`)

| built file | +/− | what |
|---|---|---|
| `Tools/ShippingMachineRan.lean` (2 commits) | +19 −69 | move out of `MachineRan`, `machineRan_of_closes`; `core_kids_self_ran` re-proved by ONE application of `Tools.ShippingKidsSelf.core_kids_self_ran` (it was a copy of that tail: the copy is gone) |
| `Tools/ShippingChecksCore.lean` | +77 −32 | `core_kids_facts`, `core_kids_factsM` split |
| `Tools/ShippingLinkedFresh.lean` | +59 −19 | `core_linkedWF` split; NEW sibling `core_instOuts_not_assigned_ran` (2-line proof; needed by `core_outsExtracted_ran`, hence in this file); `core_instOuts_not_assigned` untouched |
| `Tools/ShippingChecksRaw.lean` | +39 −19 | `core_raw_factsM` split |
| `Tools/ShippingClosedTyped.lean` | +39 −18 | `core_closed_typedIn` split |
| `Tools/ShippingChecksOuts.lean` | +44 −22 | `core_outsExtracted` split |
| `Tools/ShippingChecksWidths.lean` | +82 −38 | `core_hierGateM`, `core_callPortsM` split |
| `Tools/ShippingPortsMatchRaw.lean` | +55 −20 | `core_callConns` split |
| `Tools/ShippingCoreClk.lean` | +35 −16 | `core_clk` split |
| `Tools/ShippingKidsSelf.lean` | +34 −16 | `core_kids_self` split |
| `Tools/ShippingMachineTraceX.lean` | +150 −81 | `synthesizeCombinationalCore_machine_soundRA` split (its tail is indented under `\| some res =>` there: dedented by two columns, otherwise verbatim); `machine_trace_lets_of_streamBRA` split IN PLACE although it only threads (its proof is 104 lines; a sibling would have copied them) |

The added lines are almost all the re-stated OLD statement (the corollary) — the proof text moved,
it was not copied. In every split file the old theorem's statement is the base commit's,
character for character: `docs/parallel/G-ran-split-statements.md` has, for each of 20 theorems,
the statement at `f1ed620f`, the comparison with the working tree (script: `IDENTICAL` for all
20, with the SHA-256 of both texts) and the `_ran` statement.

**The thirteen of `A-outermost-form.md`:**

| lemma | status |
|---|---|
| `core_kids_facts`, `core_kids_factsM`, `core_raw_factsM`, `core_hierGateM`, `core_callPortsM`, `core_closed_typedIn`, `core_outsExtracted`, `core_clk`, `core_kids_self` | SPLIT |
| `kidsDesign_real` (`ShippingChecksRun2` 73), `core_hierGate_any` (`ShippingHierGateAny` 74), `core_calls_ports₁` (`ShippingCallsChildPorts` 192), `core_calls_portsG` (`ShippingCallsPortsG` 107) | NOT split, files not edited: `mixDeep`'s closing does not reach them (§1, correction 1). Splitting them would be four more built files edited for nothing this endpoint uses. Their statements are pinned all the same |

### 2.4 The threading theorems (NEW files; no built file edited for them)

* `Tools/ShippingKidFactsRan.lean` (841 lines, of which statements ≈ 430): `_ran` siblings of
  `core_outsCheck_all_gate`, `core_hierGate`, `core_callPorts`, `core_instOutWidthsOk`,
  `core_raw_facts`, `core_runFacts`, `core_portsMatch_raw`, `core_kidsMaskedN_top`,
  `core_kidsPass_deep`, `core_designCheck_run`, `kids_runFacts`, `kids_outsCheck`,
  `kids_maskedN`, `kids_designCheck` — each in its original's namespace (re-entered with the
  original's `open` list), statement and proof copied by the same script (`closes ↦ ran`,
  callees `↦ _ran`). About 200 proof lines are duplicated; they do not follow their originals.
* `Tools/ShippingMachineSeqLinkedRan.lean` (273 lines): the three wired heads with
  `hr entry closes hsyn ↦ ran`; leading binders unchanged, so a generator applies
  `<head>RA_ran` to the arguments of `f.machine_sound` exactly as the built ones apply
  `<head>RA`. 61 proof lines duplicated.

The alternative for these (split in place, old = corollary, nothing duplicated) would edit four
more built files (`ShippingChecksCoreGate`, `ShippingChecksRunFacts`, `ShippingTextShipped`,
`ShippingKidFacts`, `ShippingMachineSeqLinkedR`: five) and more theorems in the ten already
edited. Not done: the instruction was "new files where possible". It is a mechanical follow-up
if the duplication is judged worse than the edits.

### 2.5 The pin test — `Tests/Compiler/RanSplitStatementsTest.lean`

Target-only, asserting. For 20 theorems (the thirteen, the three further base lemmas,
`machine_trace_lets_of_streamBRA`, and the three of `Tools/ShippingMachineRan.lean`):

1. `example : <the statement at f1ed620f, as a ∀> := @<full name>` — type up to definitional
   equality (binder order and types);
2. a `run_cmd` comparing the present constant's leading binders' NAMES and KINDS with the list
   parsed from the old text (what 1. does not see);
3. the 31 `_ran` forms exist, are on the standard axioms, mention `MachineRan` and neither
   `MachineClosesAt` nor `MachineCloses`.

## 3. `RanAt`, and why the head needs no sibling

`Tools.ShippingNoPorts.machine_design_noPorts` is parametric in `C` and in the boundary
`Bnd : CtxBnd` (contexts, start world, CORE module and design), and gives each of its hypotheses
`Bnd mctx mref cctx cref w raw D` together with a core run from `w` returning `(raw, D)`. So
the machine synthesis of the run can ride in the boundary (`Tools/ShippingOutermost.lean`):

    def RanAt mctx mref cctx cref c shape w M D : Prop :=
      ∀ w1, RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1 →
        MachineRan mctx mref cctx cref c shape M D
    theorem RanAt.ran        (h : RanAt … w M D) (hcore : RunsTo … w (M, D) w1) : MachineRan … M D
    theorem ranAt_of_closes  (entry) (hB : ChildBnd mref cref w) (closes : MachineClosesAt …) (M D) : RanAt … w M D
    theorem ranAt_outermost  (entry) (h0 : Start0 mref cref w) (hclose : <closing at Prov worlds>) (M D) : RanAt … w M D

`RanAt` quantifies over every result of a core run from `w`, so it is provable WITHOUT the
witnesses the head's conclusion hides (`∃ raw D, …`) — which is what stopped the plain-term
application of a `MachineRan` premise. The outermost form is the same head at
`C := fun _ _ _ _ => True`, `Bnd := Bnd₀ ∧ RanAt`.

## 4. The endpoint — `Tests/Compiler/MixDeepOutermostEndpointTest.lean`

Built by `Tools/ShippingOutermostCommand.lean` (three MetaM term builders, kernel-checked by
`addTheorem`; nothing is run on import):

1. four source theorems `mixDeep_runFacts_ran`, `_outsG2_ran`, `_maskedG_ran`, `_designP2_ran`
   (`kids_*_ran` at `mixDeep`'s data; first explicit arguments `hpost ran`);
2. `composedOfTrace mixDeep 2`: takes the stored proof term of `mixDeep.machine_composedNR2`,
   replaces its application of the wired head (`<head>RA args … closes hsyn`) by a hypothesis
   `hT`, CHECKS that the closing binder no longer occurs, adds
   `mixDeep.machine_composedNR2_ofTrace`. It throws otherwise (the reading of `generateCoreNR`
   would then be wrong);
3. `openTerm`: `mixDeep.outermost_open_noPortsNR2` — the head at `C := True`, `Bnd₀ ∧ RanAt`;
4. `mixDeep_ranAt_outermost` (source): `ranAt_outermost` with the BUILT `mixDeep_closes_prov`;
5. `closeOutermost`: the boundary `Bnd₀` derived from the reflections and `Start0.childBnd` by
   the BUILT `Tools.ShippingBoundaryClose.solve`; throws, with one line per conjunct, if a
   conjunct is not derived.

Statement (as the builders make it; binder names of the first ten are those of
`mixDeep.machine_ships_hierNR2`, which I did not read off a build):

    theorem mixDeep.machine_design_noPortsNR2_outermost
        {mctx} {mref} {cctx} {cref} {w w' : Void IO.RealWorld} {b : Module} {design : Design}
        (hr    : RunsTo (synthesizeCombinational ``mixDeep) mctx mref cctx cref w (b, design) w')
        (entry : MachineDefines mctx mref cctx cref ``mixDeep mixDeep.machineData.shape)
        (hR2   : MachineDefines mctx mref cctx cref ``mid2 mid2.machineData.shape)
        (hRm   : MachineDefines mctx mref cctx cref ``midH midH.machineData.shape)
        (hRr   : EntryDefines  mctx mref cctx cref ``rcH rcH.gateValue)
        (hRc   : MachineDefines mctx mref cctx cref ``cnt cnt.machineData.shape)
        (h0    : Tools.ShippingMachineRan.Start0 mref cref w) :
        ∃ raw D, (b = dropZeroWidthModule raw ∨ b = mergeChecked (dropZeroWidthModule raw)) ∧
          <the conclusion of mixDeep.machine_design_noPortsNR2 after its boundary antecedent:
           ∃ ids, … DesignSV (childMap D.modules) 2 (checkedOptimize b) (seedIn b ins) T ⟨st0, mems, kids⟩ … >

No antecedent is left under the existentials: `Start0` gives `ChildBnd`
(`Start0.childBnd`), the reflections give the rest of the built boundary.

The test ASSERTS: standard axioms; no checker constant, `MachineClosesAt`, `MachineCloses`,
`ChildRanIn`, `RanAt`, `MachineRan` in the statement; `DesignSV` in it; exactly 7 proposition
binders in the order above; the conclusion `isDefEq` the built endpoint's after the boundary, at
the same binders; no antecedent under the existentials; the classifier's label of EVERY premise
logged (`NOPORTS PREMISE …` lines) with exactly ONE `NOT ALLOWED`, and it is `Start0` (the
classifier is not changed); the census's own re-check FAILS on it; the outermost re-check
passes; and — the built endpoint unchanged — `mixDeep.machine_design_noPortsNR2` present, with
`MachineClosesAt mixDeep` still among its binders and no `_closed` form. The log line reads
"OUTERMOST SCOPE — not counted in the census population". `#print axioms` on the endpoint and
three of its ingredients.

## 4.1 The separate tally — `Tools/ShippingOutermostCoverage.lean`

`#outermost_coverage` lists every constant whose last component is a design-level name of the
census (`isDesign`) AND ends with `_outermost`. A row is `OUTERMOST START` when exactly one
proposition binder is `Start0`, every other binder and every antecedent is ALLOWED, no checker /
closing constant occurs and `DesignSV` does. Its totals line says the population is separate and
is not part of `#design_coverage`'s COVERED count.

`Tools/ShippingDesignCoverage.lean` is NOT edited. Its marker rules, read (lines 112–133,
164–187, 258–273): a constant `p.s` is a design constant when `s` starts with
`machine_design_` (or is `gate_design0[S]`) and does not end with `_gap` / `_regen` /
`_expected`. So:

* `mixDeep.machine_design_noPortsNR2_outermost` WOULD be picked up as a design constant of
  `mixDeep` in any environment that contains it. Its re-check then counts the `Start0` binder
  NOT ALLOWED (`bad = 1`, `ok = false`): `mixDeep` stays `OPEN calls`, with the constant listed
  among "design-level constants, not check-free". **It is not counted COVERED.** (By reading;
  the test asserts `recheck … .ok = false`, and `#outermost_coverage` prints, for each row, what
  the census's re-check says and flags a pass in capitals as a defect.)
* a constant under a test namespace (a prefix that is not itself a constant) gets no row in the
  census (lines 270–273); the endpoint is deliberately NOT placed there.
* the test is target-only, so the `Tests.AllTests` environment the 134 / 133 census runs in does
  not contain the constant at all: the census is unchanged either way.
* `mixDeep.machine_composedNR2_ofTrace` and `mixDeep.outermost_open_noPortsNR2` do not start
  with `machine_design_`: not design constants.

## 5. "A public entry starts at depth 0": the grounds, and what they do not cover

All of this is BY READING unless marked. Line numbers: `Sparkle/Compiler/Elab.lean` at
`f1ed620f`.

**Created.** `initialize sparkleSynthDepth : IO.Ref Nat ← IO.mkRef 0` (961). One `IO.Ref`,
made when the module's initializer runs: once per PROCESS, value 0.

**Every write** (`grep` over `Sparkle/`: three occurrences besides the declaration, all in
`synthesizeCombinationalCoreWith`):

| line | code | when |
|---|---|---|
| 5431 | `let depth ← sparkleSynthDepth.get` | entry |
| 5432–5433 | `if depth ≥ sparkleSynthDepthLimit then throwError …` | BEFORE any write: nothing to undo |
| 5446–5516 | reads / writes of OTHER refs (caches) | `ST.Ref` operations only: no `throwError`, no Meta call, so no exception between 5433 and 5517 |
| 5517 | `sparkleSynthDepth.set (depth + 1)` | the only increment |
| 5522–5529 | `let doSynth : MetaM … := do …` | a definition, runs nothing |
| 5530–5533 | `try doSynth finally sparkleSynthDepth.modify (· - 1)` | the only decrement; the `finally` of `MetaM` runs for every exception of the monad (errors, heartbeat and recursion-depth exceptions, the interrupt exception) |

So on ONE thread of control each entry leaves the depth as it found it, whether it returns or
throws; between the increment (5517) and the `try` (5530) nothing can throw. (The proofs model
exactly this: `Tools/ShippingChildKeeps.lean` 257–266, 344, 414.)

**The commands call the entry directly.** `synthesizeCombinational :=
synthesizeCombinationalWith …` (8869) → `synthesizeCombinationalCoreWith` (5549). Each public
command resolves the name and runs, inside `Lean.Elab.Command.liftTermElabM`, either
`synthesizeCombinational` — `#synthesize` (8906), `#synthesizeVerilog` (8953), `#showVerilog`
(9011) — or `synthesizeHierarchical` (9064–9067: one call of `synthesizeCombinational`, then
pure post-processing) — `#synthesizeDesign` (9073), `#synthesizeVerilogDesign` (9082),
`#writeVerilogDesign` (9092), `#writeCppSimDesign` (9105), `#writeCudaDesign` (9154),
`#writeCudaIntraDesign` (9206), `#writeDesign` (via `writeDesignCore`, 9229), `#sim` (9300).
The parameterised forms call `synthesizeCombinationalWithParameters` (8989, 9060), which is
`synthesizeCombinationalCoreWith … declName parameters true` (7984–7988): the same function, the
same depth handling. No command wraps the entry in
another synthesis. Nested entries come only from `synthesizeChild` (8877–8881), called through
`sparkleChildSynth` from INSIDE `doSynth`, hence at depth ≥ 1 and inside the `try`.

**Conclusion of the reading:** in a process where only these commands touch the ref and
commands run one after another on one thread, the ref reads 0 whenever a command starts.

**What could make a command start at a non-zero depth** (each considered):

1. *An exception path that skips the restore.* None found (table above).
2. *Nested elaboration.* None found: commands do not nest, and the entry does not elaborate
   user commands.
3. *Another writer.* The ref is a PUBLIC declaration; any Lean code of the process can write it.
   `Sparkle/` does not, outside the entry. The test tree does, on purpose, to build nested
   states: `sparkleSynthDepth.set 1` in `Tests/Compiler/SubInstanceKeyTest.lean` 228,
   `NestedLetCacheTest.lean` 268, `CallWidthHuntTest.lean` 489, `NestedFailRestoreTest.lean`
   258, `SingleOutStaleProbe.lean` 92. A `run_cmd` that sets it and throws before resetting it
   leaves it non-zero for every later command of that FILE (I did not audit each of those tests
   for a `finally`). Not a public-command path, but it shows the premise is not a consequence of
   the compiler's code alone.
4. **FINDING — the ref is a cell of the process, not of a command or a thread.** It is shared by
   every thread of the `lean` process. *Across files* this is harmless under `lake build`: one
   process per file, each with a fresh ref. *Within one process* it holds only if no two
   elaborations overlap. By reading of the toolchain (v4.32.1, the version in
   `lean-toolchain`):
   * `Elab.async` "defaults to `false` but (when not explicitly set) is overridden to `true` in
     the Lean language server and cmdline" (`Lean/CoreM.lean` 35–41): theorem BODIES are
     elaborated on other threads. A command such as `#synthesizeVerilog` is not a theorem body,
     so I see no overlap of two public commands in a batch build — unless a tactic proof itself
     runs a synthesis, which nothing in this repository does to my knowledge (not searched
     exhaustively).
   * In the LANGUAGE SERVER, re-elaboration after an edit cancels the old command snapshots
     (`Lean/Language/Lean.lean` 612, 621: `cancelRec`) and starts the new parse without waiting;
     cancellation is cooperative (`Lean/CoreM.lean` 463–466: `checkInterrupted` throws only
     where the running code checks). A long `#synthesizeVerilog` that is being cancelled is
     still INSIDE its `try` — depth ≥ 1, caches part-filled from the OLD text — until it reaches
     a check. A command of the new elaboration that starts in that window reads depth ≥ 1, takes
     the NESTED branch (5506–5516: it does not empty `sparkleChildCache`, 5498), and its child
     entry answers from that cache (8878). I did not read the server far enough to know whether
     anything serialises the two, and I did not reproduce it (it needs the server).
   * `Tests/Compiler/DepthStartProbe.lean` (target-only, logs only) MEASURES the two ingredients
     that can be measured in a batch build: (A) a write made on another thread (`IO.asTask`) is
     read by the command's thread; (B/C) the public entry called while the depth reads 1 does
     not empty the child cache and returns with depth 1, against the same call from depth 0. It
     does not show an overlap.

   If the overlap is real it is not only a question of this premise: the nested branch would
   then run on a cache whose entries were compiled from another version of the file, and
   `ChildBnd`'s nested disjunct (`CacheInv`) is a premise about exactly that cache. That is a
   question for the reviewer, about every endpoint, not about `mixDeep`.

**What remains a premise.** Even granting "the ref reads 0", `Start0 mref cref w` says more:
there is a law witness `L : RefLaws mref cref` with `L.sval w = some synthesizeChild`,
`L.dval w = 0` and `L.quiet w`. That `L.dval` IS the ref's content in the start world is a
statement about the Lean runtime (`ST.Ref`, `MetaM`), of exactly the same kind as `ChildBnd`:
there is no model of the runtime under these laws, and nothing proves that an actual command's
run satisfies it. `Start0` is `ChildBnd` with its depth-0 disjunct chosen (BUILT:
`Start0.childBnd`); it is a STRONGER premise than `ChildBnd`, and the outermost endpoint is a
theorem about fewer runs than the built endpoints are.

## 6. Build order and `lakefile.lean` (not edited)

    lean_lib «Tools.ShippingMachineRanBase» where
      roots := #[`Tools.ShippingMachineRanBase]
    lean_lib «Tools.ShippingKidFactsRan» where
      roots := #[`Tools.ShippingKidFactsRan]
    lean_lib «Tools.ShippingMachineSeqLinkedRan» where
      roots := #[`Tools.ShippingMachineSeqLinkedRan]
    lean_lib «Tools.ShippingOutermost» where
      roots := #[`Tools.ShippingOutermost]
    lean_lib «Tools.ShippingOutermostCommand» where
      roots := #[`Tools.ShippingOutermostCommand]
    lean_lib «Tools.ShippingOutermostCoverage» where
      roots := #[`Tools.ShippingOutermostCoverage]

`Tests/AllTests.lean`: nothing to add (the three tests are target-only).

Order (each step's errors before the next):

1. `Tools.ShippingMachineRanBase`, then the ten split files in dependency order —
   `ShippingMachineTraceX`; `ShippingChecksCore`, `ShippingLinkedFresh`, `ShippingChecksRaw`,
   `ShippingClosedTyped`, `ShippingChecksOuts`, `ShippingChecksWidths`,
   `ShippingPortsMatchRaw`, `ShippingCoreClk`, `ShippingKidsSelf` — then
   `Tools.ShippingMachineRan`. This invalidates most of `Tools/` and every generated endpoint:
   the full rebuild is the real check that the corollaries have the old statements.
2. `Tools.ShippingKidFactsRan`, `Tools.ShippingMachineSeqLinkedRan`.
3. `Tests.Compiler.RanSplitStatementsTest` (read `RAN SPLIT STATEMENTS`).
4. `Tests.AllTests`, the census (expected 134 / 133, `mixDeep` open), `DepthSwitchPinTest`.
5. `Tools.ShippingOutermost`, `Tools.ShippingOutermostCommand`, `Tools.ShippingOutermostCoverage`,
   then `Tests.Compiler.MixDeepOutermostEndpointTest` (read the `OUTERMOST STEP`, `NOPORTS
   PREMISE`, `OUTERMOST ENDPOINT AUDIT` and `OUTERMOST ROW` / `TOTALS` lines and the four axiom
   listings).
6. `Tests.Compiler.DepthStartProbe` (read `DEPTH PROBE A / B / C`).

A commit of a split file can be reverted alone only together with the commits of the files that
call its `_ran` lemma (the dependency order of step 1, reversed).

## 7. UNVERIFIED, in risk order

1. **`composedOfTrace`** rests on a reading of a generator: that the closing binder of
   `f.machine_composedNR{n}` occurs in its proof term only inside ONE application of the wired
   head to `args.size + 12` arguments, and that the stored value has 12 leading lambdas. If the
   term was stored differently (auxiliary lemmas capturing the binder, a different lambda
   prefix) the builder throws; it cannot produce a wrong theorem (the kernel checks it), but the
   endpoint then does not exist and the composed theorem needs another route (re-running the
   generator with the `_ran` head — a copy of `generateCoreNR`, ~400 lines — or an edit of it).
2. **`openTerm`** is `generateX` with different arguments, written from a reading of
   `machine_design_noPorts`'s binder list (20 leading arguments, then `soundL`, `composed`,
   `houtTy`, 8 implicit, `hr`, `entry`, `closes`, 4 run hypotheses). Wrong positions give a type
   error at build, not a wrong theorem. Assumed: `a[4]` / `a[5]` of the ships theorem's proof
   term are syntactic lambdas of 7 / 4 binders, and `a[10]`, `a[11]` are `toExpr f` and
   `f.machineData`.
3. **`closeOutermost`**: that `Tools.ShippingBoundaryClose.solve` derives every conjunct of
   `mixDeep`'s built boundary from the five reflections and `ChildBnd`. PREDICTED from the
   measured case of `topD2` (same kids `mid2`, `midH`; `NoPortsTopD2BTest`): not measured for
   `mixDeep`, whose boundary has three kids. If a conjunct is a name premise that is not `True`,
   or `MachineClosesAt` of a kid without a derived closing, the builder throws and lists it.
4. **The textual split.** Twelve proofs moved by script. What can differ from the built proofs:
   the local context (no `hcore`, `entry`, `hB`, `closes`, `hne`, `hres`; `ran` instead) for
   tactics that search it (`assumption`, `simpa`, `omega` — none was seen to depend on these);
   `obtain … := ran0` needing to unfold `MachineRan` (the built `core_kids_self_ran` did the
   same and built); the term-mode corollaries' implicit arguments; unused-variable warnings.
5. **`RanSplitStatementsTest`**: assumes the four section variables are binders of every
   `variable`-bound theorem, in order `mctx mref cctx cref` (all four are mentioned in each
   statement — checked by script); the `open` lists copied per section.
6. The `_ran` heads: that `endpointParts mixDeep` returns one of the three heads this file
   covers (`ranHead` throws otherwise) — which one `mixDeep.machine_sound` uses I did not
   determine (a `circuit do` with calls: by reading of `Tools/ShippingMachineCommand.lean`
   1815, `machine_trace_of_data_causal`).
7. `#outermost_coverage` and the probe: plain MetaM / IO; the probe's `run_cmd` uses
   `IO.asTask` on a `ST.Ref.set`.
8. The classifier's label of `Start0` is MEASURED (`A-outermost-form.md`, integrator's record:
   NOT ALLOWED); the test asserts it again.

## 8. What I could not determine by reading

* Which wired head `mixDeep.machine_sound` is built from, and the exact shape of
  `mixDeep.machine_ships_hierNR2`'s boundary (both are generated; no source text).
* Whether the stored proof term of `mixDeep.machine_composedNR2` contains its closing binder
  anywhere else than the wired head (the builder checks it).
* Whether two elaborations of one process can overlap in the language server (§5, item 4), and
  the default of `Elab.async` under `lake build` beyond what `Lean/CoreM.lean` 35–41 says.
* Whether each test that sets `sparkleSynthDepth` by hand restores it on every path.

## Integrator's build record (2026-10-14) — MEASURED

BUILT on poc bcd604c4 + par/g-1 (19 commits applied to the tree, then committed one file group at a
time), cgrun 3 GiB swap 0, run `g1` (exit 0, peak 1.30 GB), worker's files UNCHANGED, FIRST ATTEMPT:
the split (12 built files) 66 s; the threading siblings; `RanSplitStatementsTest` (the 20 old statements
restated in full elaborate against the split theorems); the three outermost files;
`MixDeepOutermostEndpointTest` (216 s); `DepthStartProbe`; `Tests.AllTests` 1344 jobs (everything
downstream of the split rebuilt: every generated endpoint regenerated and audited); census UNCHANGED —
134 declarations, 133 covered, `mixDeep` open.

`mixDeep.machine_design_noPortsNR2_outermost`: standard axioms; 7 proposition binders (the run, five
reflections, `Start0`); the classifier labels `Start0` NOT ALLOWED (1), everything else ALLOWED; no
antecedent under the existentials; the census's own re-check FAILS on it, so it is not a census row.
`#outermost_coverage`: "outermost starts: 1 declaration [mixDeep] — a SEPARATE population, NOT counted in
#design_coverage's COVERED total". The existing endpoint `mixDeep.machine_design_noPortsNR2` is unchanged
(still with `MachineClosesAt mixDeep`).

STATE: `mixDeep` is connected at OUTERMOST starts (depth 0 for the law witness — a runtime premise of the
same kind as `ChildBnd`, strictly stronger). It is NOT covered in the census sense; the nested all-worlds
premise is open (needs determinism of the shared descendants' compiles).
The depth-0 evidence for public commands and the language-server concern (one depth cell per process; a
cancelled elaboration overlapping a new one — by reading, not reproduced) are in §5 above.
