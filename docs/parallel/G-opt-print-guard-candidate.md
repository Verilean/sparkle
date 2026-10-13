# G / the optimizer's print guard and the merge's register guard: an isolated candidate

Branch `fix/opt-print-guard`, base poc `cfbab0db`. **WRITTEN, NOT BUILT, NOT
RUN.** Nothing here was elaborated, built or simulated by me. NOT integrated:
a candidate for the user's decision (`docs/parallel/B-optprint.md` §5). This
is the only branch on which `Sparkle/IR/` is edited.

Marks: **[R]** read in the source, **[P]** predicted by reading, **[M]**
measured — the only [M] quoted are the integrator's records in
`docs/parallel/B-optprint.md` and `docs/parallel/A-leaf-entry-2.md` (on poc,
with the guards computed in test code).

## 1. The compiler diff (`Sparkle/IR/RefineCheck.lean`, one file)

G-opt, `checkedOptimize`, instance-free assign + register branch (line 392):

      else if m.body.all seqStmtOk then
    -   if RefineCheck.refineCheck m o then o else m
    +   if RefineCheck.refineCheck m o && Sparkle.IR.PrintGuard.printOk o then o else m

G-reg, `mergeChecked`, last branch (lines 274–275):

    - else if refineCheck m r && (masksKept m r && Sparkle.IR.PrintGuard.printOk r) then r else m
    + else if refineCheck m r && (masksKept m r && (Sparkle.IR.PrintGuard.printOk r &&
    +     !(r.body.all Sparkle.IR.RegDedup.isAssign))) then r else m

plus the two doc comments of the functions. No other compiler file.

* **Fallback, never a rejection** [R]: both new conjuncts sit in an
  `if … then candidate else m`; the `else` is the input module. No `throw`,
  no new failure path: the success domain is unchanged.
* **An assignment-only input is unaffected** [R]: `mergeChecked` is
  `if m.body.all isAssign then r else if <guards> then r else m` (261, 274).
  The new conjunct is in the second `if`, reached only when
  `m.body.all isAssign = false`; an assignment-only body returns `r` at 261
  before any guard is read. No additional `isAssign m` test is needed.
* **`refineCheck` stays the LEFT conjunct** in both; the new conjunct of the
  merge is INNERMOST, so the left projection (`mergeChecked_nonAssign` and
  four `Tools/` sites) and the left-of-right projection
  (`mergeChecked_masks`) are unchanged.
* **No import cycle** [R]: `RefineCheck` imports `OptCheck` and `HierCheck`;
  `HierCheck` imports `PrintGuard`; `PrintGuard` imports `PrintCheck`,
  `Semantics`, `RegDedup`, `ReorderInvariance` — none of them imports
  `RefineCheck` or `OptCheck`. `mergeChecked` already called
  `Sparkle.IR.PrintGuard.printOk` on poc; no import line is added.

## 2. Proofs

### 2.1 Patched (2 lines, both in `Sparkle/IR/RefineCheck.lean`)

| theorem | line | change |
|---|---|---|
| `mergeChecked_print` | 334 | `and_right_true (and_right_true hc)` → `and_left_true (and_right_true (and_right_true hc))` |
| `checkedOptimize_seqOk` | 412 | `Or.inl hc` → `Or.inl (RefineCheck.and_left_true hc)` |

No statement changed. No file in `Tools/` is edited.

### 2.2 Read again site by site at `cfbab0db`, predicted to pass unchanged [P]

`checkedOptimize` (25 sites in `Tools/`, 1 in `Sparkle/`):

* **rebuild decides** — walk every branch with `repeat' split`, each goal
  closed by the same three alternatives; the new condition changes no goal
  shape, only the hypothesis `split` introduces (unused):
  `Tools/ShippingModuleNames.lean` 94 (`checkedOptimize_name`),
  `Tools/ShippingOptSoundness.lean` 367 (`checkedOptimize_wires_sublist`),
  `Tools/ShippingOptimizePorts.lean` 58 (`checkedOptimize_ports`);
* `simple` branch only (`simp only [hg, if_true]` selects it; the `seq`
  branch disappears before `split`): `ShippingAssignmentOrder` 119,
  `ShippingOptSoundness` 309, 328, `ShippingSVBridge` 386, 462,
  `ShippingPrintEntrySoundness` 52, `ShippingPrintSoundness` 465,
  `ShippingMachineShipsComb` 135; with full `simp [checkedOptimize, hg, …]`:
  `ShippingPrintSoundness` 563, 571, `ShippingControlOptSoundness` 62, 105
  (if `simp` visits the dead `else` before `if_pos`, it meets one more `&&`
  there — no lemma of those calls fails on it);
* instance branches only (`not_all_seqOk hI` rewrites the `seq` test to
  `false` first): `ShippingShipsNoOuts` 181, `ShippingShipsHierFree` 185,
  `ShippingMachineShipsHier` 298, `ShippingMachineShipsHierH` 188,
  `ShippingShipsFree` 201, `ShippingChecksDerived2` 79,
  `ShippingPortsMatchShipped` 49, `ShippingGuardsSound` 294, 306,
  `ShippingHierShipsSV` 40;
* through the lemma `checkedOptimize_seqOk` (statement unchanged):
  `ShippingChecksDerived`, `ShippingMachineShipsW`, `ShippingChecksWidths`,
  `ShippingLeafEntry`, `ShippingMachineShipping` (via `checkedOptimize_seq`).

`mergeChecked` (9 sites in `Tools/`, 4 in `Sparkle/`):

* assignment-only branch only: `ShippingGateChildComb` 116,
  `ShippingMachineChildComb` 392, `ShippingMergeClosed` 152,
  `ShippingMachineShipsComb` 255, `ShippingCombKidText` 201;
* enter the guarded branch and take `and_left_true hrc` only:
  `ShippingSeqChildIface` 74, `ShippingMachineShipsHier` 70,
  `ShippingMachineDepthRun` 87, 254;
* `Sparkle/`: `mergeChecked_cases` (two `split`s, `rfl`), `_nonAssign`
  (left), `_masks` (left of right) unchanged; `_print` patched.

### 2.3 New (`Tools/ShippingGuardsLeaf.lean`, imports `Tools.ShippingLeafEntryBnd`)

    theorem checkedOptimize_instFree_print {m : Sparkle.IR.AST.Module}
        (hs : Sparkle.IR.OptCheck.simpleBody m = false)
        (hok : m.body.all Sparkle.IR.OptCheck.seqStmtOk = true) :
        Sparkle.IR.OptCheck.checkedOptimize m = m ∨
          Sparkle.IR.PrintGuard.printOk (Sparkle.IR.OptCheck.checkedOptimize m) = true

    theorem mergeChecked_keeps_reg {m : Sparkle.IR.AST.Module}
        (h : m.body.all Sparkle.IR.RegDedup.isAssign = false) :
        (Sparkle.IR.RefineCheck.mergeChecked m).body.all Sparkle.IR.RegDedup.isAssign = false

Proofs: the tactic text of `checkedOptimize_seqOk` (same `unfold` /
`dsimp only` / `simp only` / `split`, the right projection) and of
`Tools.ShippingSeqChildIface.mergeChecked_seqOk` (`unfold` / `dsimp only` /
`split` twice, three right projections and `(!a) = true → a = false`). A new file rather
than `Tools/ShippingGuardsSound.lean` (which holds the instance-branch
facts): the leaf consequences below need `Tools.ShippingLeafEntryBnd`, which
that file does not import. (`Tools.ShippingTextShipped.checkedOptimize_print`
is the `hierGate` fact — a different statement in a different namespace.)

The binders of the leaf entry, discharged:

    theorem mergeReg_closed (b : Module) :
        ∀ m0, b = mergeChecked m0 → m0.body.all isAssign = false → b.body.all isAssign = false
    theorem leaf_entry_seqBranch (K : LeafKid … c dk) (hbnd : ChildBnd mref cref w) (hr : RunsTo …) :
        simpleBody b = false ∧ b.body.all seqStmtOk = true
    theorem leaf_entry_optPrint (K) (hbnd) (hr) :
        checkedOptimize b = b ∨ printOk (checkedOptimize b) = true
    theorem leaf_entry_textChecks_closed (K) (hbnd) (hr) : (the conclusion of leaf_entry_textChecks_bnd)
    theorem leaf_entry_shipped_seq_closed (K) (hbnd) (hr) : (checkedOptimize b).body.all seqStmtOk = true
    theorem leaf_entry_ships_closed (d) (soundL) (K) (hbnd) (hr) : (the conclusion of leaf_entry_ships_bnd)

`leaf_entry_ships_closed` is `leaf_entry_ships_bnd d @soundL K hbnd hr
(mergeReg_closed b) (leaf_entry_optPrint K hbnd hr)`.

## 3. The payoff: `cnt` (`Tests/Compiler/LeafEntryCntClosedTest.lean`)

`cnt.machine_ships_leafC`: the proof term of `cnt.machine_ships_leafB` with
`hmergeReg := mergeReg_closed b` and
`hoptPrint := leaf_entry_optPrint (cnt_leafKid entry) hbnd hr`.

| endpoint | premise | predicted state (pending build) |
|---|---|---|
| `cnt.machine_ships_leafC` vs `cnt.machine_ships_leafB` | `hmergeReg` | absent — a theorem of this branch's compiler |
| | `hoptPrint` | absent — a theorem of this branch's compiler |
| | `RunsTo (synthesizeCombinational cnt) …` | ALLOWED |
| | `MachineDefines … cnt cnt.machineData.shape` | ALLOWED |
| | `ChildBnd mref cref w` | ALLOWED |
| | `InvW`, `simpleBody`, `seqCheck`, `seqNames`, `MachineCloses`, `printOk`, `isAssign` | absent |

The test asserts: exactly 3 proposition binders (one of each allowed kind),
0 NOT ALLOWED, the seven constants absent, standard axioms for the endpoint
and the eight theorems of `Tools/ShippingGuardsLeaf.lean`.

SCOPE: one declaration, one module (`MachineShips` at the emitter's own width
map); not `DesignSV`, not the SV string, not `#sim`; data conditions decided
for `cnt`; the run, the reflection, the runtime boundary are premises. It is
a statement about the compiler OF THIS BRANCH. Whether it counts as a
check-free endpoint is the integrator's / user's call after the build.

## 4. The guards fire (`Tests/Compiler/OptPrintGuardFiresTest.lean`)

The guarantee, restated (`opt_guard_guarantee`, `merge_guard_guarantee`,
standard axioms asserted), and three evaluated firings — an error when a
value is not as stated:

| module | what is asserted |
|---|---|
| `optCex` (probe file, hand-written IR) | `simpleBody` false, `seqStmtOk` all, `printOk m`, `refineCheck m o`, **`printOk o` false**, `checkedOptimize m == m`, `printOk (checkedOptimize m)`, `== guardedOptimize m` |
| `mergeCex` (probe file, hand-written IR, multiply driven) | body not assignment-only, `refineCheck`, `masksKept`, `printOk` of the merge true, **merged body assignment-only**, `mergeChecked m == m`, kept body not assignment-only, `== mergeGuarded m` |
| `shlAdd32` (`OptPrintSourceTest`, a REAL source; the full entry is run) | as `optCex` on the entry's module `b`; the shipped top `checkedOptimize b` is `b` and passes `printOk`; the modules named as `b` in `designArtifact` of the returned design pass `printOk` |

All values are [P] here; for `optCex`, `mergeCex` and `shlAdd32` each
operand was [M] on poc by the integrator (A-leaf-entry-2 build record;
B-optprint run record row `shlAdd32`: `printOk(b)=T refineCheck=T
printOk(opt b)=F printOk(guarded)=T`), so the predictions are those
measurements carried through one `&&`.

## 5. Existing files whose LOG TEXT changes on this branch (none throws) [R]

* `Tests/Compiler/LeafEntryCexProbe.lean` (target-only): both `VERDICT`
  lines flip to `PREDICTION REFUTED — …`. The file has no `throwError`; it
  logs. The wording "the reading … is wrong somewhere" is then misleading:
  the reading was right for poc, the compiler changed. Not edited.
* `Tests/Compiler/OptPrintSourceTest.lean` (target-only): the six hit rows
  become `checkedOptimize(b)==b=T printOk(checkedOptimize b)=T
  guard-changes-shipped=F hit=F`; `SUMMARY`: hits 0, predictions right 6,
  wrong 6 (its predictions are poc's). No `throwError` on a prediction.
* `Tests/Compiler/OptPrintCensusTest.lean` (target-only): `fires` and
  `MERGE … FIRES` are computed against test-code guards that now equal the
  compiler; both stay 0.
* `Tests/Compiler/LeafEntryCntBndTest.lean` (in AllTests): still asserts
  exactly 2 NOT ALLOWED binders of `cnt.machine_ships_leafB` — true, the
  statement keeps its binders; its closing log line ("false by reading") is
  stale on this branch.

## 6. Integrator

`lakefile.lean` (I did not edit it):

    lean_lib «Tools.ShippingGuardsLeaf» where
      roots := #[`Tools.ShippingGuardsLeaf]

`Tests/AllTests.lean` (only if the candidate is accepted):
`import Tests.Compiler.LeafEntryCntClosedTest`,
`import Tests.Compiler.OptPrintGuardFiresTest`. Name added under `cnt`:
`machine_ships_leafC`.

Order (each in the protected queue; `Sparkle.IR.RefineCheck` changes, so
everything downstream of it rebuilds — the whole compiler and `Tools/`):

1. `lake build Sparkle.IR.RefineCheck` — the two patched proofs;
2. `lake build Tools.ShippingModuleNames Tools.ShippingOptSoundness
   Tools.ShippingOptimizePorts` — the three `repeat' split` sites;
3. `lake build Tools.ShippingGuardsLeaf` — the new theorems (pulls most of
   `Tools/`, among them the four `mergeChecked` sites of §2.2);
4. `lake build Tests.Compiler.LeafEntryCntClosedTest` — read `LEAFENTRYC`;
5. `lake build Tests.Compiler.LeafEntryCexProbe
   Tests.Compiler.OptPrintSourceTest Tests.Compiler.OptPrintGuardFiresTest`
   — read `GUARDFIRES`, the flipped `LEAFCEX … VERDICT`, `OPTPRINT SRC`;
6. `lake build Tests.AllTests` — compare the count with poc;
7. `lake build Tests.Compiler.OptPrintCensusTest` — `OPTPRINT DIGEST today`
   against poc;
8. `MemoHitCensusTest` and `NestedLetCacheTest` digests against poc;
9. `scripts/shipping-coverage/optprint_sim.sh`, `writer_sim.sh` (after 5).

Predicted results [P], against the poc records:

| run | poc [M] | this branch [P] |
|---|---|---|
| `Tests.AllTests` | green | green, same count (+2 if the two imports are added) |
| `OPTPRINT DIGEST today` 361 / 362 | 1444467916182415447 / 8149634735370364912 | identical (on poc `today` = `guarded` and 0 declarations changed) |
| `OPTPRINT CENSUS` (d), `fires`, `MERGE … FIRES` | 0, 0, 0 | 0, 0, 0 |
| `MemoHitCensusTest` combined digest (361) | poc's value | identical — with one caveat: that digest is of the entry's result (`(Module × Design)` after the merge), which G-reg could change only where it fires (0 of 13 on poc) and G-opt not at all (the optimizer runs in the writer) |
| `NESTEDLET DIGEST` (84) | poc's value | identical, same reason |
| `optprint_sim.sh` | 12 × `command==source T`, `printOk-shipped` T 6 / F 6, `guard-changes-text` T 6 | 12 × `command==source T` (the six texts are poc's `guarded` texts, [M] `guarded==source T`), `printOk-shipped=T` × 12, `guard-changes-text=F` × 12, TOTAL "shipped top with printOk false: 0" |
| `writer_sim.sh` | 7/7 | 7/7, texts unchanged unless one of its declarations is of `shlAdd32`'s shape (not checked) |

A digest that differs is not a failure of the candidate by itself: it names
a declaration whose shipped text falls back to the unoptimised module —
report it with the declaration.

UNVERIFIED, highest risk first:

1. `Tests/Compiler/LeafEntryCntClosedTest.lean`, second `run_cmd`: the term
   `leaf_entry_textChecks_bnd … (mergeReg_closed b) (leaf_entry_optPrint …)`
   inside the quotation (`b` is the lambda's implicit binder); the report
   tuple `(lines, counts)` and `List.getD`.
2. `Tests/Compiler/OptPrintGuardFiresTest.lean`: the third `run_cmd`
   (`runBoth` of `OptPrintSourceTest` reused; projections `res.2.1`,
   `res.2.2`; `(sparkleSynthDepth.set 0 : IO Unit)` inside `liftTermElabM`);
   `throwError` inside plain `run_cmd do`; the import of the probe AND the
   source test in one file (no shared name found by reading). A VALUE
   mismatch there is a finding, not a syntax error: report the
   `GUARDFIRES` line.
3. `Tools/ShippingGuardsLeaf.lean`: `mergeChecked_keeps_reg` — two
   `split`s under `.body.all isAssign`, the tactic shape of the built
   `Tools.ShippingSeqChildIface.mergeChecked_seqOk` (`rename_i hall`, then
   `rename_i _ hc`); the first branch closes by
   `absurd (hall.symm.trans h) (by decide)` (`true = false`);
   `bnot_true_false` (`simp at h` on `(!true) = true`);
   section `Entry`: the `open` lines are those of
   `Tools/ShippingLeafEntryBnd.lean`'s section `Entry`, in another namespace;
   `@soundL` passed on.
4. The three `repeat' split` sites (§2.2) and the four full-`simp` sites.
5. A test in `Tests.AllTests` that pins the emitted text of a 32- / 64-bit
   register machine with a literal shift under `+ - *` or a comparison: its
   text changes to the unoptimised module (none found by the census on 362
   declarations; pinned texts outside that population were not searched).
6. `checkedOptimize_seqOk` / `mergeChecked_print`: one projection each.

## Verification of this candidate in isolation (integrator, 2026-10-13) — NOT merged into poc

Branch `fix/opt-print-guard-build` = `fix/opt-print-guard` d4084fb5 (on poc cfbab0db) + one `lean_lib` entry
(`Tools.ShippingGuardsLeaf`). Worker files unchanged; everything built at the first attempt. cgrun 3 GiB,
swap 0, one job.

- `lake build Tests.AllTests Tests.Compiler.OptPrintCensusTest Tests.Compiler.NestedLetCacheTest
  Tests.Compiler.OptPrintSourceTest`: Build completed successfully (1254 jobs). The three `repeat' split`
  sites and all other unfold sites of `checkedOptimize` / `mergeChecked` in `Tools/` built unchanged.
- `cnt.machine_ships_leafC`: premises exactly `ChildBnd`, the run, `MachineDefines cnt` (all ALLOWED);
  standard axioms — on THIS branch only; it is not a poc endpoint.
- Guard firing: on the real source `shlAdd32` the print guard fires and the shipped top is the unoptimised
  module with `printOk` true; `OptPrintSourceTest`: shipped modules with `printOk` false 0 (6 on poc);
  `LeafEntryCexProbe`: both statements now hold on `mergeCex` / `optCex`.
- Census on 362 returned declarations: `printOk` guard would-fire list empty, merge guard FIRES 0; digests
  of the shipped texts equal to poc's: 361 declarations 1444467916182415447, 362 declarations
  8149634735370364912. `WIREWIDTH DIGEST` 361: 11874691237837614088 and `NESTEDLET DIGEST` 84:
  2141260620024790681 — equal to poc's.
- `optprint_sim.sh`: 12/12 `command==source T`, shipped top with `printOk` false 0. `writer_sim.sh`: 7/7
  `new==source T`.

Not established: all successful inputs; text for sources outside the measured population (the six
constructed shift declarations change to the unoptimised module by design). Integration is the user's
decision; if integrated, the integrated poc tree is built again before the commit.

Run records:
- `20261013-092629-guard-tools`: result=success, exit=0, memory_peak_file=2739781632, events: low 0 high 149 max 0 oom 0 oom_kill 0 oom_group_kill 0 
- `20261013-095411-guard-all`: result=success, exit=0, memory_peak_file=1660805120, events: low 0 high 0 max 0 oom 0 oom_kill 0 oom_group_kill 0 
