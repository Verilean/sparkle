# B-core-dedup-slice1 — first slice of the `core_*` / `core_*M` consolidation (round par/b-24)

Status: WRITTEN, NOT BUILT. Base edd9496c, branch `par/b-24`, five commits
on `Tools/` plus one for the test and this note. Follows
`docs/parallel/B-unify-core.md` (4.3). No file under `Sparkle/`, no
`lakefile.lean`, no `Tests/AllTests.lean`, no existing test is changed.

## 0. Import graph (read from the `import` lines of edd9496c)

    ShippingMachineEntry            MemChildren (:862)            [memChild?: Sparkle/Compiler/MachMemory.lean:61]
      └ ShippingChildInv            RealChild (:451), Res (:55), ChildrenReal (:492)
          └ … ShippingCallsGate → ShippingCallsRunG; ShippingKidsChildIface (CallsKidsD, ClosedKinds, MachineDepthChild)
              └ ShippingChecksRun → ShippingChecksRun2
                  └ ShippingChecksCore (+ ChecksDepth)                      #1
                      ├ ShippingChecksRaw (+ ChecksShipsHier)               #2
                      ├ ShippingLinkedFresh                                 #3 #4
                      ├ ShippingChecksCoreGate (+ ChecksDepthGate)          #10
                      ├ ShippingClosedTyped (+ …)                           #11 → ShippingCoreClk #12
                      └ ShippingChecksOuts (ChecksExtract, LinkedFresh, ClosedPorts, OutsExtractedParts)   #5
                          └ ShippingChecksWidths (+ TransitionPortTys, InstWidthsParts)                    #6 #7 #8
                              ├ ShippingChecksRunFacts (+ GuardsSound)                                     #9
                              │   └ ShippingTextShipped (PrintGuard, ClosedTyped)                          #17
                              └ ShippingPortsMatchRaw (ClosedTyped, TextShipped, LeafTyped)                #13 #14
                                  ├ ShippingKidsSelf (KidsPassLeaf, ChildServe, ChecksMasked)              #15 #16
                                  └ ShippingOneOutConns
    ShippingMemKidCore  imports ChecksCore, ChecksRaw, LinkedFresh, ChecksOuts, ChecksWidths, ChecksRunFacts, ChecksCoreGate
    ShippingMemKidPorts imports MemKidCore, ClosedTyped, CoreClk, PortsMatchRaw, KidsSelf, TextShipped
    ShippingMemKidFacts imports MemKidPorts, KidFacts, DesignSVMem, MachineShipsHier
    ShippingCoreFromM   imports MemKidCore;  ShippingCoreFromMPorts imports CoreFromM, MemKidPorts

(# = row of the inventory in `B-unify-core.md`.) At edd9496c `Kid`, `kid_of`,
`Kid.real`, `Kid.mem` were defined in `ShippingMemKidCore.lean:72–116`
(namespace `Tools.ShippingMemKid`), the bridge in `ShippingCoreFromM.lean:60–81`
(namespace `Tools.ShippingCoreFromM`). No old file imports an `M` file.

**Which `M` theorems are leaves: none.** The calls between `M` theorems:

| `M` theorem | calls |
|---|---|
| `core_kids_factsM` (#1, not a corollary) | — |
| `core_raw_factsM` #2, `core_callPortsM` #6, `core_hierGateM` #8 | `core_kids_factsM` |
| `core_linkedWFM` #3, `core_outsCheck_all_gateM` #10, `core_closed_typedInM` #11 | `core_kids_factsM` |
| `core_instOuts_not_assignedM` #4 | #3 |
| `core_outsExtractedM` #5 | #1, #4 |
| `core_instOutWidthsOkM` #7 | #6 |
| `core_runFactsM` #9 | #2, #8, #3, #5, #7 |
| `core_clkM` #12, `core_kids_selfM` #15 | — |
| `core_callConnsM` #13, `core_callStmtM` | #1 (`core_callStmtM` also #13) |
| `core_portsMatch_rawM` #14 | #11, #13 |
| `core_kidsPass_deepM` #16 | #1, #15, #8 |
| `core_designCheck_runM` #17 | #9, #11 |

Every one of the ten corollaries reaches `core_kids_factsM`, which is one of
the SEVEN (old statement without `hfne`). So the first move has to be
`core_kids_factsM` itself, as a pure move (its old twin keeps its proof).
After it, the leaf-most corollaries are #2, #6, #8 (and #13): they call
nothing else. This slice does #2, #8 and #6 (#6 is the bridged one: a kid
hypothesis and a kid in the conclusion). `core_outsExtracted` (#5), named as
a candidate, is NOT leaf-most: it needs #3 and #4 moved first.

## 1. What each commit does

All four moved `M` blocks are byte-identical to the blocks of edd9496c
(checked by a script: doc comment, `set_option`, statement, proof). The three
old statements are line-identical up to `:= by`. Every other theorem block of
the three old files and of `ShippingMemKidCore.lean` is unchanged.

| commit | moved (name and namespace kept) | from → to | old proof replaced |
|---|---|---|---|
| 1/5 | `Kid`, `kid_of`, `Kid.real`, `Kid.mem` (`Tools.ShippingMemKid`); `kid_iff_real_of_nomem`, `real_of_kid`, `kid_of_real` (`Tools.ShippingCoreFromM`) | `ShippingMemKidCore.lean`, `ShippingCoreFromM.lean` → NEW `Tools/ShippingKid.lean` (imports `Tools.ShippingChildInv` only) | — |
| 2/5 | `core_kids_factsM` (158 lines) | `ShippingMemKidCore.lean` → end of `ShippingChecksCore.lean` | — (`core_kids_facts` is not a corollary) |
| 3/5 | `core_raw_factsM` (112) | → `ShippingChecksRaw.lean`, after the helper lemmas | `core_raw_facts`: 87 → 2 lines |
| 4/5 | `core_hierGateM` (55) | → top of `ShippingChecksWidths.lean` | `core_hierGate`: 33 → 2 lines |
| 5/5 | `core_callPortsM` (168) | → same block of `ShippingChecksWidths.lean` | `core_callPorts`: 132 → 9 lines |

The bridge keeps the namespace `Tools.ShippingCoreFromM` although it now
lives in `ShippingKid.lean`: `CoreFromMAuditTest` (not editable here) names
`Tools.ShippingCoreFromM.real_of_kid` etc.

Layout of a moved `M` theorem: a `namespace Tools.ShippingMemKid … end` block
with the SAME thirteen `open` lines as `ShippingMemKidCore.lean` (they are
also the old files' own `open` lines — compared) and the same `variable`
line, so the proof text is elaborated in the namespace and under the opens it
was built with.

- `ShippingChecksCore.lean`: the block is after `end Tools.ShippingChecksCore`
  with `open Tools.ShippingChecksCore` (the proof reads `closeMachine_outputs`).
- `ShippingChecksRaw.lean`: the old namespace is closed after the helpers,
  the block has `open Tools.ShippingChecksRaw` (`rst_not_allocated`,
  `instNameOf_eq`, `noSelfRead_of_feed`), then the old namespace is reopened
  with its `open` lines repeated.
- `ShippingChecksWidths.lean`: the block is BEFORE `namespace
  Tools.ShippingChecksWidths` (neither proof reads a declaration of that
  namespace), nothing is closed or reopened.

The new old-theorem bodies are the bodies of the BUILT `_fromM` theorems with
`Tools.ShippingMemKid.…M` and `Tools.ShippingCoreFromM.real_of_kid` written
in full (the old namespaces do not open those two).

KEPT: the three `_fromM` constants (`core_raw_facts_fromM`,
`core_hierGate_fromM`, `core_callPorts_fromM`) — now second derivations of
statements the old names also derive that way; `CoreFromMAuditTest` reads
them and cannot be edited in this round.

**A log line of an existing test becomes untrue.** `CoreFromMAuditTest`
ends its summary with "NOTHING is replaced: the old theorems are unchanged
and no declaration uses a _fromM theorem." After this slice three old proofs
ARE replaced (the second half of the sentence still holds). Its checks
should still pass (it throws only if a `_fromM` proof names the OLD theorem;
the dependency now runs old → `M`, and `_fromM` → `M`). Its "old declaration
lines" column shrinks for the three (log only). The integrator should reword
that line when the test may be edited.

## 2. Lines

| commit | added | removed | net |
|---|---|---|---|
| 1/5 | 123 | 73 | +50 (file header, two `open` blocks) |
| 2/5 | 192 | 164 | +28 (block header and `open`s) |
| 3/5 | 79 | 116 | −37 |
| 4/5 | 88 | 88 | 0 (first block of the file) |
| 5/5 | 77 | 197 | −120 (joins the existing block) |
| `Tools/` total | 559 | 638 | **−79** |

Proof lines of the three old theorems: 252 → 13 (**−239**). The rest of the
difference is overhead: one `Tools.ShippingMemKid` block per old file
(≈ 25–45 lines of header, `open`s, and — where the old namespace has to be
reopened — the `open`s a second time). The overhead is per FILE, not per
theorem (5/5 shows the rate once the block exists), so the ≈ 610 lines of
`B-unify-core.md` 4.1 should be read as ≈ 610 minus ≈ 30–45 per old file
touched (eight files for the ten corollaries).

Added outside `Tools/`: the test (≈ 135 lines) and this note.

## 3. The new test

`Tests/Compiler/CoreDedupAuditTest.lean` (NOT in `Tests/AllTests.lean`: add
`import Tests.Compiler.CoreDedupAuditTest`). THROWS unless, for each of the
three: the old constant's type `isDefEq` its `_fromM` twin's type; old, `M`
and twin on standard axioms; the old proof term names the `M` form; the `M`
proof does not name the old; old and `M` are both declared in the old
theorem's module. THROWS unless the seven declarations of `ShippingKid.lean`
and `core_kids_factsM` are declared where this round put them, on standard
axioms. LOGS `Expr.numObjs` of the proof terms: old name AFTER, the twin, the
`M` form. The size BEFORE is not obtainable after the replacement; the `M`
proof (the scripted copy of the old one) is logged as a stand-in and named
as such. To get the true BEFORE figure: evaluate
`(← getConstInfo n).value!.numObjs` for the three old names on edd9496c.

## 4. What the integrator builds

lakefile (the integrator adds it; every `Tools` module has its own entry):

    lean_lib «Tools.ShippingKid» where
      roots := #[`Tools.ShippingKid]

| commit | first targets | then |
|---|---|---|
| 1/5 | `Tools.ShippingKid`, `Tools.ShippingMemKidCore`, `Tools.ShippingCoreFromM`, `Tools.ShippingCoreFromMPorts` | `Tests.Compiler.CoreFromMAuditTest`, `Tests.AllTests` (only what is above `ShippingMemKidCore` is rebuilt) |
| 2/5 | `Tools.ShippingChecksCore`, `Tools.ShippingMemKidCore`, `Tools.ShippingMemKidPorts` | `Tools.ShippingCoreFromMPorts`, `CoreFromMAuditTest`, `Tests.AllTests` — this one rebuilds the WHOLE check-free chain (everything above `ShippingChecksCore`) |
| 3/5 | `Tools.ShippingChecksRaw`, `Tools.ShippingMemKidCore` | as above (everything above `ShippingChecksRaw`) |
| 4/5 | `Tools.ShippingChecksWidths`, `Tools.ShippingMemKidCore` | as above (everything above `ShippingChecksWidths`) |
| 5/5 | `Tools.ShippingChecksWidths`, `Tools.ShippingMemKidCore` | as above, plus `Tests.Compiler.CoreDedupAuditTest` (it needs all five) |

Each commit is meant to build on its own. To save queue time: build HEAD
(`Tools.ShippingMemKidPorts`, `Tools.ShippingCoreFromMPorts`, the two audit
tests, `Tests.AllTests`, and the target-only endpoints the round normally
re-checks) and go back commit by commit only on a failure.

## 5. What may not elaborate, most likely first

1. **Name resolution after the moves.** (a) `ShippingKid.lean` has FOUR of
   the thirteen `open` lines (`Lean Meta`; `Sparkle.Compiler.Elab
   Sparkle.IR.AST Sparkle.IR.Machine`; `Tools.ShippingEntrySoundness
   Tools.ShippingMachineEntry`; `Tools.ShippingChildInv`): `MachineShape`,
   `Res`, `RealChild`, `MemChildren`, `Name` must resolve with these alone.
   Fewer opens cannot make a name ambiguous, but a name that came from one of
   the nine dropped namespaces would be unknown (none found by reading).
   (b) In the old namespaces, `Tools.ShippingMemKid.core_…M` and
   `Tools.ShippingCoreFromM.real_of_kid` are written in full.
2. `open Tools.ShippingChecksCore` / `open Tools.ShippingChecksRaw` inside
   the `Tools.ShippingMemKid` block of the same file, after `end` of that
   namespace: the namespace is registered by its declarations above (both
   files have some), so this should hold; the `ShippingChecksWidths` block
   deliberately has no such `open` (nothing is declared there yet).
3. `ShippingChecksRaw.lean`: the reopened `namespace Tools.ShippingChecksRaw`
   — the `open` block is repeated verbatim, the original `variable` line
   follows it; `core_shipsHier_rest` and everything after are unchanged.
4. Universe / implicit order of `core_callPorts`: the `obtain` patterns are
   those of the built `core_callPorts_fromM`; only the constants' spelling
   differs.
5. The test: `moduleOf` (`env.getModuleIdxFor?`, `env.header.moduleNames` —
   the pattern of the built `Tests/Compiler/OptPrintCensusTest.lean:168`),
   `Expr.numObjs : Expr → IO Nat` lifted into `TermElabM`, and the module
   names `Tools.ShippingChecksRaw` / `Tools.ShippingChecksWidths` /
   `Tools.ShippingKid` as recorded by the environment.
6. Linter only: unused `hnomem` in `core_raw_facts`, `core_hierGate` (part
   of the statement), and `set_option maxHeartbeats 4000000 in` left in
   front of three now short proofs (harmless; kept so the header lines of
   the old theorems are untouched).

## 6. What stays duplicated, and the order recommended

Still twice: the seven non-corollaries (#1, 3, 4, 10, 11, 12, 15; 570 proof
lines) and seven corollaries (#5, 7, 9, 13, 14, 16, 17; 420 proof lines).

Order (each step = one commit; "pure move" = like 2/5, no old proof changes):

1. #7 `core_instOutWidthsOk` — READY: its `M` form calls only
   `core_callPortsM`; joins the block at the top of `ShippingChecksWidths.lean`
   (18 → 4 lines).
2. #13 `core_callConns` — READY: calls only `core_kids_factsM`; in
   `ShippingPortsMatchRaw.lean` after its helpers (`callStmtG_conn`,
   `callArgsOk`, `callArgs_width`), closed/reopened like `ShippingChecksRaw`;
   `core_callStmtM` moves with it (155 → ≈ 12 lines).
3. pure move of #3, #4 to the end of `ShippingLinkedFresh.lean`; then #5
   `core_outsExtracted` in `ShippingChecksOuts.lean` (143 → 3).
4. #9 `core_runFacts` in `ShippingChecksRunFacts.lean` (needs 1 and 3).
5. pure move of #11 to `ShippingClosedTyped.lean`; then #14
   `core_portsMatch_raw` and #17 `core_designCheck_run` (#17 needs 4).
6. pure move of #15 to `ShippingKidsSelf.lean`; then #16 `core_kidsPass_deep`.
7. pure moves of #10 (`ShippingChecksCoreGate.lean`) and #12
   (`ShippingCoreClk.lean`): `ShippingMemKidCore.lean` /
   `ShippingMemKidPorts.lean` are then import-only shims.
8. With the test editable: drop the ten `_fromM` constants and the two
   `CoreFromM*` files (bridge already in `ShippingKid.lean`); then the mode
   hypothesis of `B-unify-core.md` 5.1 for the seven.

## Build record (integrator, 2026-10-13)

Verified tree `bb456eadda49517eac3b4f90d73ea0d42f9a7b1a` = poc c45f545c + the six commits of par/b-24 applied together (one refactor
commit on poc; NO compiler file touched) + one `lean_lib` + one import + ONE integrator change: the log
sentence of `Tests/Compiler/CoreFromMAuditTest.lean` that said "NOTHING is replaced" (now false for three
theorems) reworded. cgrun 3 GiB, swap 0.

- `20261013-152603-b24-all`: the refactored files, both audits and AllTests — result=success, memory_peak_file=1728446464; Build completed successfully (1275 jobs).
- `20261013-153226-b24-final` (after the wording change): result=success; Build completed successfully (1275 jobs).

Established: no theorem name or statement changed (`CoreDedupAuditTest`: the three old theorems' types are
`isDefEq` their `_fromM` twins', standard axioms, their proofs name the `M` forms; 8 moved declarations
checked); `CoreFromMAuditTest` still 10 of 17 `isDefEq`. The proofs of `core_raw_facts`, `core_hierGate`,
`core_callPorts` are now corollaries (252 → 13 proof lines; net −79 lines in `Tools/`). Still duplicated:
the 7 non-corollaries and 7 further corollaries; the `_fromM` twins are kept as independent re-derivations.

```
n:96:0: COREDEDUP AUDIT TABLE:
n:96:0: COREDEDUP AUDIT: 3 old core_* theorems are now corollaries of their M forms (statement defEq the _fromM twin's, standard axioms, proof names the M form); the M forms and core_kids_factsM are declared in the old theorems' modules, Kid and its bridge in Tools.ShippingKid (8 moved declarations checked). The _fromM twins are KEPT (independent re-derivations, read by CoreFromMAuditTest). Still duplicated: the 7 non-corollaries and the other 7 corollaries.
```
