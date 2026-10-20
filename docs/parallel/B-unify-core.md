# B-unify-core — making the `core_*` / `core_*M` duplication removable (round par/b-16)

Status: WRITTEN, NOT BUILT. Base 8554bddb. No existing file is changed.

New files:

- `Tools/ShippingCoreFromM.lean` — the bridge and six re-derivations
- `Tools/ShippingCoreFromMPorts.lean` — four re-derivations
- `Tests/Compiler/CoreFromMAuditTest.lean` — the audit (throws)
- this note

## 1. What was duplicated

Round par/b-13 wrote `Tools/ShippingMemKidCore.lean` and
`Tools/ShippingMemKidPorts.lean` as scripted copies of 17 built `core_*`
theorems (suffix `M`), plus the new `core_callStmtM`. The script changed
three things: the name, `RealChild mref cref` ↦ `Kid mref cref`, and the
binder `hnomem`.

    Kid mref cref c y := memChild? c = some y ∨ (memChild? c = none ∧ RealChild mref cref c y)
    hnomem : ∀ c ∈ d.shape.insts, memChild? c.1 = none
    hfne   : d.shape.instFields ≠ []

The script treated `hnomem` in two different ways, and that is what decides
whether the old theorem is a corollary of the copy:

- **DROP** — the old statement already had `hfne`; the copy only loses
  `hnomem`. The copy is the more general theorem. Old = corollary.
- **REPLACE** — the old statement had NO `hfne`; the copy has `hfne` where
  `hnomem` was. The old statement also holds of the one-output closing
  (`instFields = []`, closed by `closeInsts`,
  `Tools/ShippingMachineEntry.lean:930`), where the copy says nothing. The
  two statements are INCOMPARABLE: old is not a corollary of the copy and
  the copy is not a corollary of old.

## 2. Inventory

Lines are of 8554bddb. "proof" = lines of the old proof body (after `:= by`).
`Kid` column: where the child predicate occurs in the statement (H =
hypothesis asked of every child, C = conclusion).

| # | old theorem (file:line) | `M` copy (file:line) | `hnomem` | `RealChild`→`Kid` | old proof | old ⇐ `M`? |
|---|---|---|---|---|---|---|
| 1 | `core_kids_facts` `ShippingChecksCore.lean:71` | `ShippingMemKidCore.lean:126` | REPLACED by `hfne` | C ×1 | 130 | **NO** — old has no `hfne`; its proof case-splits `instFields = []` (lines 155, 166) and uses `hnomem` once (216) |
| 2 | `core_raw_facts` `ShippingChecksRaw.lean:131` | `ShippingMemKidCore.lean:293` | DROPPED | none | 87 | yes — the `M` call, `hnomem` unused |
| 3 | `core_linkedWF` `ShippingLinkedFresh.lean:162` | `ShippingMemKidCore.lean:413` | REPLACED | none | 60 | **NO** — no `hfne`; `hnomem` only passed on to #1 (236) |
| 4 | `core_instOuts_not_assigned` `ShippingLinkedFresh.lean:243` | `ShippingMemKidCore.lean:494` | REPLACED | none | 2 | **NO** — no `hfne`; passes `hnomem` to #3 |
| 5 | `core_outsExtracted` `ShippingChecksOuts.lean:86` | `ShippingMemKidCore.lean:528` | DROPPED | H ×1 (`hkidP`) | 143 | yes — `hkidP` bridged |
| 6 | `core_callPorts` `ShippingChecksWidths.lean:104` | `ShippingMemKidCore.lean:708` | DROPPED | H ×1 (`hkidP`), C ×1 | 132 | yes — `hkidP` bridged, the conclusion's kid is real |
| 7 | `core_instOutWidthsOk` `ShippingChecksWidths.lean:271` | `ShippingMemKidCore.lean:876` | DROPPED | H ×2 (`hkidP`, `hkidW`) | 18 | yes |
| 8 | `core_hierGate` `ShippingChecksWidths.lean:365` | `ShippingMemKidCore.lean:927` | DROPPED | none | 33 | yes — `hnomem` unused |
| 9 | `core_runFacts` `ShippingChecksRunFacts.lean:42` | `ShippingMemKidCore.lean:988` | DROPPED | H ×2 | 15 | yes |
| 10 | `core_outsCheck_all_gate` `ShippingChecksCoreGate.lean:41` | `ShippingMemKidCore.lean:1043` | REPLACED | H ×2 | 23 | **NO** — no `hfne`; `hnomem` only passed to #1 (69) |
| 11 | `core_closed_typedIn` `ShippingClosedTyped.lean:95` | `ShippingMemKidPorts.lean:53` | REPLACED | none | 215 | **NO** — no `hfne`; `hnomem` only passed to #1 (117–118) |
| 12 | `core_clk` `ShippingCoreClk.lean:57` | `ShippingMemKidPorts.lean:300` | REPLACED | none | 98 | **NO** — no `hfne`. NEITHER proof uses its binder (`hnomem` in old, `hfne` in the copy: no occurrence in either body) — see 5.3 |
| 13 | `core_callConns` `ShippingPortsMatchRaw.lean:247` | `ShippingMemKidPorts.lean:430` | DROPPED | C ×2 | 155 | yes — both kids of the conclusion are real |
| 14 | `core_portsMatch_raw` `ShippingPortsMatchRaw.lean:441` | `ShippingMemKidPorts.lean:732` | DROPPED | H ×4 (`hkidW`, `hkidT`, `hkidIn`, `hkidClk`) | 56 | yes |
| 15 | `core_kids_self` `ShippingKidsSelf.lean:78` | `ShippingMemKidPorts.lean:841` | REPLACED | H ×1 | 42 | **NO** — no `hfne`; uses `hnomem` once (135) |
| 16 | `core_kidsPass_deep` `ShippingKidsSelf.lean:144` | `ShippingMemKidPorts.lean:909` | DROPPED | H ×1 (`hkidK`) | 27 | yes |
| 17 | `core_designCheck_run` `ShippingTextShipped.lean:131` | `ShippingMemKidPorts.lean:978` | DROPPED | H ×2 | 6 | yes |

Apart from the row's `hnomem` line and `Kid`, each pair of statements is
textually identical (checked by a line diff of the statement text after
substituting `Kid mref cref` ↦ `RealChild mref cref`; the only differing
line in every pair is the `hnomem` / `hfne` binder).

**10 corollaries** (#2, 5, 6, 7, 8, 9, 13, 14, 16, 17), **7 not** (#1, 3, 4,
10, 11, 12, 15).

### Why the bridge is short for the ten

Every child hypothesis and every child conclusion in these statements is
indexed by a call entry: `∀ k (hk : k < d.shape.insts.length) y, P (d.shape.insts[k]).1 y → …`.
Under `hnomem` the name `(d.shape.insts[k]).1` is not a memory placeholder,
so (`Kid.real`, already built) a kid there is a real child:

- a hypothesis asked of kids (`M`) is given by the old hypothesis asked of
  real children: `fun k hk y hy => hkidX k hk y (real_of_kid hnomem hk hy)`;
- a kid in the conclusion (`core_callPorts`, `core_callConns`) is turned
  back by the same lemma.

No statement quantifies a child predicate over an arbitrary name, so no
case needs more than `real_of_kid`.

### Why the seven are not corollaries

`hfne` is not implied by the old hypotheses (`ok`, `hbody`, `hC`, `hslots`,
`hdomB`, `hins`, `outTy`, `hnomem`, the run, `entry`, `closes`): `callsOk`
(`Tools/ShippingCallsShape.lean:106`) does not read `instFields`, and
`hins : insts ≠ []` holds of one-output shapes too. It is a genuinely
different case split, not a missing lemma.

Of the seven, only TWO read the child witness (#1 and #15: one `hnomem`
use each, at the place where the left case of `ChildrenReal` is refuted).
Four (#3, 4, 10, 11) only pass the binder on to #1. One (#12) does not use
it at all.

## 3. New statements

`Tools/ShippingCoreFromM.lean` (namespace `Tools.ShippingCoreFromM`):

- `kid_iff_real_of_nomem` — `memChild? c = none → (Kid mref cref c y ↔ RealChild mref cref c y)`
- `real_of_kid` — under `hnomem`, the kid of call entry `k` is a real child
- `kid_of_real` — the converse (not used by the re-derivations; for the
  integrator's replacement of consumers)
- `core_raw_facts_fromM`, `core_outsExtracted_fromM`, `core_callPorts_fromM`,
  `core_instOutWidthsOk_fromM`, `core_hierGate_fromM`, `core_runFacts_fromM`

`Tools/ShippingCoreFromMPorts.lean` (same namespace):

- `core_callConns_fromM`, `core_portsMatch_raw_fromM`,
  `core_kidsPass_deep_fromM`, `core_designCheck_run_fromM`

Each `_fromM` statement is the OLD statement, text copied by a script from
the old file (only the theorem's name changed; `core_designCheck_run`'s
`:=` became `:= by`). Proofs: one `exact` of the `M` theorem (eight), or
`intro` / `obtain` / `exact` around it (the two with a kid in the
conclusion). 44 proof lines in total for the ten.

The test `Tests/Compiler/CoreFromMAuditTest.lean` THROWS if

- a `_fromM` type is not `isDefEq` the old constant's type (also logs
  whether they are syntactically equal);
- a `_fromM` proof term names the old theorem (restatement);
- any of the 17 old, 17 `M`, 10 `_fromM`, 3 bridge constants is off
  standard axioms;
- the inventory's reason is not what the statements say: every old
  statement has a binder `hnomem`, no `M` statement has it, every `M`
  statement has `hfne`; a pair is listed as corollary iff the OLD statement
  has a binder `hfne`;
- the counts are not 10 and 7.

It logs the table (old name — T/F — lines of the old declaration from its
recorded range — lines of the re-derivation) and the totals.

## 4. Replacement proposal (NOT performed)

### 4.1 Old proofs that become corollaries

The ten of section 2. Proof lines today: 87 + 143 + 132 + 18 + 33 + 15 + 155 +
56 + 27 + 6 = **672**. Replaced by the 44 proof lines of the `_fromM` bodies
plus the bridge (about 20 lines, once): **about 610 lines removed**. The
statements, names and namespaces of the old theorems do not change, so no
consumer changes.

### 4.2 The import graph: there IS a cycle

Today (read from the `import` lines):

    ShippingMemKidCore  imports  ShippingChecksCore, ShippingChecksRaw, ShippingLinkedFresh,
                                 ShippingChecksOuts, ShippingChecksWidths,
                                 ShippingChecksRunFacts, ShippingChecksCoreGate
    ShippingMemKidPorts imports  ShippingMemKidCore, ShippingClosedTyped, ShippingCoreClk,
                                 ShippingPortsMatchRaw, ShippingKidsSelf, ShippingTextShipped

No old file imports an `M` file. The `M` files import the old ones because
the copied proofs use the old files' HELPER declarations (not the old
`core_*` theorems): e.g. `noSelfRead_of_feed`, `instNameOf_eq`
(`ShippingChecksRaw.lean:71–91`), `writes_sub_linked`, `instOuts_not_written`
(`ShippingLinkedFresh.lean:53–99`), `callStmtG_conn`, `callArgsOk`,
`callArgs_width` (`ShippingPortsMatchRaw.lean:88–205`),
`core_designCheck_rest2` (`ShippingTextShipped.lean:114`).

So "`core_raw_facts := core_raw_factsM …` inside `ShippingChecksRaw.lean`"
needs `ShippingChecksRaw` to import `ShippingMemKidCore`, which imports
`ShippingChecksRaw`: a cycle. The same for all ten.

### 4.3 How to break it — move the general theorem INTO the old file

The `M` proof calls `XM` exactly where the old proof calls `X`, and `X`'s
file is already imported by the old file (the old proof compiles). So each
`M` theorem can live in the old file directly above its old counterpart
with no new import between old files. Order:

1. New early file `Tools/ShippingKid.lean`: `Kid`, `kid_of`, `Kid.real`,
   `Kid.mem` (from `ShippingMemKidCore.lean:72–116`) and the bridge
   (`real_of_kid`, `kid_of_real`, `kid_iff_real_of_nomem`). It needs only
   `Tools.ShippingChildInv` (`RealChild`) and `Tools.ShippingMachineEntry`
   (`MemChildren`), both below `ShippingChecksCore` (its exact import list
   was not built). Keep the namespace
   `Tools.ShippingMemKid` so the five consumers
   (`ShippingMemKidFacts`, `ShippingMemClosesRun`, `ShippingMemClosesKids`,
   `ShippingMemOnly`, `Tests/Compiler/NoPortsMemSeqMemTest.lean`) need no
   rename.
2. In the old files, in the order of the existing DAG —
   `ShippingChecksCore` → `ShippingLinkedFresh`, `ShippingChecksRaw`,
   `ShippingChecksCoreGate`, `ShippingClosedTyped` → `ShippingChecksOuts` →
   `ShippingChecksWidths` → `ShippingChecksRunFacts` → `ShippingCoreClk`,
   `ShippingTextShipped` → `ShippingPortsMatchRaw` → `ShippingKidsSelf` —
   add `import Tools.ShippingKid`, paste the `M` theorem above the old one
   (in a `namespace Tools.ShippingMemKid … end` block, or renamed), and for
   the ten replace the old proof body by the `_fromM` body of this round.
   For the seven the old proof stays next to the `M` one (see 5).
   `core_callStmtM` goes to `ShippingPortsMatchRaw.lean`.
3. `ShippingMemKidCore.lean` / `ShippingMemKidPorts.lean` become import-only
   shims (or are deleted and the five consumers' imports updated; the two
   `lean_lib` entries with them).
4. `Tools/ShippingCoreFromM*.lean` and the audit test are deleted (their
   content is now the old theorems' proofs), or the test is kept with the
   pairs (old, `M`) only.

Alternative (more files, no edit inside proofs): split each old file into
`<F>Parts` (the helpers) and `<F>` (the `core_*` theorems), let the `M`
files import only `Parts`, and let `<F>` import the `M` file. No `M` proof
calls an old `core_*` theorem, so this works too, but it doubles the number
of files in the chain; 4.3 is preferred.

Risk of the replacement itself: each old file is rebuilt, and everything
above `ShippingChecksCore` with it (the whole check-free chain). Statements
unchanged, so no downstream proof should move.

## 5. The seven that stay duplicated — what would unify them (NOT written)

570 proof lines (130 + 60 + 2 + 23 + 215 + 98 + 42) remain twice after 4.

5.1 **One mode hypothesis.** A third statement with

    hmode : d.shape.instFields ≠ [] ∨ ∀ c ∈ d.shape.insts, memChild? c.1 = none

in place of the binder and `Kid` as the child predicate has BOTH existing
statements as corollaries (`Or.inl hfne` gives the `M` one; `Or.inr hnomem`
and `real_of_kid` give the old one). The proof differs from the `M` proof at
the one kind of place the script already isolated: `hMC` + `kid_of` becomes

    have hKid : (witness of ChildrenReal at k) → Kid … := by
      rcases hmode with hfne | hnomem
      · (hMC from the closing, then kid_of)          -- the M proof's lines
      · (refute the memory case by hnomem, Or.inr)    -- the old proof's lines

This is needed in #1 and #15 only; #3, 4, 10, 11 just pass `hmode` on.
It is a new proof text for six theorems (about 470 lines today), so it was
not written unbuilt in this round: a third unverified copy would add debt
before removing any. With the in-place move of 4.3 it is an EDIT of the
moved `M` proof (two places in #1, one in #15, the binder in the other
four), after which both the old and the `M` statement of all six are
short corollaries: one general proof (≈ 470 lines) where there are two
today, so about 410 further lines removed (470 minus ≈ 60 of corollaries).

5.2 Whether the old one-output half is still consumed was not read: if
every remaining caller of #1, 3, 4, 10, 11, 15 has `hfne` at hand, the old
statements could simply be retired instead (a decision about existing
statements, for the user).

5.3 **`core_clk`: a dead binder on both sides.** Neither proof body
mentions its binder (`hnomem` in `ShippingCoreClk.lean:57–173`, `hfne` in
`ShippingMemKidPorts.lean:300–416`). The statement without either binder is
proved by the same text and has both as one-line corollaries (98 lines
removed). It needs a new name or a changed statement of an existing
theorem, hence not done here.

## 6. Lines

| | lines |
|---|---|
| removed by replacing the ten old proofs (4.1) | ≈ 610 |
| removed additionally by 5.1 + 5.3 (not written) | ≈ 410 + 98 |
| added this round (two `Tools` files, test, note) | 538 + 169 + this note |
| removed again in step 4 of 4.3 | the 538 + (optionally) the test |

## 7. Integration

lakefile lines (the integrator adds them):

    lean_lib «Tools.ShippingCoreFromM» where
      roots := #[`Tools.ShippingCoreFromM]

    lean_lib «Tools.ShippingCoreFromMPorts» where
      roots := #[`Tools.ShippingCoreFromMPorts]

`Tests/AllTests.lean`: `import Tests.Compiler.CoreFromMAuditTest`.

Build order: `Tools.ShippingCoreFromM` → `Tools.ShippingCoreFromMPorts` →
`Tests.Compiler.CoreFromMAuditTest`. All three sit on top of the built
`ShippingMemKidCore` / `ShippingMemKidPorts`; nothing below them is rebuilt.

What may not elaborate, most likely first:

1. `Tests/Compiler/CoreFromMAuditTest.lean` — Meta API details:
   `Lean.findDeclarationRanges?` (first use in this repository),
   `binderNames` by structural recursion on `Expr`, the pattern
   `Lean.ConstantInfo.thmInfo v`, `indentD` / `MessageData.joinSep`.
2. The same test at RUN time: the binder-name checks assume the theorem
   types keep the source binder names `hnomem` / `hfne`; `isDefEq` assumes
   the copied statement text resolves to the same constants in the new
   namespace (same `open` lines as the `M` file, which built with that
   text).
3. `core_callConns_fromM`, `core_callPorts_fromM` — the `obtain` / `rcases`
   patterns against the `M` conclusion's nesting.
4. The lambdas `fun k hk y hy => hkidX k hk y (real_of_kid hnomem hk hy)` —
   unification of `(?shape.insts[k]).1` (fixed by `hnomem` first; the index
   proof differs only up to proof irrelevance).
5. `kid_iff_real_of_nomem`, `kid_of_real` — `Or.inr` against the unfolded
   `Kid` (same pattern as the built `kid_of`).
6. Linter only: unused `hnomem` in `core_raw_facts_fromM`,
   `core_hierGate_fromM` (the binder is part of the old statement).

## Build record (integrator, 2026-10-13)

Built on poc 8554bddb + this round's files (worker files unchanged): `Tools.ShippingCoreFromM`,
`Tools.ShippingCoreFromMPorts`, `Tests.Compiler.CoreFromMAuditTest` (in AllTests). No endpoint changes and
NOTHING is replaced: the old theorems and the `M` copies are both still there. What is established is that
10 of the 17 old `core_*` statements are re-derived from their `M` copies with statements `isDefEq` the old
ones (standard axioms, no proof naming the old theorem); 7 are not corollaries (the old statement has no
`hfne` and also covers `instFields = []`). The replacement of old proofs (import restructuring, §proposal)
is not done.

```
20261013-064839-b16-tests: lake build Tools.ShippingCoreFromM Tools.ShippingCoreFromMPorts Tests.Compiler.CoreFromMAuditTest 
result=success
exit=0
memory_peak_file=804614144
Build completed successfully (464 jobs).
20261013-064926-b16-alltests: lake build Tests.AllTests 
result=success
exit=0
memory_peak_file=443088896
Build completed successfully (1230 jobs).
info: Tests/Compiler/CoreFromMAuditTest.lean:97:0: COREFROMM AUDIT TABLE (old name — re-derived — lines):
  Tools.ShippingChecksCore.core_kids_facts — re-derived F (old statement: hnomem, NO hfne; Tools.ShippingMemKid.core_kids_factsM: hfne in its place — the one-output closing instFields = [] is in the old statement only) — old declaration 155 lines
  Tools.ShippingChecksRaw.core_raw_facts — re-derived T (Tools.ShippingCoreFromM.core_raw_facts_fromM; statement defEq, syntactically equal: true; proof term names Tools.ShippingMemKid.core_raw_factsM: true) — old declaration 113 lines — re-derivation 25 lines
  Tools.ShippingLinkedFresh.core_linkedWF — re-derived F (old statement: hnomem, NO hfne; Tools.ShippingMemKid.core_linkedWFM: hfne in its place — the one-output closing instFields = [] is in the old statement only) — old declaration 81 lines
  Tools.ShippingLinkedFresh.core_instOuts_not_assigned — re-derived F (old statement: hnomem, NO hfne; Tools.ShippingMemKid.core_instOuts_not_assignedM: hfne in its place — the one-output closing instFields = [] is in the old statement only) — old declaration 23 lines
  Tools.ShippingChecksOuts.core_outsExtracted — re-derived T (Tools.ShippingCoreFromM.core_outsExtracted_fromM; statement defEq, syntactically equal: true; proof term names Tools.ShippingMemKid.core_outsExtractedM: true) — old declaration 170 lines — re-derivation 28 lines
  Tools.ShippingChecksWidths.core_callPorts — re-derived T (Tools.ShippingCoreFromM.core_callPorts_fromM; statement defEq, syntactically equal: true; proof term names Tools.ShippingMemKid.core_callPortsM: true) — old declaration 166 lines — re-derivation 40 lines
  Tools.ShippingChecksWidths.core_instOutWidthsOk — re-derived T (Tools.ShippingCoreFromM.core_instOutWidthsOk_fromM; statement defEq, syntactically equal: true; proof term names Tools.ShippingMemKid.core_instOutWidthsOkM: true) — old declaration 50 lines — re-derivation 35 lines
  Tools.ShippingChecksWidths.core_hierGate — re-derived T (Tools.ShippingCoreFromM.core_hierGate_fromM; statement defEq, syntactically equal: true; proof term names Tools.ShippingMemKid.core_hierGateM: true) — old declaration 55 lines — re-derivation 22 lines
  Tools.ShippingChecksRunFacts.core_runFacts — re-derived T (Tools.ShippingCoreFromM.core_runFacts_fromM; statement defEq, syntactically equal: true; proof term names Tools.ShippingMemKid.core_runFactsM: true) — old declaration 46 lines — re-derivation 35 lines
  Tools.ShippingChecksCoreGate.core_outsCheck_all_gate — re-derived F (old statement: hnomem, NO hfne; Tools.ShippingMemKid.core_outsCheck_all_gateM: hfne in its place — the one-output closing instFields = [] is in the old statement only) — old declaration 53 lines
  Tools.ShippingClosedTyped.core_closed_typedIn — re-derived F (old statement: hnomem, NO hfne; Tools.ShippingMemKid.core_closed_typedInM: hfne in its place — the one-output closing instFields = [] is in the old statement only) — old declaration 238 lines
  Tools.ShippingCoreClk.core_clk — re-derived F (old statement: hnomem, NO hfne; Tools.ShippingMemKid.core_clkM: hfne in its place — the one-output closing instFields = [] is in the old statement only) — old declaration 119 lines
  Tools.ShippingPortsMatchRaw.core_callConns — re-derived T (Tools.ShippingCoreFromM.core_callConns_fromM; statement defEq, syntactically equal: true; proof term names Tools.ShippingMemKid.core_callConnsM: true) — old declaration 195 lines — re-derivation 47 lines
  Tools.ShippingPortsMatchRaw.core_portsMatch_raw — re-derived T (Tools.ShippingCoreFromM.core_portsMatch_raw_fromM; statement defEq, syntactically equal: true; proof term names Tools.ShippingMemKid.core_portsMatch_rawM: true) — old declaration 100 lines — re-derivation 52 lines
  Tools.ShippingKidsSelf.core_kids_self — re-derived F (old statement: hnomem, NO hfne; Tools.ShippingMemKid.core_kids_selfM: hfne in its place — the one-output closing instFields = [] is in the old statement only) — old declaration 62 lines
  Tools.ShippingKidsSelf.core_kidsPass_deep — re-derived T (Tools.ShippingCoreFromM.core_kidsPass_deep_fromM; statement defEq, syntactically equal: true; proof term names Tools.ShippingMemKid.core_kidsPass_deepM: true) — old declaration 60 lines — re-derivation 34 lines
  Tools.ShippingTextShipped.core_designCheck_run — re-derived T (Tools.ShippingCoreFromM.core_designCheck_run_fromM; statement defEq, syntactically equal: true; proof term names Tools.ShippingMemKid.core_designCheck_runM: true) — old declaration 46 lines — re-derivation 42 lines
info: Tests/Compiler/CoreFromMAuditTest.lean:97:0: COREFROMM AUDIT: 10 of 17 old core_* statements re-derived from their M copies (statements defEq the old ones, standard axioms, no proof names the old theorem); 7 are NOT corollaries (old statement without hfne) and have no _fromM. Declaration lines, statement included: the 10 old declarations 1001, their re-derivations 360 (difference 641: what a replacement of the old proofs would remove, before import restructuring); the 7 old declarations that stay duplicated: 731. NOTHING is replaced: the old theorems are unchanged and no declaration uses a _fromM theorem.
```
