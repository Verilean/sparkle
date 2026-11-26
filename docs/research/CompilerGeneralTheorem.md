# The general theorem about the compiler: what was tried, what is proved, what is missing

This is the **second, separate effort** of the project. The per-circuit results of
[PerCircuitVerification.md](PerCircuitVerification.md) do not depend on anything here, and
nothing there should be read as a conclusion of this page.

**In one paragraph.** The per-circuit route proves, one circuit at a time, that the module the
compiler returned computes what the Lean function says. The effort on this page asked for
more: *one* theorem that holds for **every** source the old shipping compiler accepts. We
proved theorems of that kind only **under conditions**: they assume facts about the Lean
runtime in which the compiler runs, and about each input, that nobody has been able to supply.
So there is **no unconditional soundness theorem** of the old compiler. The effort is paused,
with its results and its negative results preserved.

## 1. What was attempted

The goal, stated in words: for every source in the Sparkle DSL and every successful run of the
real compiler entry on it that returns a design `D`:

1. the top module's outputs equal, cycle by cycle, the values of the source streams;
2. for every length `T` a run of the generated hardware exists from an admissible start;
3. every such run has those outputs.

It covers every input the entry accepts today, not a subset. The plan split it into three
obligations: a *general theorem* over a formal copy of the source language; a *reflection* step
that links a particular Lean definition to its formal copy (the kernel can check this for one
definition at a time; the statement "for every definition in every environment" was not
formalised in this effort, so it stayed an unproved premise); and *coverage* (the reader of the source, the data
checks, the generators are total and correct). The audit of the design records the gap this
leaves: the quantification "for every source and run" was not yet a Lean statement.

## 2. What was learned

The following findings are the reason for the pause. "Refuted" means a kernel-checked negative
result; "not supplied" means neither proved nor refuted.

1. **A universal assumption about the source meaning made the goal refutable.** Requiring
   functionality for an arbitrary relation between sources and meanings makes the outer
   hypotheses of the goal inconsistent (refuted). Functionality, type soundness and existence of
   a meaning are separate obligations.
2. **Runs and environments were not tied to one run.** A world fixed to some value was not shown
   to belong to the chain of the run being analysed. Negative controls were added.
3. **No equations for the runtime primitives were found in the range investigated.** The
   compiler runs in `IO` and `ST` with opaque primitives (reading a reference, getting an output
   stream). In the investigated range the kernel and the API gave no equations for them, so the
   facts the proof needs (the laws about references, and the cell facts) were not supplied.
   This is an *unproved correspondence between a model and the implementation*. It is **not** a
   proof that such facts cannot be proved, and not a statement about runtimes in general.
4. **An explicit-state model did not remove the gap.** The first environment correspondence was
   inconsistent and the first "quiet" relation was trivially true (both refuted). A toy model
   satisfies the laws; correspondence to the real runtime is not proved. A full port was
   estimated at 2,500 to 4,000 lines and put on hold.
5. **The general substitution lemma was never supplied.** A negative control showed that the
   formal substitution does not commute with the two reduction operations (`substS` against
   `betaS` and `instForallS`); that points to a *counterexample candidate* for the lemma. No
   counterexample to the lemma itself was constructed: the record's class is "not supplied
   (counterexample candidate)", not "false".
6. **Sharing was lost** when an intermediate expression was copied as a tree (a 28 GB
   out-of-memory failure), and one kernel time was mis-measured (an asynchronous declaration time
   had been reported as kernel time).
7. **Checker and generator bugs** (names of bound variables confused, instances not checked,
   signatures compared by name). Mutant counts do not prove a checker.
8. **Observed agreement was nearly taken as a proved bridge** between a candidate and the real
   optimiser output. Observations are not theorems.
9. **Local checks accumulated without reducing the missing premises.** Many checks and
   circuit-specific theorems were added without connecting the original definition to the final
   conclusion.

**Lessons recorded.** Test a universal assumption on extreme cases and on non-vacuous witnesses
before freezing a statement; establish a jointly satisfiable model *and* a bridge to a real run
before long conditional assembly; fix what each unit hands to the final conclusion; report local
acceptances apart from progress on the goal; never present the theorem about the formal
language as the soundness of the whole compiler.

## 3. What is proved

All of these are Lean theorems on public branches (the reproduction box at the end names them).
"Conditional" means proved under premises that are not discharged for the real runtime.

**Class-general conditional theorems (the strongest results).** For all designs of two classes
(a top module, paired wrappers and **one shared leaf module**, depth two; the two classes
differ in the shape of the leaf, one with a memory), for all inputs, run lengths and start states, the shipped
result is correct (`memSharedLeaf_ships`, `qSharedLeaf_ships`). They carry 19 premises each:
runtime laws, machine reflection and closing premises. They stop at the run of the IR, not at the
SystemVerilog text; membership of a concrete design in the class is itself conditional; a
census of 20 shape-only candidates found no real IP as a top.

**Closing lemmas for the machine route** (`machine_ships_checked`, `closeInstsG_of_facts`, the
`closeLets_*` family, `machineClosesAt_of_seqKids`, `machineClosesAt_of_kidsD`): they close a run
of the machine given per-declaration data checks; reflection remains a premise.

**Smaller shipping results**: `memParent_ships` (takes the bundle of runtime laws),
`oneOut_topShips`, `readerTrace_final`; the step statement itself is not proved, only its cases.

**A validator for checked entries.** `checkComb_sound` and `ofData_sound` are general.
`checkData_sound` and `certifiedEntryC_sound` are general up to an intermediate meaning; the
link from that meaning to the original declaration is **not** supplied.

**Negative results, kept on purpose.** `cvTop_not_functional` and `fgG_refutes_outer`
(finding 1), `envCorr_inconsistent` and `oldQuietR_eq_true` (finding 4).

**The pilot.** The one worked case, a PCIe output-byte circuit of a trading design (the theorem
`synth_hftPcieOutByte_finalOffCombined11`), was fixed to one root. It still has nine premises
besides the antecedent of a successful run, all unsupplied.

## 4. What is missing, and why

| Missing | In plain words | Status |
|---|---|---|
| Reference laws for the runtime (`RefLaws`, `ChildLaws`) | what reading and writing a reference cell does | never proved; the first frame law was refuted and replaced |
| Operation and telescope laws (`RefLawsAOps`, `RefLawsATele`) | quiet, diagnostics, frame, exception, cache and depth sets | fit to the runtime and joint satisfiability **open** |
| Memoisation and overall laws (`MemoLaws`, `Laws`) | cache behaviour | not supplied |
| Cell facts (`CellPrem`) | read-world, set-frame, set/get | supply stopped at the first read-world and at the diagnostic law |
| Reflection for all declarations (`ReflectsAll`) | each declaration equals its formal copy | not supplied in general |
| Program lookup (`Pk`) | finding a program by name | has no Lean definition |

**Why.** See finding 3: no model-to-implementation correspondence was proved. Observing that
a reference value did not change in a real run does not prove the law for all worlds, nor the joint
satisfiability of the laws and the cell facts. A bundle with "quiet = False" was built but is not
a non-vacuous witness (for it, the premise about a run is false).

## 5. The counts, in words

The earlier summaries speak of two numbers. Both are **counts of rows in premise tables, not
counts of Lean binders**, and neither measures proof progress.

* **75 of the 110 recorded premises remain unproved** (the final-goal premise table, "FG 75"). The 110
  is itself 146 first-stage blocks minus 36 duplicates that were merged. Of the 75 open rows, 54 are
  leaves and 21 are not. The change from 110 to 75 is a net reduction of 35 rows made of: 31 removed
  by proof (12 of them conditional on a fixed carrier, a fixed scope or a changed statement), 2
  unneeded binders removed, 2 duplicates merged, 6 non-leaf replacements, 1 removed by a counting
  rule, and **7 premises added**: `110 − 31 − 2 − 2 − 6 − 1 + 7 = 75`. The ledger itself says that 10
  of the removals are *not* proof progress (the two merges, the six replacements, one unneeded
  non-leaf binder and the counting rule). The often-quoted "from about 100 to 75" is not the
  record: the recorded start is 146 blocks (110 after merging).
* **57 premises remain on the machine route alone** (the "T1" table): 62 − 10 + 5 = 57 (10
  removals, 5 additions, and 5 further rows replaced one for one). This is explicitly **not** the
  final goal: it is the machine route only, conditional on its own premises (reach facts, data
  checks, decodings). It has been 57 since the beginning of November 2026.

The count did not move over the last stretch because local checks and circuit-specific theorems
accumulated without removing rows (finding 9).

## 6. What is kept, and when the effort could resume

**Kept**: the existing run proofs, the functionality of the source carrier, the lemmas connecting
the same run and the same artifact, the general combinational validator, the input boundary and
hierarchy checks, the counterexamples and the negative controls.

**Why paused.** The maintainers decided to preserve the reached state, not to count the goal as
complete, and to move the main line of development to extending the per-circuit route. The premises
that were not proved (the runtime laws `Laws`, the cell facts `CellPrem` and the rest of the
open rows) **remain as unsupplied assumptions**. They were not discharged and were not counted
as done. The correspondence boundary to the real runtime (`Corr`) was **not adopted** as an
assumption either, and **no premise was added to the trusted base** by this decision; the state
is "paused with the premises open". (The retrospective's first paragraph can be read as
moving them to a trusted side; the reconciled record is the one stated here.)

**Restart condition.** The effort resumes only if three things become concrete: which of the 75
open rows can really be removed; how the runtime boundary is handled (the laws and cell facts, or
a different boundary); and how the work connects to the final statement. Not every row is an
opaque-IO problem; do not classify them all so. A restart separates approved commits from
unaccepted work. The concrete task is problem 6 of
[OpenProblems.md](OpenProblems.md#6-the-general-theorem-a-witness-for-the-runtime-laws).

## 7. Statements in older documents that must not be read as unconditional soundness

All on a public design branch (see the box below); none of them is a claim about the whole
compiler:

| Document and passage | How to read it |
|---|---|
| "Existing compiler: success implies semantic preservation" (title of the soundness note) | a target specification, not a proved theorem |
| "The CompCert-style theorems … prove compiled artifacts…" (trust-base note, section 0) | theorems about artifacts under the gate, and premises the note then lists as retained |
| Milestones S0 to S2 marked "Done" | fragments only (for example the first covers inputs, constants, six basic operations and same-width shifts) |
| `Machine.compileChecked_sound` in the certified-acceptance note | a separate typed compiler, not the shipping one |
| The audit's gap about "for every source and run" | per-endpoint; this quantification is not a Lean statement |

Compare the per-circuit route: its guarantee is *per circuit and per instance*, a theorem about
the module the compiler returned in one run, or nothing.

## Reproduction box (branches and commits)

This is the one place in the page that lists commits. The code is **not** on `main` and not in
the release snapshot; it is on public branches:

| Branch | Commit | What it holds |
|---|---|---|
| `par/fgc-retro` | `7423e4e1` | the reconciled retrospective `docs/FG-RETROSPECTIVE-2026-11-08.md` (in Japanese; this page restates it, including its Appendices A, B and C) and the Lean files named above (`Tests/Compiler/C4ComposedTest.lean`, `Tests/Compiler/QFinalTest.lean`, `Tools/ShippingMachineShipping.lean`, `Tools/ShippingCallsAssemblyG.lean`, `Tools/ShippingGen2*.lean`, `Tools/ShippingFGCircuitS3*.lean`, `Tools/ShippingGen5SM1.lean`: the premise statement `FGLedgerPremisesStmtH` is a `def : Prop` and is **not proved**) |
| `par/fg-ledger-sync` | `8649968e` | the 110-row premise table `scripts/gen2/PREMISE_LEDGER.md`, section 8.2 (latest version, section 12.24) |
| `poc/roundtrip-proof` | `09621708` | the design notes of the shipping compiler (`docs/ShippingCompiler-*.md`) |
| `par/cvtop` | `40b176fe` | one refutation (`Tests/Gen5/CVTopCheck.lean`) |

The machine-route table (62 → 57) lived on a branch that is **not** on the public remote
(`par/t1-ledger-sync`, `d91bab13`), and one more branch with ledger material is not public;
neither is relied on here beyond the counts above. To rebuild any named file, check out the
branch in a separate worktree and build the target of the same name
([appendix C](appendix/C-Reproduction.md)); this was not run for this page.
