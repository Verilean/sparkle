# Contributing to the verified-synthesis research

This page is for people who want to add a lemma, an entry or a circuit to the proof side of
Sparkle. For adding an ordinary IP to the library (simulation tests, the Verilog check, the
CI listing), read the root [CONTRIBUTING.md](../../CONTRIBUTING.md). Start with the
[overview](README.md) and pick a task from [OpenProblems.md](OpenProblems.md). All file
paths below are paths in the reader's checkout named in the
[snapshot box](README.md#snapshot-box): the branch `docs/research-release` (later the merge
commit), which holds the code, these pages, the scripts and the example. The commit `2bcf256b`
holds only the code and cannot run these commands.

## Build

```bash
git clone https://github.com/Verilean/sparkle && cd sparkle
git checkout docs/research-release   # the reader's checkout of the snapshot box (code + pages + example)
lake build Tools.VedU1Entry                                     # the verified entries
```

The Lean version is in `lean-toolchain` (install it with `elan`). The verified tools and their
checks are separate `lean_lib` targets of `lakefile.lean`. They are **not** in the default build
or in the `Sparkle` umbrella, so build each by name. The first build also compiles the Sparkle
library. On a clean 4-vCPU runner this was 83 s for the library, plus 60 s for `Tools.VedU1Entry`
([BuildAndCI.md](BuildAndCI.md)).

## Run one check

A check is a Lean file whose build fails if any expected result changes.

```bash
lake build Tests.Ved.U1EntryCheck          # basic entry: accepted examples, refused controls
lake build Tests.Ved.U2HierRegCheck        # a parent with registers and instances
lake build Tests.Ved.WriteCheckedCheck     # the writer receives the checked design
python3 -I scripts/research/coverage_table.py --check    # generated tables match their data
python3 -I scripts/research/check_links.py               # links and anchors in these pages
```

To see the output of one command on your own file instead of a whole check, build the entry
once and run the file (`docs/research/examples/Delay8.lean` is a file of this kind):

```bash
lake build Tools.VedU1Entry
lake env lean docs/research/examples/Delay8.lean ; echo "exit $?"   # expected: the OK report, the axiom list, exit 0
```

The file contains one refused circuit on purpose; `#guard_msgs (error)` pins that refusal, so
the exit status is 0 and the refusal prints nothing. A different exit status or a message diff
means the result changed.

## Where things live

| What | Path |
|---|---|
| The statement of the per-circuit theorem, the order-free lemmas | `Tools/VedU1Contract.lean` |
| Registers, loops with several registers | `Tools/VedU1Entry.lean`, `Tools/VedU1Loop.lean` |
| Shared terms (keeping sharing in big circuits) | `Tools/VedU1WireShare.lean`, `Tools/VedU1Wire.lean` |
| The deep route and its general theorem | `Tools/DeepElab.lean`, `Tools/VedU1Deep.lean` |
| Packed ports | `Tools/VedU1Packed.lean` |
| Memories | `Tools/VedMem.lean` |
| Hierarchies: statements and composition lemmas | `Tools/VedU2HierStmt.lean`, `Tools/VedU2HierReg.lean`, `Tools/VedU1HierComp.lean`, `Tools/VedU2Hier*.lean` |
| The checked writer | `Tools/VedWriteChecked.lean` |
| Order-free meaning of an IR body | `Sparkle/IR/ReorderInvariance.lean` |
| The strict axiom audit | `Tools/VedStrictAudit.lean` |
| Checks: accepted examples and refusal controls | `Tests/Ved/*Check.lean` |
| The 327 command rows and their data | `docs/research/data/`, generator `scripts/research/coverage_table.py` |

A **new lemma** goes in the file of the statement it serves (for a lemma about shared terms,
next to `Tools/VedU1WireShare.lean`; for a hierarchy lemma, beside the composition lemmas). A
**new statement** (a new kind of module the entry may accept) gets its own file under `Tools/`
and is imported by the entry that uses it.

## How a new lemma or route is checked

Every new lemma, statement or route comes with a **check file** `Tests/Ved/<Name>Check.lean`
that has two kinds of cases, so that acceptance is never vacuous:

1. **Accept cases.** A real circuit (or a small one shaped like a refused real row) is run through
   the entry. The check pins the report line with `#guard_msgs`, rebuilds the registered
   theorem's expected type by hand and compares it, and checks that its axioms are exactly the
   three standard ones (`propext`, `Classical.choice`, `Quot.sound`).
2. **Refuse controls.** Mutants of the returned module or of the facts, each of which must be
   refused at a named stage, after which the checker's generated constants are absent from the environment (a check of those names, not a claim that synthesis is rolled back): one changed constant or next
   value, two same-width registers swapped, another circuit's module or facts. The existing
   checks define a small helper `expectRefused stage absent act` for this (see the top of
   `Tests/Ved/U1EntryCheck.lean`; each check file carries its own copy).

Then register the check in two places, as the existing ones are:

```lean
-- lakefile.lean
lean_lib «Tests.Ved.MyNewCheck» where
  roots := #[`Tests.Ved.MyNewCheck]
```

and a step in `.github/workflows/ved.yml` (job `ved-pr` for a representative check, job
`ved-full` for all): `run: lake build Tests.Ved.MyNewCheck`.

Rules of the house: never raise a budget to make a case pass (options that change a limit are
floors, behind an option, with the default unchanged); report heartbeats for budget walls, and
elaboration time, kernel time and peak memory as separate numbers; do not label a local success
as progress on a goal.

## What a pull request should contain

* The lemma or statement, with its Lean proof, and **no new axiom and no `sorry`**. The strict audit
  must still pass.
* The check file (accept and refuse cases) and its two registrations.
* The command lines you ran and their output: the `lake build` of your check and of the existing
  ones you could have affected (`Tests.Ved.U1EntryCheck`, `Tests.Ved.U2HierRegCheck`).
* If a row of the 327 should change status: the measurement it comes from, and a regenerated
  table (`python3 -I scripts/research/coverage_table.py`, then `--check` exits 0). A change that
  alters what a route accepts does not inherit the old numbers; say which rows you re-measured.
* If you touch the pages of this directory: `python3 -I scripts/research/check_links.py` exits 0.
* A paragraph in plain words: what is now proved, on which artifact, and what is still not. If
  something moves, update the relevant sentence in [PerCircuitVerification.md](PerCircuitVerification.md)
  and the problem in [OpenProblems.md](OpenProblems.md).

To discuss a task before starting, open an issue with the commit you ran and the output you saw.
