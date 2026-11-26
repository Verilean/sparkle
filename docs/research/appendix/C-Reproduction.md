# Appendix C: reproduction

[Back to the research README](../README.md). All refs below are public refs of the repository
(`https://github.com/Verilean/sparkle`) and no step needs a private path.

**What can be reproduced from public steps today.**

| Task | Public steps only? |
|---|---|
| Re-run the per-circuit checks and the example | **Yes**, in the reader's checkout (section "The reader's checkout") |
| Regenerate the coverage tables and the link check from the committed data | **Yes**, same checkout |
| Re-measure the 327 rows | Yes in principle with the public harness branch (separate worktree, below); **not tested** here, and it takes hours |
| Regenerate the ledger (`ledger.tsv`) from the measurement results | **No, not with public steps today**: see "Regenerate the TSV from a measurement" |

## Toolchain

* Lean `leanprover/lean4:v4.32.1` (file `lean-toolchain`), installed with `elan`; Lake from the
  same toolchain. Build and cache details are the subject of [BuildAndCI.md](../BuildAndCI.md).
* The VED tools and their checks are `lean_lib` targets that are **not** in the default build or
  in the `Sparkle` umbrella; build them by name.

## The reader's checkout

There are two kinds of commit; only the first is a place to work.

* **The reader's checkout**: the branch `docs/research-release` (after the pull request is
  merged: the merge commit on `main`, or the release tag if one is made). It has the code, these
  pages, `scripts/research/` and `docs/research/examples/`. Every short procedure in this
  directory (CONTRIBUTING-research, OpenProblems, this appendix up to the TSV section) starts here.
* **Provenance only**: the code SHA `2bcf256b` (branch `ved/consolidated-1`, the code the numbers
  describe; it has no `docs/research/`, no `scripts/research/`) and the measured SHA `fb7124fc`
  (code plus the harness). `git diff --stat 2bcf256b <reader's checkout>` shows only `docs/`,
  `scripts/research/`, `.github/workflows/research-ux.yml` (the build-time measurement, run only
  on request), `README.md` and `CONTRIBUTING.md`.

```bash
git clone https://github.com/Verilean/sparkle && cd sparkle
git checkout docs/research-release
```

## Run the per-circuit checks

Each target is a file of accepted examples and refusal controls; a build that exits 0 means
every positive was accepted with the exact statement and the standard axioms, and every control
was refused.

```bash
lake build Tests.Ved.U1EntryCheck       # delay8 and friends; mutants refused
lake build Tests.Ved.U1MultiRegCheck    # several registers, Bool inputs
lake build Tests.Ved.U1MultiLoopCheck   # Signal.loop registers on real IP declarations
lake build Tests.Ved.U2HierRegCheck     # hierarchy with registers
lake build Tests.Ved.WriteCheckedCheck  # #ved_write_checked, byte comparison
```

Expected output: no error. For this page we ran only the example file (`lake build Tools.VedU1Entry`,
then `lake env lean docs/research/examples/Delay8.lean`, exit 0).
The five check targets above were **not** re-run for this page; the CI workflows of the pull request have their own results, listed per workflow in
[BuildAndCI.md](../BuildAndCI.md) (`ved-full` was skipped on the head of #163, so CI is not a blanket confirmation; see [D-Evidence.md](D-Evidence.md)). Times and memory are the subject of [BuildAndCI.md](../BuildAndCI.md).

## Regenerate the coverage table from the committed data

```bash
python3 -I scripts/research/coverage_table.py            # rewrites Coverage327.md, appendix/E and appendix/F
python3 -I scripts/research/coverage_table.py --check    # exit 1 if the file differs
python3 -I scripts/research/check_links.py               # relative links and anchors
```

The table's counts are computed from `docs/research/data/coverage-327.tsv`; they must be
243 / 168 / 75 (strict, real-IP strict, regression strict) with 10 unmeasured rows listed.

## Regenerate the TSV from a measurement

The 327 rows are measured by the harness on the public branch `meas/ved-pr16-fb71`
(`fb7124fc` = `2bcf256b` plus the harness under `scripts/ved/`, marked "MEASUREMENT ONLY, never for
main"):

```bash
git fetch origin meas/ved-pr16-fb71
git worktree add ../sparkle-meas fb7124fc && cd ../sparkle-meas   # a separate worktree, not the reader's checkout
# after building Tools.VedU1Entry Tools.VedU1Deep Tools.VedStrictAudit (and the other entries):
scripts/ved/u1_full.sh rows ROWS.txt OUT    # lines "ROW ROUTE"; routes u1 u1_deep u1_deep_ns u1_hier u1_packed u2_hier u1_mem_packed
```

The harness reads its Lean command from `U1_LEAN`, which defaults to the maintainers' cluster
wrapper (`kjob lake env lean`); for a plain checkout set `U1_LEAN="lake env lean"`. This
substitution was **not tested** here. A full measurement is 327 rows × 7 routes, each case in its
own process with a time limit (default 1800 s).

**The ledger cannot be regenerated from public steps today.** The per-row ledger (`ledger.tsv`)
was produced from the measurement results by the ledger generator `gen_ledger.py` (sha256
`6eb49c7ec93ac58f4c57fd864652e069e65ff8da8b12725b34935f71d0a1d5dd`, the version used for the
ledger `pr16-fb71`). It is **not published**, for two reasons. (1) It has the maintainers'
workspace layout built in (a result tree under `~/git/workspaces/…`, the baseline results of the
earlier candidate `d331ff24` and a history table), so it is not a self-contained script. (2) Its
inputs are the per-run result files with the scheduler job identities of the maintainers'
cluster, and those result files are not public either. Publishing the generator alone would not
make the ledger reproducible, so we did not. What is public is the **committed data**:
`docs/research/data/coverage-327.tsv`, which the tables are regenerated from, and
`scripts/research/ledger_to_tsv.py LEDGER_DIR OUT.tsv`, which turns a generator output
(`ledger.tsv`) into that TSV. A reader can therefore verify that the tables follow the data,
and re-measure rows with the harness, but cannot independently rebuild the approved ledger;
whoever needs that should ask the maintainers for the generator and the result files.

## Checks of the general-theorem work

The Lean files named in [CompilerGeneralTheorem.md](../CompilerGeneralTheorem.md) are on
`par/fgc-retro` (`7423e4e1`); check out that ref in a separate worktree and build the named
`Tools/Shipping*` and `Tests/Compiler/*` targets with the lake target of the same name. Not run
here.
