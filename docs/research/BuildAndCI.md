# Build time and CI

This page answers two questions for a new user of the research release: what you have to build
and how long you wait, and how the repository's CI is organised. All times come from runs whose
ID is given. Each CI number is the wall time of one job on a shared GitHub runner, for that
job's scope; none of them is the time a user's own build takes.

Revisions: the release candidate is the code at `2bcf256b`; the baseline is `main` before it
(`6c29b9b8`).

## 1. What you build

Start from the reader's checkout of the [snapshot box](README.md#snapshot-box). Until the pull
request is merged, that is the branch `docs/research-release`. A plain clone gives you `main`,
which does not contain the release.

```text
git clone https://github.com/Verilean/sparkle.git && cd sparkle
git checkout docs/research-release  # the reader's checkout (see the snapshot box)
lake build                          # the only default target: the `sparkle` executable
```

The only default target is the executable `sparkle` of `lakefile.lean` (`Main.lean`, which
imports `Sparkle`). Building it compiles its import closure, the Sparkle library: 47 modules
including `Main`, the same list at the baseline and at the release candidate. It does **not** build the verification commands, the IP
libraries, the CI checks, the benchmarks or the 327-command measurements. These are separate
targets that you build by name:

```text
lake build Tools.VedU1Entry         # #ved_u1: per-circuit proof of a flat circuit (tutorial Ch07c)
lake build Tools.VedU1Deep          # #ved_u1_deep, loop and packed-state routes
lake build Tools.VedU2HierRegEntry  # #ved_u2_hier: hierarchical designs
lake build IP.Crypto.Keccak256HW    # one real IP library, to run an entry on
```

How this was checked: a scan of the `import` lines from each root, at both revisions. Results:

- The closure of `Sparkle` contains no module under `Tools`, `Tests`, `IP` or `bench`.
- The entry libraries import none of the checks, IP libraries or benchmarks.
- `lake test` (481 tests) contains no VED check.

No public theorem was moved out of a target to make a build faster. The statement of the
per-circuit guarantee (`Tools.VedU1Contract`) and the entry commands were never part of
`import Sparkle`.

What a user runs on demand, not normally: one research check (`lake build Tests.Ved.<Check>`),
the full list of VED checks (the `ved-full` CI job), `lake test`, and the API docs.

## 2. Waiting time by use case

Each row is the waiting time of one kind of user, measured at the release candidate `2bcf256b`. The
measurement ran on clean GitHub runners (`ubuntu-latest`, 4 vCPU, 15 GB): no cache, a fresh
`elan`, a fresh clone.

**Where the numbers come from.** Workflow run 45777577786 ran twice on the same script commit,
each attempt on a new runner. Both values are given as "sample 1 / sample 2". Their artifacts are
`research-ux-candidate-attempt1` and `research-ux-candidate-attempt2`, with `ux-candidate.tsv`
listing every step.

**How the two samples differ.** Sample 2 was shorter on every step, by between 17% (the deep-route
library) and 40% (the real IP's library). These are observations only: the cause, such as
differences between runners, was not separated. Two values do not show how stable these times are
and do not give an upper bound.

**Status of the run.** Both attempts are marked as failures as a whole, because `lake test` ran
there without its prerequisite (see B). Every value below is from a step that succeeded, and the
`lake test` row is from a separate run.

**Not the same as section 3.** Section 3 is the earlier before/after comparison with `main` (run
45765909458). Its numbers are a different run.

### A. You write circuits in your own project that depends on Sparkle

Condition: the project files already exist. They are a `lakefile.toml` that requires Sparkle at
a fixed commit, plus one circuit, as in `.github/workflows/downstream-smoke.yml`. The setup time
includes installing `elan` and downloading the toolchain (0.4 + 9.5 s / 0.2 + 7.1 s). If both are
already installed, subtract that.

| What you wait for | Sample 1 / sample 2 |
|---|---|
| Setup: `elan` + toolchain download, `lake update`, first `lake build` (compiles Sparkle and your circuit) | 112 s / 82 s |
| After editing your circuit: `lake build` | 2.2 s / 1.6 s |

### B. You develop Sparkle itself

Condition: you work in a clone of the repository.

| What you wait for | Sample 1 / sample 2 |
|---|---|
| Setup: clone, `elan` + toolchain, dependencies, `lake build` | 112 s / 83 s |
| `lake build` again, nothing changed / after a one-line library edit | 1.4 s / 1.0 s, and 3.6 s / 2.7 s |
| The regression suite: `lake build IP.RV32.SoCVerilog`, then `lake test` | 48 s + 351 s (one sample, run 45783205628), rc 0 |
| A pull request's VED job (`ved-pr`) | 5851 s (98 min) in run 44539786136 |

About the regression suite:
- It runs only after the SoC build (README "Testing"). Without that build, on a fresh clone,
  `lake test` exits 1: 24 checks fail because they read `verilator/generated_soc.sv` and
  `generated_soc_cppsim.h`, which that build writes. Both samples of run 45777577786 showed this,
  and so did a run on a development machine. `main` has the same dependency.
- Making the suite self-contained is a separate follow-up.
- Its time has one sample only, because the two earlier attempts ran it without the SoC build.

The `ved-pr` figure is the run time of that one job on the code `2bcf256b`. It is not the time a
pull request waits in total, which also includes queueing and review. The goal of about 20
minutes for required CI is not met (section 6).

### C. You get proofs for your own circuits with the existing entry commands

Condition: you work in a clone of the repository, because the entry commands are used inside it.
Using them from your own project, as a dependency, is not documented and was not measured.

| What you wait for | Sample 1 / sample 2 |
|---|---|
| Setup: B's setup plus `lake build Tools.VedU1Entry` | 173 s / 128 s |
| A short proof: `#ved_u1` on the tutorial's 8-bit register | 2.1 s / 1.6 s |
| A real IP proof: `#ved_u1` on the Keccak round-constant table | 80 s / 60 s, peak memory 5.3 GB |

If the real IP's library is not built yet, its build comes first: 48 s / 29 s.

### D. You add lemmas, statements or routes, each with a check file

This is the path of [CONTRIBUTING-research.md](CONTRIBUTING-research.md).

**Measured order.** The steps ran in this fixed order:
1. C's setup and C's two proofs;
2. the two existing entry checks (`Tests.Ved.U1EntryCheck`, `Tests.Ved.U1KeccakRcCheck`);
3. `lake test`. In these attempts it exited 1 (see B), but it still built the regression suite's
   dependencies;
4. the steps in the table below.

Every time in this table is therefore an **additional** cost after all of that had been built.
None of them is a cold build on its own. They also cannot simply be added to C's setup to give a
new researcher's total setup time: part of what they rely on was built by steps 2 and 3.

**What you need.** A lemma for the basic entry only needs `Tools.VedU1Entry` and its check. The
deep-route and hierarchy libraries are needed only for work on those routes.

| What you wait for | Sample 1 / sample 2 |
|---|---|
| The other tool libraries: the deep route (`Tools.VedU1Deep`) | 770 s / 639 s |
| The other tool libraries: hierarchies (`Tools.VedU2HierRegEntry`) | 47 s / 33 s |
| The checks the contributing page names: hierarchy (`Tests.Ved.U2HierRegCheck`) | 218 s / 149 s |
| The checks the contributing page names: writer (`Tests.Ved.WriteCheckedCheck`) | 119 s / 88 s |
| Re-check after editing a lemma file near the entry (`Tools/VedU1WireShare.lean`) | 23 s / 16 s |
| Re-check after editing a shared foundation file (`Tools/VedU1Contract.lean`, which every entry imports) | 59 s / 43 s |
| A pull request's VED job | as in B |

Each re-check rebuilds `Tools.VedU1Entry` and the entry's check (`Tests.Ved.U1EntryCheck`):
- **The edit:** one trivial theorem appended to the file. This stands in for the cost of
  re-checking what depends on that file. It is not the time needed to write a new, hard proof.
- **Before each edit:** the same targets were built, unchanged.
- **After it:** the edit was reverted, and the targets were rebuilt back to the same baseline
  state before the next edit started.
- **Evidence:** the logs show that the edited module and the check were really rebuilt
  (`Built Tools.VedU1WireShare`, `Built Tests.Ved.U1EntryCheck`).

Not in this table:
- **Re-measuring rows of the 327-command table.** This is possible in principle with the public
  harness branch, but it was not tested for this page and takes hours.
- **Regenerating the approved ledger from measurement results.** This is not possible with public
  steps today, because the generator and the raw data are not public. Appendix C explains both
  points.
- **Writing a new proof.** That time depends on the proof and is not measured.

## 3. Measured waiting time on a clean machine, step by step

Workflow `.github/workflows/research-ux.yml`, run 45765909458 (2026-11-26) on two fresh `ubuntu-latest` runners,
one per revision. Each runner:

- uses no cache and no prebuilt `.olean` files;
- starts from a fresh `elan`;
- clones the revision into an empty directory and follows the published steps.

Each value is a **single run** (one sample per revision). CPU is user plus system seconds. Peak
RSS is the largest single process of the step.

| Step | baseline wall s | CPU s | peak RSS MB | candidate wall s | CPU s | peak RSS MB |
|---|---|---|---|---|---|---|
| clone and checkout | 3.0 | 4.9 | 39 | 3.4 | 4.8 | 36 |
| toolchain manager (`elan` itself) | 0.2 | 0.2 | 16 | 0.6 | 0.2 | 16 |
| toolchain download (`elan toolchain install`) | 10.6 | 8.0 | 84 | 11.0 | 7.8 | 85 |
| dependency fetch, read the lakefile | 10.2 | 10 | 985 | 14.3 | 14 | 1075 |
| **(a) normal `lake build`, cold** | 84.0 | 183 | 1812 | 83.0 | 179 | 1824 |
| (b) `lake build` again, nothing changed | 1.4 | 1.4 | 829 | 1.4 | 1.4 | 830 |
| (c) one-line edit of a library module, rebuild | 3.8 | 5.5 | 1578 | 3.5 | 5.2 | 1578 |
| (c) a user project depending on Sparkle, cold build | 95.7 | 208 | 1808 | 86.1 | 177 | 1821 |
| (c) one-line edit of the user's circuit, rebuild | 2.6 | 3.8 | 1580 | 2.2 | 3.2 | 1580 |
| proof-tool libraries: `lake build Tools.VedU1Entry` | 8.0 | 12 | 1644 | 60.0 | 117 | 1873 |
| (d) tutorial `delay8`: synthesis only | 1.3 | 1.4 | 1573 | 1.2 | 1.2 | 1573 |
| **(d) tutorial `delay8`: `#ved_u1` (synthesis, proof, kernel)** | 2.6 | 3.5 | 1603 | 2.2 | 3.0 | 1624 |
| real IP library: `lake build IP.Crypto.Keccak256HW` | 53.5 | 57 | 2106 | 49.6 | 53 | 2056 |
| **(e) real IP leaf `keccakRcHW`: `#ved_u1`** | 1.4 | 1.4 | 1572 | 78.4 | 79 | 5253 |

Results of the proof steps:

- `delay8` is accepted at both revisions.
- `keccakRcHW` is refused at the baseline: rc 1 after 1.4 s, with no theorem. It is accepted at
  the candidate. Of its 78 s, the profiler attributes 40 s to `simp` and 30.6 s to the kernel's
  type checking, and elaboration is 3.2 s. Synthesis was not timed separately for this proof, so
  its share is not separated here. For `delay8`, the synthesis-only step (d1) is a separate
  measurement.

The CI check file for that proof (`Tests.Ved.U1KeccakRcCheck`) took 82.3 s on the candidate. It
does not exist at the baseline.

What a new user waits for at the release candidate, on this 4-vCPU, 15 GB runner:

| Path | Time |
|---|---|
| Clone, toolchain, dependencies and the normal build | about 112 s (clone, `elan`, toolchain, dependencies, build) |
| The proof tools, on top of that | 60 s more |
| The tutorial proof | 2.2 s |
| The real-IP strict proof | 78 s and 5.3 GB of memory |

Compared with the baseline:

- The normal build is unchanged: 83 s at the candidate against 84 s at the baseline, one sample
  each.
- The proof-tool build grows from 8 s to 60 s, because it has 21 more modules.
- The real-IP proof is new: refused at the baseline, accepted at the candidate.

Memory: the real-IP proof's largest process peaked at 5.3 GB in this single run. We recommend
at least 8 GB of free memory for it. That is a recommendation from one observation, not a
measured lower limit.

The per-step logs, the TSV files and the probe `.lean` files are the run's artifacts
(`research-ux-baseline`, `research-ux-candidate`). The script is
`scripts/research/ux_measure.sh`, and its header lists every step's command.

**Collection and verification are separate.** The script runs every step to the end and
records each exit code. `scripts/research/ux_verdict.py` then judges the result:

- Every required step must be present with exit code 0.
- A proof counts as accepted only if all three hold: exit code 0, the `VED U1 OK` line, and no
  error line.
- A refusal counts only if it was declared as expected. The baseline declares `e2=refused`,
  because it predates that proof.
- Any other combination fails. For example, an OK line with exit code 1 fails.

The workflow's job fails when the verdict fails. `python3 scripts/research/ux_verdict.py
--self-test` runs fake controls: a failed required build, OK with exit code 1, an error after
OK, an undeclared refusal, a declared refusal that was accepted, a missing step, and an absent
optional check.

Run 45765909458 used the script before the verdict step was added. Its saved TSVs and logs were
re-judged with `ux_verdict.py`: the baseline passes with `--expect e2=refused` and fails without
it, and the candidate passes.

## 4. CI, per workflow, at the release candidate `2bcf256b`

Runs of the pull request (event `pull_request`) and one dispatched `ved-full` run.

| Workflow / job | Run | Wall | Largest steps |
|---|---|---|---|
| Build / `build` | 44539785451 | 756 s | full test suite 243 s, SVParser tests 122 s, build project 105 s, RV32 47 s |
| Build / `tutorial-notebooks` (after `build`) | 44539785451 | 404 s | tutorial chapters 193 s, docs-builder image pull 133 s |
| Downstream smoke, ubuntu / macOS / WSL | 44539785554 | 96 / 298 / 422 s | `lake build` of a user project 62 / 123 s, WSL install 129 s |
| IP Tests, 15 groups in parallel | 44539785603 | 47 to 723 s | rv32 group 553 s plus SoC Verilog 155 s |
| VED / `ved-pr` (the VED checks of a pull request) | 44539786136 | 5851 s | strict entry checks 1408 s, nested-loop checks 601 + 542 s, real IP with several loops 558 s |
| VED / `ved-full` (dispatched) | 44539843974 | 6761 s | strict entry checks 1036 s, chained CRC bodies 819 s, real IP with several loops 783 s, every deep-route regression 549 s |
| VED / `ved-full` (dispatched, earlier) | 44492169629 | 8560 s | another run of the same job on the same head; shared runners vary |

The critical path of a pull request is `ved-pr`, about 98 minutes. It is one job of about 45
sequential steps. Every other job finishes within 20 minutes: Build plus tutorial is 1160 s, and
the longest IP group is 723 s.

At the baseline `main` (`6c29b9b8`) the corresponding times were:

| Workflow / job | Wall |
|---|---|
| VED / `ved-full` (run 45176157090) | 1156 s |
| Build / `build` | 921 s |
| Build / `tutorial-notebooks` | 1055 s |

What triggers each workflow:

| Workflow | Runs on | Path filter |
|---|---|---|
| `build.yml` (build, tutorial, pages) | push to main, every pull request, dispatch | **none** |
| `downstream-smoke.yml` | push to main, every pull request, dispatch | **none** |
| `ved.yml` | pull request: `ved-pr`; weekly schedule and dispatch: `ved-full` | yes: `Sparkle/**`, the VED tools and checks, `lakefile.lean`, toolchain |
| `ip-tests.yml` | push, pull request, dispatch | yes: `IP/**`, `Sparkle/**`, `Tests/**`, `Examples/**`, lakefile, toolchain |
| `research-ux.yml` | dispatch, push to `research/ux-*` only | never on main or pull requests |

Two consequences follow:

- A pull request that changes only documentation still runs Build, tutorial and downstream
  smoke, which is about 20 minutes of runner time unrelated to the change.
- `ved-full`, the job that checks all VED targets, never runs on a pull request or a push to
  main. It runs only weekly or on request.

## 5. Proposal: how to split CI

This is a proposal. No workflow is changed by this page.

| Tier | Contents | When |
|---|---|---|
| Required on a code PR | normal `lake build`; `lake test`; the strict-audit controls; the VED checks for the changed paths (`ved-pr`, path-filtered as today); the small examples (Ch07c `delay8`, the entry check); every check's refusal controls; the IP groups for the touched paths | every pull request that touches code, path-filtered |
| Docs-only PR | link check (`scripts/research/check_links.py`), coverage table check (`scripts/research/coverage_table.py --check`), tutorial syntax check (`scripts/check_tutorial.sh`); the tutorial build only when `docs/tutorial/**` changes | pull requests that touch only `docs/**` or `*.md` |
| Heavy | `ved-full` as a matrix of independent targets, the API docs, macOS and WSL smoke | weekly, on request, or by a label on a pull request |
| Release candidate | `ved-full` on the exact release commit, `research-ux.yml` (the user procedure above), downstream smoke on all systems, the tutorial build | before a release is declared, on that commit |

Rules that keep the split honest:

- **No silent skip.** Every check that a path filter removes from a pull request still runs in
  the weekly and release tiers. A skipped job is reported as skipped, never as a success.
- **Same coverage, shorter wall time (to be tried, not yet shown).** The `ved-pr` and `ved-full`
  steps are independent `lake build` targets, so they could run as a matrix with the same set of
  checks. The resulting wall time is not known yet:
  - Each matrix runner may rebuild the shared dependencies (the Sparkle library and the tool
    libraries), so today's sequential step times are not a bound for it.
  - The longest single step of `ved-pr` (the strict entry checks, 1408 s, 23.5 minutes) is
    already longer than the target below.

  Open work: split that step's targets; design how the runners share the built dependencies (a
  dependency job whose `.lake` the matrix jobs restore, or a cache keyed on the commit); then run
  one matrix trial with the same set of checks and compare.
- **Docs PRs.** Add a `paths-ignore` for `docs/**` and `**/*.md` to `build.yml` and
  `downstream-smoke.yml`, and give the docs checks above their own small job.

## 6. Targets, from the measurements

Rules, in order:

1. **Normal build:** on a 4-vCPU runner, the cold `lake build` measured 83 s at the candidate and
   84 s at the baseline. The target is no regression: a change that makes this step more than
   about 20% slower on the same runner type needs a recorded reason. These are single samples,
   so rerun the workflow before acting on a difference of that size. The proof-tool build (60 s)
   and the tutorial proof (seconds) get the same rule.
2. **Required CI on a pull request (a goal that is not met today):** a code pull request should
   get its required result in about the time of the longest required job, not the sum of all
   steps. Without `ved-pr`, the longest required jobs are Build plus tutorial (1160 s) and the
   rv32 IP group (723 s). That suggests a goal of about 20 minutes for required CI.

   Today `ved-pr` takes 5851 s, and its longest step alone takes 1408 s, so the goal is not met.
   Whether a matrix can reach it depends on the open work in section 5: splitting the longest
   step and sharing the built dependencies. Until a matrix trial with the same checks has been
   measured, 20 minutes stays a goal and not a gate.
3. **Long steps:** a single required step above 10 minutes is a candidate for splitting. Lake
   already warns at 10 minutes.
4. **Release candidate:** no wall-time gate, but the run must complete, and its run ID is
   recorded.

Slow targets, the choice made for each, and why:

| Target | Measured | Choice | Why |
|---|---|---|---|
| `lake build` (Sparkle, compiled to native code) | 83 s cold (baseline 84 s) | keep | the native code is needed by the simulation and by the IP libraries; the release candidate changes one compiler file in this closure |
| `Tools.VedU1Entry` | 60 s (baseline 8 s) | keep as an explicit target | it is the proof tool itself; a user of `#ved_u1` needs it |
| strict proof of a real IP leaf (`keccakRcHW`) | 78 s, 5.3 GB (refused at the baseline) | stays an explicit target; no `-O0` | the profiler shows the time is in `simp` and in the kernel, not in compiling; `-O0` would not change it |
| `ved-pr` / `ved-full` | 5851 / 6761 s | try a matrix with the same checks, after splitting the longest step and sharing built dependencies | the steps are independent targets, but each runner may rebuild dependencies; the gain is measured only by a trial |
| API docs and tutorial image | 475 + 176 s at `main` | docs-path trigger, plus the weekly run | unrelated to whether the code is correct |
| `lake test` | 243 s | required on a code PR | the regression suite for code changes |
