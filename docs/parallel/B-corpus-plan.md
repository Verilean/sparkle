# B — plan: the design-level generators on the CORPUS (round par/b-35)

A PLAN. No file of it is written, nothing was run. Marks: [R] read in the
tree at 20ab638e, [M] measured earlier by the integrator (record cited),
[P] predicted, [?] not known.

## 1. What exists [R]

`scripts/shipping-coverage/endpoints.sh WORKDIR [FILES.txt]`
(80 lines) and `endpoint_tail.lean.in`:

* needs `WORKDIR/status.txt` and `WORKDIR/machine_decls.txt` — both are the
  OUTPUT of `run.sh` pass 1 (`report.py routes` writes `machine_decls.txt`
  from the compiler's profile log, `report.py` 57–59). Pass 1 elaborates
  every corpus file: this is the full-corpus run the standing instruction
  forbids.
* per file: a job file = 8 `import Tools.…` lines + the corpus file + the
  tail, run by `timeout 1500 lake env lean --load-dynlib=…libsparkle_Sparkle.so`,
  `xargs -P ${ENDPOINT_JOBS:-3}`; stdout/stderr discarded; exit code to
  `endpoint_status.txt`; results appended by the tail itself to
  `endpoint_reasons.txt`, `linked_reasons.txt`, `premise_items.txt`.
* the tail's first `run_cmd`: for every name of `machine_decls.txt` that is
  a constant of this file's environment (private names resolved by user
  name), `Tools.ShippingMachineCommand.generate n (checkCloses := false)` →
  `f.machine_sound` and, where they apply, `f.machine_ships_wired` /
  `f.machine_ships_comb` (tags `OK|WIRED`, `OK|COMBSHIP`, `OK`); then
  `generateChild` / `generateLinked`; second `run_cmd`: `generateGateChild`
  for gate children, `generateComposed`, the `SHIPSHIERH` premise
  evaluation; third: `generateAny` (`machine_composedT`), depth 1–3
  `generateCoreN`, `ShipsDesignSVCommand.generate`, premise evaluation.
* It is not under `cgrun.sh` (its own `timeout`, parallel 3, no memory
  cap), and a rerun truncates the four result files (`: >`): not resumable.
* [M, memory note / `docs/ShippingCompiler-Coverage.md`] 391 files, 364
  machine-route declarations, all with ship-level endpoints; one
  elaboration of a large file can take 3 GB (the script's own comment).

So the ship-level sweep cannot be reused as it is: it presupposes the
full pass 1, it is parallel and uncapped, and it restarts from zero.

## 2. The design: one file = one resumable, capped, serial job

### 2.1 No pass 1: the candidates are found in the file's own environment

The tail does not read `machine_decls.txt`. It computes its candidates
itself, in Meta code, from the environment AFTER the corpus file:

1. *Tops* (optional, cheap, no Lean): a shell `grep -oE` of the file for the
   identifier after `#synthesizeVerilog`, `#writeDesign`,
   `#writeVerilogDesign`, `#synthesizeVerilogDesign`, `#synthesize` (the
   patterns of `run.sh` 25) → `WORK/jobs/<file>.tops`. Used only to MARK
   rows as "top of this file"; not needed to find candidates.
2. *Candidates* (in the tail): every constant of the environment whose
   module is the job file's own (`env.getModuleIdxFor? c = none`: declared
   in the file being elaborated) and that is a definition with the
   `@[hardware_module]` attribute (`Sparkle.Compiler.isHardwareModule env`,
   as `probe_tail.lean.in` 62 uses it) or is one of the tops. For each:
   `Tools.ShippingMachineCommand.readMachine c` in a `try` — success ⇒
   machine route candidate, with `shape.insts`, `shape.layout.slots`,
   `shape.instFields` read off the result (the classification the census
   tool `#design_coverage` already does: `depthOf`, `openReason`); failure
   ⇒ try the gate (`mixedCertifiedShape?` on the entry constant, as
   `gateDefs` does); failure ⇒ row `NOT-MACHINE` with the reader's message
   (legacy route or not hardware) and nothing else is attempted.
   Imported declarations are NOT candidates of this file (they are
   candidates of the file that defines them); they are generated only as
   callees, on demand (2.3).

   This replaces "the route the compiler took" (pass 1's profile log) by
   "the route the reader predicts". They can differ [?]: the reader is the
   machine gate's own function, but the compiler tries `certifiedShape?`
   and the mixed gate first. The tail therefore records the predicted
   class, and a declaration counts only when an ENDPOINT is generated —
   whose premises are the run and the reflection, so a wrong route
   prediction yields a theorem with a premise that the real run does not
   satisfy, not a false theorem. Where a `machine_decls.txt` from an OLD
   measurement is available it can be passed as an optional cross-check
   column (`in old machine list: yes/no`), never as the source of
   candidates.

### 2.2 Per candidate: the chain, each step a `try` with its own class

All in ONE `elab` command per candidate (not one `run_cmd` for the file),
so that a kernel check that does not end costs one declaration's rows, and
START lines exist. A small command file `Tools/ShippingCorpusSweep.lean`
would define `#corpus_design_sweep` (no argument: all candidates of the
file) on top of the existing generator functions — the tail is then three
lines. Each step logs `CORPUS START f step` to stderr BEFORE it runs and
appends one line to `WORK/rows/<file>.txt` AFTER it (so a killed job still
shows where it stopped).

| class of `f` (predicted by the reader) | prerequisite calls, in order | design-level generator | endpoint |
|---|---|---|---|
| register leaf (no call, ≥ 1 slot) | `ShippingMachineCommand.generate f` (→ `machine_sound`, `machineData`, `machine_ships_wired`); `closesTheorem? f` | `ShippingLeafSweepCommand` (`#leaf_sweep`'s function) | `f.machine_design_leaf0` |
| slotless leaf (no call, no slot, output `out`) | `generate f` (→ `machine_ships_comb`); `closesTheorem? f` | `ShippingCombLeafClosedCommand.combDesign0` | `f.machine_design_comb0` |
| gate-route leaf | `generateGateChild f` | `ShippingGateDesignCommand.gateDesign0` (this round, NOT BUILT) | `f.gate_design0` |
| one-output parent of gate / leaf children | `generate` on `f` and on every callee (callees first, 2.3); `generateLinked`, `generateComposed`; `#machine_design_svHR`'s function; `#machine_oneout_any` / `#machine_design_svH_full`; `#machine_closes_at` | the closing step of `ShippingOneOutFullCommand` | `f.machine_design_svH_full_closed` |
| group / deep parent | callees first; `generateCoreN f n` for the least `n ∈ 1..3` (as the old tail does); `#machine_design_svNR f n`; `#machine_closes_at f` | `#machine_no_ports f n`, else `_kids`, else `_deep`, else `_seq` (each a `_try`-style call: the first whose scope scan accepts) | `f.machine_design_noPortsNR{n}_closed` |
| memory parent at depth 0 (its calls are memory reads / memory-only children) | `generateAny f` (`machine_composedT`), `#machine_ships_hier`, `#machine_design_svR0` | `#machine_no_ports_mem`, else `#machine_no_ports_memseq` | `f.machine_design_noPortsR0_closed` |

Every generator above already has a non-throwing scope scan and the
REFUSED / FAILED / GENERATED vocabulary (the `_try` commands and the three
sweeps). The corpus command only sequences them and never asserts a class.
After the chain: the endpoint is re-checked by the census's `recheck`
(0 NOT ALLOWED, no checker constant, `DesignSV`) — the row's class is
`COVERED <form>` only then.

Rule from round b-34, binding for the new command: no reflected data
(`f.machineData…`) is EVALUATED in compiled code; the classification uses
`readMachine`'s result (Meta values) and kernel `decide`.

### 2.3 Callees

A parent's generators need its callees' endpoints (`run #machine_endpoint c
first` is their error). Callees may be imported. The command runs `generate
c` (and the callee's own leaf / comb / gate design step) for every callee
of a candidate, depth first, with a visited set, inside the candidate's
budget; rows for imported callees are tagged `callee-of f` and are not
counted for this file. This repeats work across files that share a child
(e.g. `keccakRcHW`); accepted, because the alternative — a persistent
`.olean` of generated endpoints per file — changes the build graph.

### 2.4 The driver script (new, `scripts/shipping-coverage/design_sweep.sh`)

    design_sweep.sh WORKDIR FILES.txt        # FILES.txt is REQUIRED: the chosen subset

* no default file list: the script refuses to run without `FILES.txt`
  (the standing instruction — a chosen subset, never the corpus);
* serial: one file at a time, each as ONE `cgrun.sh -n ds-<k> -m 3G -s 0
  -t <limit> -- lake env lean --load-dynlib=… job.lean` (the one-job gate of
  `cgrun.sh` already forbids two at once; exit 75 = "another job is alive"
  → the script waits and retries, it does not skip);
* resumable: `WORKDIR/done/<file>.status` is written after each job (exit
  code, wall time, cgroup peak from the cgrun record); a file with a status
  is skipped unless `REDO=1`; the per-file row files are never truncated by
  a rerun of another file;
* job file = imports (the generator command files + `Tools.ShippingCorpusSweep`)
  + the corpus file + the 3-line tail. The corpus file's own
  `#synthesizeVerilog` commands run again in the job (as in `endpoints.sh`):
  the job is at least as heavy as elaborating the file;
* classification of unfinished files as in `endpoints.sh` 66: timeout (124),
  killed / OOM (137, and the cgrun record's `memory.events`) ⇒ the file's
  remaining candidates are `UNMEASURED`, not failed;
* a final `report.py design WORKDIR` prints, for the files done so far:
  per class the counts of COVERED / REFUSED (by reason) / FAILED /
  UNMEASURED, the forms, and the per-declaration times. It prints "N of
  the M files given" in every line: a subset is never reported as the
  corpus.

### 2.5 Order of use

1. A pilot of 5–10 small files chosen by the integrator (suggested, by
   class, from files already known to be on the machine route [M, older
   records]: one control-loop file (PID / biquad), one CRC / UART file, one
   crypto controller wrapper, one Keccak file, one file with a memory) —
   each run alone, to MEASURE the cost per file and per step before any
   larger subset.
2. Then by directory, a few files per session, smallest first (line count
   as the proxy), stopping at the first OOM class to look at it.

## 3. Expected cost per file

| part | cost | basis |
|---|---|---|
| elaborating the corpus file itself (+ its syntheses) | most files seconds to a minute; the large ones minutes and up to ~3 GB | [M] `endpoints.sh` header; `run.sh` gives 300 s per file in pass 1 |
| `generate f` (`machine_sound` + ships) | 0.1–1.5 s per declaration for the first 55; larger for wide data | [M] `docs/ShippingCompiler-Coverage.md` 562–566; Keccak-size data [?] (A-census-2 §2.3: unmeasured) |
| leaf step (`leaf0`) | 150–640 ms per declaration | [M] `docs/parallel/B-leaf-sweep.md` build record (test declarations) |
| slotless step (`comb0`) | 110–210 ms per declaration | [M] `docs/parallel/B-slotless-leaf-2.md` build record |
| gate step (`gate_design0`) | ~ `#gate_child` | [P], not built |
| parents' chains | seconds per parent for the test parents; the `decide`s are over the reflected data, so they grow with slots × width | [?] for IP-size parents (the 256-bit wrappers: A-leaf-gen §6 "not known") |
| memory | the job must fit 3 GiB with swap 0; the old sweep ran 3 such jobs in parallel on a larger budget, so ONE job is PREDICTED to fit for most files; the files that needed ~3 GB alone are PREDICTED to be killed | [P] |

Per-file time limit: 1500 s as in `endpoints.sh` to start with; the pilot
decides. A whole-subset estimate is deliberately NOT given: it is the
pilot's result.

## 4. Classes: covered by today's generators, and what needs new work

PREDICTED, by the reader's class. The corpus proportions are [?] — the
last route table (112 → 364 machine-route declarations) does not record
calls / slots / memories per declaration, and I did not run anything.

| class | today | new work |
|---|---|---|
| register leaf, one or more outputs, no call | COVERED form exists (`leaf0`); 55/55 of the test leaves GENERATED [M] | none expected; wide data may need `decide +kernel` budget [?] |
| slotless machine leaf, one output `out` | COVERED form exists (`comb0`); 32/32 [M] | several outputs or an output not named `out`: `CombKid.one` refuses — generalise `comb_entry_design0_of_ships` to the layout's outputs (the ship-level form already quantifies over them) |
| gate-route leaf | this round, NOT BUILT (`gate_design0`) | the Signal-level source form (B-gate-entry §3.3) if wanted |
| one-output parent over gate / slotless children | `svH_full_closed` (14 declarations [M]) | — |
| group / deep parents without shared descendants | `noPortsNR{n}_closed` (9 [M]) | depth > 3 [?] |
| parents with a shared descendant (`mixDeep`) | OPEN | worker A's cache-coherence route (HarnessStill / EntryStill; `mixDeep` not connected) |
| memory parent at depth 0 | `noPortsR0_closed` (9 [M]) | — |
| **memory at depth ≥ 1** (a child that has a memory, under a parent) | OPEN | the depth generators' kid classes do not include a memory-route child: needs the `R0` form as a kid interface of `noPortsNR{n}` (a new kid kind + its `ChildIface`) |
| **slotless parents of combinational children** (no register in the parent) | partly: `#machine_no_ports_seq` covers slotless parents of SEQUENTIAL children; `K = 0` parents of comb children are listed open in the calls-close notes | a `comb0`-like closed form for a slotless parent: `comb_entry_shape` assumes `shape.insts = []` |
| **multi-output gate children** | OPEN | `ChildFn` is one output (`mc.outputs = [outP]`); needs a `ChildFnN` and the linked theorem over it — a proof unit, not a generator change |
| **legacy route** | no endpoint of any kind | not a generator question (G2: the legacy route's meaning); the row is `NOT-MACHINE` with the reader's reason, which doubles as the per-file list of what blocks certification |
| Keccak-size designs | sponge parent covered in a target-only test [M] | kernel cost over the corpus variants [?] |

## 5. What the first written unit would be (not written now)

1. `Tools/ShippingCorpusSweep.lean`: candidate discovery (2.1) + the chain
   (2.2) as ONE never-failing command with START lines and row files; a
   test file running it on two existing test modules (one leaf file, one
   parent file) to pin the row format — buildable and measurable without
   touching the corpus.
2. `scripts/shipping-coverage/design_sweep.sh` + `design_tail.lean.in` +
   `report.py design` (2.4).
3. The pilot (2.5), by the integrator.

## 6. Not determined by reading

* How often the reader's predicted route differs from the compiler's route
  on corpus declarations (2.1).
* Whether `isHardwareModule` + "declared in this file" finds every
  declaration pass 1 listed (untagged `synth_*` wrappers are found only
  through the tops grep; private declarations need the name resolution of
  the old tail).
* The memory peak of a job on the large IP files under a 3 GiB cap.
* Whether the generators' `IO.Ref` row stores (`initialize rows`) behave in
  a job file that is not a module of the package (they did in the old
  tail's style of `run_cmd`; the sweeps' refs were only used in test
  modules).
* The corpus counts per class (4).

## 7. The tooling AS WRITTEN (round par/b-36) — WRITTEN, NOT RUN

Nothing below was executed (the shell script was only parsed with `bash -n`,
the Python file with `ast.parse`); the integrator does not run it on corpus
files without the user's ruling.

| file | what |
|---|---|
| `Tools/ShippingCorpusSweep.lean` | `#corpus_design_sweep "ROWS" "TOPS" "LABEL" "MODE"`: candidates of the file being elaborated, class by the readers, the leaf chains, the census re-check, one appended row per candidate + a `FILE-DONE` row; never an error |
| `scripts/shipping-coverage/design_tail.lean.in` | the three-line tail (`set_option maxHeartbeats 0 in #corpus_design_sweep …`) |
| `scripts/shipping-coverage/design_sweep.sh` | the driver: `design_sweep.sh WORKDIR FILES.txt` |
| `scripts/shipping-coverage/design_report.py` | the report; every line "N of the M files given" |
| `scripts/shipping-coverage/design_selftest_files.txt` | the self-test list: `Tests/Compiler/ShippingMachineSeqTest.lean`, `Tests/Compiler/ShippingMachineInstTest.lean` (both in `Tests.AllTests`' closure) |
| `Tests/Compiler/CorpusSweepSelfTest.lean` (target-only) | the command on three declarations of its own file, rows to `/dev/null`: pins the row format without the script |

### Differences from the plan (§2)

* **Parents are NOT attempted** in this version. Classes `LEAF-REG`
  (`generate` + `#leaf_sweep`), `LEAF-COMB` (`generate` +
  `#comb_closed_sweep`) and `GATE` (`#gate_design_sweep`) run their chain;
  `PARENT` rows record slots / callees / structure fields with outcome
  `NOT-ATTEMPTED`; so do `GATE-INST` (a parent without a register over
  combinational calls: no generator, `B-slotless-parents.md`) and
  `NOT-MACHINE`. Reason: each parent form is a chain of 3–5 commands with a
  depth argument and callee prerequisites; sequencing them blind, without
  one measured run of the leaf part, would mix tooling failures with
  generator refusals. §2.2's table stays the plan for the next version.
* Therefore no callee handling (§2.3) yet: leaves have no callees.
* The gate chain is `#gate_design_sweep` (BUILT), not the Signal-level
  `#gate_source_sweep` of this round (NOT BUILT) — the tool must not depend
  on an unbuilt file.
* The sweeps are called as COMMANDS (`elabCommand` of `#leaf_sweep f` …):
  they resolve `f` as an identifier, so a PRIVATE declaration comes back
  `UNRESOLVED` from the sweep and its row is `NOT-COVERED`.
* The report is a separate file, `report.py` is not edited.

### Driver behaviour (as written)

* `FILES.txt` REQUIRED (exit 2 without it); `#` comments and blank lines
  skipped; the list is copied to `WORKDIR/files_given.txt`.
* per file: `jobs/<key>.tops` by `grep -oE` of the synthesis commands'
  identifiers; job = `import Tools.ShippingCorpusSweep` + the file + the
  tail; ONE `cgrun.sh -m $DS_MEM(3G) -s 0 -t $DS_TMO(1500) -j 2 -- lake env
  lean --load-dynlib=… job`; cgrun's exit 75 (another protected job alive)
  → wait 30 s and retry up to `DS_WAIT` (3600 s), then NO status (the file
  is tried again by the next invocation).
* `done/<key>.status`: `file= result= exit= seconds= peak=`; `result` is
  `measured` iff the rows file has the `FILE-DONE` row — NOT by the exit
  code (a corpus file with an error message of its own makes `lean` exit 1
  although the tail ran); otherwise `unmeasured-timeout` (124),
  `unmeasured-oom` (137), `unmeasured-not-protected` (76–78: cgrun refused,
  the payload did not run), `unmeasured-exit-N`.
* resumable: a file with a status is skipped; `REDO=1` reruns it (its rows
  file is truncated then, only its own).
* logs: `logs/<key>.cgrun.txt` (cgrun's protect / result lines),
  `logs/<key>.lean.txt` (the job's output: the `CORPUS START …` lines show
  where a killed job stopped).

### Cost model and assumptions (each one unverified until the self-test runs)

1. One job costs at least the elaboration of the file itself (its own
   `#synthesizeVerilog` / `#machine_endpoint` commands run again in the
   job), plus per candidate: `generate` 0.1–1.5 s [M, first 55], leaf step
   150–640 ms [M], slotless step 110–210 ms [M], gate step 126–271 ms [M,
   0a0a4f71], the census re-check (one `forallTelescope`), and — in mode
   `all` — one `readMachine` per local definition.
2. The import `Tools.ShippingCorpusSweep` pulls the generators' closure
   (the leaf, slotless, gate and census command files): its `.olean`s must
   be built; loading them is part of every job's memory. ASSUMED to fit
   with the file under 3 GiB for the self-test files; UNKNOWN for large IP
   files (the old sweep's comment: one elaboration of a large file can take
   3 GB).
3. `initialize` refs of the sweeps (`rows`) work in a job file: ASSUMED
   (the job imports their modules, as the test files do).
4. A job file re-declares the corpus file's contents as a new module; this
   is what `endpoints.sh` does. ASSUMED that none of the tool's imports
   imports the corpus file (true for `Tools/*`: they import no `Tests`,
   `IP`, `Examples` module [R: `grep "^import" Tools/ShippingCorpusSweep.lean`
   and its direct imports; the transitive closure was not walked]).
5. The candidate filter drops a local definition `p.s` when `p` is a
   definition and `s` starts with a generated prefix (`machine_`,
   `machineData`, `gate_`, …) — ASSUMED not to hit user definitions.
6. `tops` matching is by full name or `.`-suffix of the user-facing name.
7. The class is the READER's prediction (§2.1); `COVERED` is decided only
   by the endpoint's existence and re-check.
8. Serial: wall time is the sum over files; no estimate for a subset is
   given before the self-test and a pilot.

### Self-test (for the integrator, when allowed)

    lake build Tools.ShippingCorpusSweep          # via cgrun, as every build
    scripts/shipping-coverage/design_sweep.sh ~/sparkle-work/ds-selftest \
        scripts/shipping-coverage/design_selftest_files.txt

PREDICTED: both files `measured`; `ShippingMachineSeqTest`: its register
machines (`cnt`, …) as `LEAF-REG COVERED machine_design_leaf0` where they
carry the flag `data` or `tagged`; `ShippingMachineInstTest`: `pick`,
`pickD` `GATE COVERED gate_design0`, `counter2` / `innerPick`… per their
flags, the callers `PARENT NOT-ATTEMPTED`. Which definitions are candidates
in mode `marked` depends on which carry `@[hardware_module]` or generated
data — not predicted per declaration.
