# The process-global depth cell: overlap and cancellation (worker K, round par/k-depth) — WRITTEN, NOT RUN

Reviewer's ruling 2026-10-14 (second message), item 5: reproduce first; a controlled minimal probe of what
`finally` does to the depth and the caches under concurrency and cancellation; record if the real language
server does not reproduce it; no redesign before the impact is known; keep it tied to whether `Start0` holds
at the real entry.

Base `poc/roundtrip-proof` 80745d94, branch `par/k-depth`. INVESTIGATION ONLY: no file under `Sparkle/` or
`Tools/` is changed. Nothing here was built or run (no `lean`, `lake`, server); every outcome is a PREDICTION
from reading. Line numbers: `Sparkle/Compiler/Elab.lean` at 80745d94; toolchain
`~/.elan/toolchains/leanprover--lean4---v4.32.1/src/lean/` (written `L/…`).

Files of this round: this document; `Tests/Compiler/DepthCancelProbe.lean` (controlled probe, one process, no
server; target-only, logs only); `scripts/shipping-coverage/ls_depth_probe.lean` + `ls_depth_probe.py` (the
real-server procedure).

## 0. Result of the reading, plainly

1. **Batch elaboration (`lake build`, `lake env lean f.lean`) has no overlap**: one `lean` process per file,
   commands of a file strictly one after another, and nothing in `Sparkle/` or `Tools/` starts a task. There
   the depth reads 0 at every public command (the argument of `G-mixdeep-outermost.md` §5 stands).
2. **In the language server two synthesis runs of ONE file can be alive at once**: the run of the OLD
   document version, cancelled but not yet at a cancellation check, and the run of the NEW version. The
   server cancels and does not wait. The window is the time the old run needs to reach its next check; the
   compiler's code has no check of its own, only those inside `whnf` / `inferType` / `isDefEq`.
3. **Cancellation itself is clean**: the interrupt is an exception of the monad; it passes every `try …
   finally` (and cannot be caught by `try … catch`), so the cancelled run decrements the depth and restores
   its nested caches. No depth leak from a cancellation alone.
4. **The overlap is what does harm.** The second run reads depth ≥ 1, takes the NESTED branch, and
   (a) does not empty the child cache, the sub-module memo and the type cache — they hold entries of the
   first run, compiled from the OLD text, keyed by declaration NAME: a stale child module is returned for a
   declaration whose body changed (a silent wrong result in the editor's output);
   (b) empties seven per-module caches the first run is using, and at its end writes back the snapshot it
   took, over whatever the first run wrote meanwhile;
   (c) the depth cell is updated by `get` … `set (d + 1)` (not atomic): one interleaving loses a decrement
   and leaves the cell at 1 with no run alive — every later command of that server session is then
   "nested" and never empties a cache again.
5. **Premises.** A server session with such an overlap violates `Start0` (depth 0 at the start world) for
   the second run — and more: the law witness `RefLaws` itself (reads return this run's last write) is not a
   description of an interleaved execution, so neither disjunct of `ChildBnd` is available. Batch
   elaboration violates neither.
6. Not reproduced: it needs the server. §5 is the procedure; §4 the controlled probe with predictions.

## 1. (a) Ways two synthesis runs can be alive in one process

| situation | overlap? | grounds (by reading) |
|---|---|---|
| `lake build` | no | one `lean` process per module; within it, see the next row |
| consecutive commands of one file, one document version (batch or server) | **no** | `L/Lean/Language/Lean.lean` 679: `let cmdState ← doElab …` RETURNS before 749 `parseCmd none parserState cmdState next …` parses the next command (654–656: "for now, wait on 'command finished' snapshot before parsing next command"). `doElab` (751–781) runs `elabCommandTopLevel` synchronously. A `#synthesizeVerilog` is an `elab` command: its whole body runs inside that call |
| `Elab.async` (`L/Lean/CoreM.lean` 35–41; true in server and cmdline) | no, for these commands | what runs in tasks: bodies of theorems / definitions (`elabMutualDef`), kernel checking of added declarations (`L/Lean/CoreM.lean` 732–750), linters (`L/Lean/Elab/Command.lean` 379–393) — tasks that OUTLIVE their command (`snapshotTasks`) and so run next to LATER commands. None of them calls the compiler: the entry is called only from the command bodies (`G-mixdeep-outermost.md` §5) inside `liftTermElabM`. A tactic proof or a `deriving` handler that called `synthesizeCombinational` would overlap with later commands; `grep` finds none in `Sparkle/`, `Tools/`, `IP/`, `Examples/` |
| tasks in the repository's own code | no | `IO.asTask` in `Tests/Drivers/{SvRoundtripMain:198, SvToDslMain:104, SvCosimMain:533}.lean` (workers over parsed SystemVerilog files; none calls the entry: `grep synthesizeCombinational\|synthesizeHierarchical` — 0 in the three) and in `Tests/Compiler/DepthStartProbe.lean` 48, 74 (a one-line write). `Sparkle/`, `Tools/`: no `asTask` / `Task.spawn` |
| **language server, re-elaboration after an edit** | **YES** | below |

The server (one FileWorker PROCESS per open file: every version of that file shares the cells).
`handleDidChange` → `updateDocument` (`L/Lean/Server/FileWorker.lean` 566–600) calls the incremental
processor on the new text at once, with the old snapshot tree. In `parseCmd`
(`L/Lean/Language/Lean.lean` 555–749):

* commands before the edit are reused (`unchanged`, 560–581: the new chain WAITS on the old command's
  `resultSnap`, 569 — no second run of them);
* at the first changed command: `old.nextCmdSnap?.forM (·.cancelRec)` (612) — every LATER old command is
  cancelled. `cancelRec` (`L/Lean/Language/Basic.lean` 234–237) sets the cancellation tokens down the tree;
  it does not wait for anything. The comment at 608–611 promises only that no further OLD command STARTS;
* the changed command itself: its old elaboration is handed to the new one as `snap.old?`; a command
  without incrementality support — every `elab` command of this repository — cancels it on entry
  (`L/Lean/Elab/Command.lean` 425–430, `old.val.cancelRec`) and goes on immediately;
* then a new task elaborates the new command (640, `BaseIO.asTask`), and so on down the file.

Cancellation is cooperative (`L/Lean/CoreM.lean` 463–466: `checkInterrupted` throws only where it is
called). The token reaches the compiler's `MetaM` (`L/Lean/Elab/Command.lean` 172–190: `runCore` copies
`ctx.cancelTk?` into `Core.Context`; `liftTermElabM` 731 goes through it). So after the edit the OLD
`#synthesizeVerilog` keeps running — inside its `try`, depth ≥ 1 — until its next check, while the NEW
elaboration proceeds. Two shapes:

* **S1, edit ABOVE the long command** (the usual one: the user edits a definition while the synthesis of
  the file's top is still running). Old top: cancelled by 612. New: the edited definition is elaborated
  (milliseconds for a small one), then the unchanged-text commands after it are RE-ELABORATED (`old? =
  none` from 749 on), among them the new `#synthesizeVerilog top`. It overlaps the old one iff the old one
  has not reached a check by then.
* **S2, edit IN the command line itself**: the new run of the same command starts right after cancelling
  the old one (no other command in between): the shortest gap.

Where the compiler meets a check: it has none of its own (`grep checkInterrupted\|checkSystem
Sparkle/Compiler/Elab.lean` — 0). It is interrupted inside Lean's Meta functions: `whnf` on a non-trivial,
uncached term (`L/Lean/Meta/WHNF.lean` 1111 `checkSystem "whnf"`), `inferType` on a cache miss
(`L/Lean/Meta/InferType.lean` 206, 213), `isDefEq` (`ExprDefEq.lean` 2274), instance synthesis, `transform`
(`Transform.lean` 53, 111), and `Core.withIncRecDepth` (`CoreM.lean` 471–472). The translator calls these
constantly, so in Meta-heavy phases the window is short (the time between two such calls). It is long
where the entry does no Meta call: pure `CircuitM` / IR work between handlers, the two-pass body
evaluation's bookkeeping, and — outside the entry, depth already 0 — `optimizeDesign`, DRC, printing,
file writes. How long the longest check-free stretch INSIDE the entry is on a real design was not
determined by reading; that is the quantity the real-server check (§5, mode `real`) would measure.

## 2. (b) What the second run observes

Entry code: 5432 read depth; 5447–5503 snapshots (only if depth ≠ 0); 5504–5516 depth-0 branch (empties 12
cells); 5517–5528 nested branch (empties 7); 5529 `set (depth + 1)`; 5542–5554 `try … finally` (decrement;
if depth ≠ 0 put the 7 snapshots back).

The second run B starts while the first run A is inside: it reads depth ≥ 1.

| cell (line of `initialize`) | key | B at entry (nested branch) | consequence |
|---|---|---|---|
| `sparkleSynthDepth` (961) | — | reads A's depth `d ≥ 1`, writes `d + 1` | `get` and `set` are two operations: see §3 |
| `sparkleChildCache` (1032) | declaration NAME | **not emptied**; read at 8891 before any synthesis | a child A compiled from the OLD text is returned for the same name in the NEW text: stale module, no check of body or environment |
| `sparkleSubModuleCache` (1024) | declaration NAME | not emptied; read at 5313 | the same, for the memoised sub-module route |
| `sparkleTypeCache` (1088) (+ hit / miss counters 1093–1094) | `Expr` | not emptied | keyed by the expression itself; an `Expr` that mentions a constant whose TYPE changed between the versions would give the old type (not examined further) |
| `sparkleFvarValueMap` (984), `sparkleWireWidthCache` (164), `sparkleLetWireCache` (991), `sparkleLoopWireCache` (1008), `sparkleWireCanon` (1014), `sparkleSubInstanceOutputs` (1053), `sparkleSingleOutInstanceCache` (1080) | fvar name / wire name / call key — names of the module BEING BUILT | snapshot taken (A's half-built content), then **set to `{}`** | A, still running, loses its let / loop / alias / width / port entries in mid-module (a width lookup of one of A's wires misses; a `let` of A is translated twice; …). At B's end the snapshot is written back **over** what A added meanwhile |
| `sparkleFvarZetaVisited` (976) | fvar name | neither saved nor emptied by the entry (set at 5668, inserted / erased at 6975–6989) | A's and B's insertions and erasures interleave |
| `sparkleChildSynth` (1040) | — | constant (`some synthesizeChild`, 8895) | none |
| profiling counters (757–758, 950–951, 1101–1106, 1144–1145) | — | shared | diagnostics only |

All of these are plain `IO.Ref`s shared by the threads; each single `get` / `set` / `modify` is safe, the
sequences are not. Besides the stale answers there is unsynchronised read-modify-write of every map by two
threads: an entry written by one run between the other's `get` and `set` is lost.

A's result is then also suspect (it ran on emptied caches), but A is the cancelled run: its result is
discarded by the server. B's result is the one the editor shows.

## 3. (c) What `finally` does on cancellation; (d) consequences

**An interrupt is an exception.** `checkInterrupted` → `throwInterruptException` = `throw (.internal
interruptExceptionId)` (`L/Lean/Exception.lean` 182–183). `try … finally` is `MonadFinally.tryFinally'`
(`L/Init/Control/Except.lean` 292–312), for `EIO` the `EStateM` instance (`Init/Control/EState.lean` 57):
the finalizer runs for EVERY exception value. What does NOT see an interrupt is `try … catch` in
`CoreM`-based monads (`Core.tryCatch`, `L/Lean/CoreM.lean` 786–799: `if ex.isInterrupt || ex.isRuntime then
throw ex`), so the translator's fallback handlers (which catch a failed route and try another) cannot
swallow it. Hence, on a cancelled run, every nested entry's `finally` (5544–5554) runs, innermost first:
the depth is decremented once per level and each level's seven caches are put back. On ONE thread of
control the cell returns to the value the run found.

**Can a task be dropped without its `finally`?** Not by cancellation: nothing pre-empts a Lean task; the
token is only a flag. A task that never STARTED never incremented the depth. The remaining ways are the
end of the process (the cells die with it) and a hard abort (stack overflow, `panic` with abort) — not
examined in the runtime sources (`src/runtime`), stated from the semantics of `Task`.

**What a cancelled OUTERMOST run leaves behind** (depth 0 at its entry, so its `finally` restores
nothing): depth 0; the child cache, the memo, the type cache and the seven per-module caches with its
partial content. Harmless on its own: the next command starts at depth 0 and empties all twelve.

**Depth leak — from the overlap, not from the cancellation.** 5432 `get` and 5529 `set (depth + 1)` are
~100 lines apart; 5545 is `modify (· - 1)`. One interleaving: A's outer entry and B's entry alive (cell =
2); A's child entry reads 2; B ends, `modify` → 1; A's child writes 2 + 1 = 3; A's child ends → 2; A ends
→ 1. The cell reads 1 with no run alive. From then on every public command of that FileWorker reads depth
≥ 1 at its start: nested branch for ever — the child cache and the memo are never emptied again, and every
later edit of a child's body is answered from the cache under the child's name until the worker is
restarted (the file is closed, the header changes, or the server is restarted). The opposite interleaving
(two entries read the same value) makes the cell too SMALL: a run that is nested believes it is outermost
and empties the caches of the run it is nested in. The subtraction is on `Nat`, so the cell never goes
below 0. Probability on a real session: not determined; it needs the overlap first.

**Wrong results.** With an overlap (or after a leak): `synthesizeChild` (8891) returns the cached pair for
the NAME. If the edit changed that child's body, the new top is built from the old child. Nothing downstream
notices: the Verilog is well-formed. In the editor this is the `#synthesizeVerilog` / `#writeVerilogDesign`
OUTPUT of the new text — and `#writeDesign`-style commands write FILES from it. A later batch build
overwrites those files with correct ones (fresh process).

**Relation to the endpoint premises.**
* `Start0 mref cref w` (`Tools/ShippingMachineRan.lean` 77–79): `∃ L : RefLaws, L.sval w = some
  synthesizeChild ∧ L.dval w = 0 ∧ L.quiet w` — the premise of the outermost endpoint
  (`machineRan_outermost`, 100). A run that starts during another run starts with the cell ≥ 1: `L.dval w =
  0` is false of any witness that describes the cell.
* `ChildBnd w` (`Tools/ShippingChildInv.lean` 600–601) = `∃ L, StartV L w ∧ L.quiet w`, `StartV` (508–509)
  = `sval = some synthesizeChild ∧ (dval = 0 ∨ CacheInv (L.val w))`. The depth-0 disjunct fails as above.
  The other disjunct, `CacheInv` (462–463: every entry of the child cache is a `RealChild` — the result of
  a run of the entry on that name from a state satisfying the invariant, 454–459), is exactly what a cache
  filled by a run on ANOTHER environment does not give: the entry under `c` is a result for the old
  constant `c`, not for the `c` this run's environment has. (`RealChild` quantifies over runs with the
  proof's `mref` / `cref`; a run of another command has other state references altogether.)
* Beneath both: `RefLaws` (331 ff.) states that reads of the cells return what the run last wrote
  (state-passing over `Void IO.RealWorld`). With a second thread writing the same cells this is not a
  property of the execution: there is no witness `L` for an interleaved run, so no endpoint with a
  `ChildBnd` or `Start0` premise says anything about it.
* Batch elaboration: no overlap (§1), every public command starts at depth 0 with all twelve cells emptied
  by its own entry — the situation the premises describe. Whether an actual run SATISFIES `Start0` is still
  a premise about the runtime (`G-mixdeep-outermost.md` §5, last paragraph); this round adds only that in a
  SERVER session it can be false, and how.

## 4. The controlled probe — `Tests/Compiler/DepthCancelProbe.lean`

Target-only (`lake build Tests.Compiler.DepthCancelProbe`, as `Tests.Compiler.DepthStartProbe` is built; not
imported by `Tests/AllTests.lean`). Logs only; asserts nothing; restores every cell in
a `finally`. One process, no server.

How a run is made long without editing the compiler: `sparkleChildSynth` (1040) is a PUBLIC cell holding the
child entry the translator calls for a `@[hardware_module]` call. The probe puts there a wrapper that, the
first time it is asked for one named child, raises a flag and holds until released (polling
`Core.checkInterrupted`, or not, or throwing an ordinary exception), then calls the real `synthesizeChild`.
While it holds, the run is inside the entry's `try` at depth 1 with its top module half built. Runs are
`synthesizeCombinational <decl>` on dedicated threads (`Core.wrapAsync … (some token)`, `EIO.asTask`), each
with its own `IO.CancelToken` — the shape of a server-elaborated command. The command's thread reads the
cells at each stop.

Limits, stated: (1) the wrapper replaces `sparkleChildSynth`'s content, so `sval = some synthesizeChild`
is false during the probe — it is an experiment on the cells, not an instance of the theorems; (2) "the
same name with another body" is PLANTED (the module compiled from `kidSOld` is put in the child cache under
the name `kidS`): two environments with a re-bodied declaration were not built (it needs `addDecl` of a
copied definition plus the `@[hardware_module]` tag from a `CoreM` program — more unbuilt machinery than
the observation is worth; the real-server procedure covers the real thing); (3) the lost-decrement
interleaving of §3 cannot be forced on the real entry from outside (the two operations are inside it): case
`model` performs the three operations on the real cell in that order — arithmetic, not a run.

PREDICTED lines (`T` / `F`; lists abbreviated; wire names not predicted):

| line | prediction |
|---|---|
| `DEPTHCANCEL clean topA` (and `topB`, `topS`) | `ok`; two modules (child, top); afterwards `depth=0 childCache=[…kidA]` |
| `DEPTHCANCEL clean topSOld` | `ok`; `the child cache has kidSOld: T` |
| `overlap A-held` | `A reached its hold: T`; `depth=1`; `childCache=[]`; `wireWidth` non-empty (A's input at least) |
| `overlap B-held` | `B reached its hold: T`; `depth B's entry found … = 1`; `child cache still has the sentinel …: T`; `wire-width cache still has every wire A had …: F`; `depth=2` |
| `overlap B-ended` | `B ok`; `B == its clean result: T`; `… A's wires again …: T`; `depth=1`; `childCache` = sentinel, `kidB` |
| `overlap A-ended` | `A ok`; `A == its clean result: T`; `depth=0`; `childCache` = sentinel, `kidB`, `kidA` (B's child still there: content of another run) |
| `stale A-held` | `T`; `PLANTED …: T`; `depth=1` |
| `stale B-ended` | `B ok`; **`B == its clean result: F`**; B's modules name the `kidSOld` module, the clean ones `kidS`; `depth=1` |
| `stale after` | `A ok, depth 0`; `topS from that depth: ok, == its clean result: T` |
| `cancel-check A-held` | `T`; `depth=1` |
| `cancel-check A-ended` | **`A INTERRUPTED`**; `depth back to 0 …: T`; the per-module cells keep A's partial content (`wireWidth` non-empty) |
| `cancel-check B-ended` | `B ok`; `== clean: T`; `the sentinel is gone …: T`; `depth=0` |
| `cancel-nocheck A-cancelled` | `A reached its hold: T`; **`… A has ended: F`**; `depth=1` |
| `cancel-nocheck B-ended` | `B ok`; `== clean: T`; `child cache still has the sentinel (… nested branch): T`; `depth=1` |
| `cancel-nocheck A-ended` | `A INTERRUPTED` (it meets a check in the child's synthesis after the hold; `ok` if it meets none — less likely); `depth=0` |
| `throw A-ended` | `the exception was thrown: T`; `A ok` or `ordinary error` — NOT predicted (it depends on whether a fallback handler catches a failed child); `depth=0` either way |
| `model` | `the cell reads 1` |
| `DEPTHCANCEL SUMMARY` | the same facts in one line |

If a prediction about the route is wrong (the child of `topA` is not compiled through `sparkleChildSynth`),
`A reached its hold` reads `F`, the run simply ends, and the later lines of that case show depth 0: the
probe says so instead of hanging (every wait has a budget of 30 s).

Reading the two `B == clean` lines of `overlap` and `cancel-nocheck`: `T` there does NOT mean an overlap is
harmless — in the probe A is HELD while B runs, so nothing of A is lost when B empties and restores the
per-module caches; in a real overlap A is running.

## 5. The real language server — procedure (not run)

Usable headlessly here: `lake` and `lean` of the toolchain are on PATH; `lake serve` speaks LSP on stdin /
stdout; `python3` is on PATH. `scripts/shipping-coverage/ls_depth_probe.py` uses the standard library only.

The file under test, `scripts/shipping-coverage/ls_depth_probe.lean`, defines its own wrapper command
`#ls_depth "<tag>" <mode> <holdMs> <decl>`: it appends `ENTRY depth=<d>` (the depth the command finds BEFORE
it calls the entry), `HOLD-START` / `HOLD-END`, `RETURNED`, `EXIT depth=<d>` with millisecond times to
`.lake/build/gen/ls-depth/log.txt` (a file: diagnostics of a cancelled elaboration are not published), and
runs the real `synthesizeCombinational`. With `holdMs > 0` the first child entry of the run waits that long
inside the entry (same device as §4). The file has `def lsAnchor : Nat := 0`, then `#ls_depth "long" …
topL`, then `#ls_depth "quick" … topQ`.

Steps (the script does them; by hand they are the same in an editor):
1. `lake build Sparkle` finished; no other build running. Run under the memory-capped runner:
   `scripts/shipping-coverage/cgrun.sh -n lsdepth -m 3G -t 900 -- python3 scripts/shipping-coverage/ls_depth_probe.py --mode nocheck --hold-ms 8000 --trials 3`
2. The script starts `lake serve`, sends `initialize` / `initialized`, then `textDocument/didOpen` with the
   file's text (`MODE`, `HOLDMS` substituted).
3. It waits for the marker file `.lake/build/gen/ls-depth/entered`: the old `long` command is inside the
   entry, depth 1.
4. It sends `textDocument/didChange` (version 2) changing `lsAnchor`'s `0` to `1` — shape S1 of §1.
5. It waits for a second `long@… ENTRY` line, then shuts the server down and prints the log, the
   diagnostics and a verdict per trial, and `LSDEPTH SUMMARY`.

Three settings, three questions:

| setting | question | "reproduced" | "not reproduced" |
|---|---|---|---|
| `--mode nocheck` (the old run cannot be interrupted for `holdMs`) | does the SERVER let a new command start while a cancelled one is still running? | a `long` or `quick` `ENTRY` line of the new version with `depth=1` (or more), written BEFORE the old run's `EXIT` | every new `ENTRY` has `depth=0` and comes AFTER the old run's `EXIT`: the server serialises (then §1's reading of 612 / 640 is wrong, and the concern is void for this toolchain) |
| `--mode check` (the old run polls `checkInterrupted` every 10 ms) | with prompt checks, is the old run gone before the new command starts? | a new `ENTRY` with `depth ≥ 1` | old `EXIT` (after an interrupted hold: `HOLD-END` within ~10 ms of the edit) before the new `ENTRY`, `depth=0`, in every trial: with checks at least every 10 ms the window is not hit in N trials — evidence of rarity, not of impossibility |
| no hold, a REAL long design (replace `topL` by a top whose synthesis takes seconds, `holdMs` 0; the marker is then not written — send the edit after a fixed delay) | does the compiler's own code stay check-free long enough? | a new `ENTRY` with `depth ≥ 1` | `depth=0` in all trials: "not reproduced on the real LS with design X, N trials" — to be recorded as that, no more |

PREDICTED: `nocheck` → REPRODUCED in every trial (new `long` ENTRY `depth=1` a few tens of milliseconds
after the edit, the old run's `EXIT` ~8 s later). `check` → SERIALISED in most or all trials. Real design:
not predicted.

Also worth reading in the log of a `nocheck` trial: after both runs ended, a further edit (by hand) and its
`ENTRY depth=` — a non-zero value there with no run alive would be the leak of §3 (not expected in a
handful of trials; the interleaving is narrow).

Caveats of the script, by reading only: the server may want `initializationOptions` or reject
`languageId` "lean4" (the diagnostics and the INCONCLUSIVE verdict would show it); the FileWorker runs
`lake setup-file`, which builds missing imports; `IO.monoMsNow` values of two THREADS of one process are
comparable, of two processes not (each trial is one FileWorker).

## 6. What a per-command state would have to cover (for judging the impact later; no design here)

`Elab.lean` has 27 `initialize`d `IO.Ref`s. Twelve carry state that results depend on and that a run
assumes it owns: the depth (961) and eleven maps / sets — sub-module memo (1024), child cache (1032), type
cache (1088), sub-instance outputs (1053), single-output map (1080), fvar value map (984), fvar zeta set
(976), wire-width (164), let (991), loop (1008), wire-canon (1014) caches. They would have to live in the
run (a context or state value created by the public entry and threaded through `CompilerM` / the child
entry), not in the process. `sparkleChildSynth` (1040) is a knot-tying constant and could stay. The other
fourteen are profiling counters (757–758, 950–951, 1093–1094, 1101–1106, 1144–1145): shared counting is
only imprecise. The proofs speak about these cells through `RefLaws` (`val`, `sval`, `dval`, and
`RefLawsM.mval`): a change of where the state lives changes what those laws are about.

## 7. Could not be determined by reading

* Whether anything in the server serialises old and new elaboration after all (the reading of 612, 640 and
  `Command.lean` 430 says no) — §5 `nocheck`.
* The longest check-free stretch inside the entry on real designs, i.e. the real size of the window.
* Runtime details: a dropped / unreferenced running task, hard aborts (`src/runtime` not read).
* Whether the FileWorker debounces edits before `updateDocument` in a way that matters here (the 200 ms
  sleep at `FileWorker.lean` 383 is on the header-restart path).
* For the probe: that `topA`'s child is compiled through `sparkleChildSynth` on every route; whether an
  ordinary exception at the child entry is caught by a fallback (case `throw`); `Core.wrapAsync` +
  `EIO.asTask` from `liftCoreM` inside `run_cmd` (API read at `CoreM.lean` 562–578, not built); whether
  results compared with `==` are equal across two clean runs at all (if the compiler numbers wires
  differently on a second run in one process, `== clean` reads `F` everywhere — the `clean` lines and the
  module lists show it).
* Whether the type cache can give a stale TYPE across versions (keyed by `Expr`).

## 7. MEASURED (integrator, 2026-10-14, poc b3e1ba42 + these files; no compiler change)

### 7a. Controlled one-process probe `Tests.Compiler.DepthCancelProbe`
`cgrun -n depthprobe -m 3G -j 1 -- lake build Tests.Compiler.DepthCancelProbe`: exit 0, peak 0.35 GB.
Every line as predicted in §4 except one:

* `clean`: all four ok, depth 0 afterwards (the `modules [...]` list shows the child module only).
* `overlap`: B entered at depth 1, sentinel kept (nested branch), A's wires NOT visible while B inside, B and A
  each == clean, depth 0 at the end — as predicted.
* `stale`: **B (nested, name-keyed child cache) == clean: F** — it returned the module of `kidSOld` under the
  name `kidS`; the same B from depth 0 == clean: T. As predicted. NOTE: the stale entry was PLANTED by the probe.
* `cancel-check`: A INTERRUPTED, depth back to 0, next run from depth 0 == clean — as predicted.
* `cancel-nocheck`: A alive 300 ms after cancellation at depth 1, B meanwhile nested and == clean.
  **Differs:** A then ended `ok`, not `INTERRUPTED` (the alternative §4 called less likely: no interrupt check
  was met after the hold). Depth 0 at the end.
* `throw`: ordinary error, depth 0 afterwards.
* `model`: the three operations in the §3 interleaving leave the cell at 1 with no run alive (arithmetic on the
  real cell, not a run of the entry).

### 7b. Real language server `scripts/shipping-coverage/ls_depth_probe.py`
`cgrun -n lsdepth-{nocheck,check} -m 3G` (`lake serve` of the installed toolchain), hold 8000 ms:

* `--mode nocheck --trials 3`: **REPRODUCED 3/3** — after the edit, the re-elaborated `long` command ENTERED at
  `depth=1` (~310–340 ms after the first ENTRY) while the old run was still holding inside the entry. As predicted.
* `--mode check --trials 5`: **REPRODUCED 5/5 — prediction (SERIALISED) WRONG.** Even with the old run polling
  `checkInterrupted` every 10 ms, the new command's ENTRY (depth 1) precedes the old run's HOLD-END/EXIT by
  0–4 ms in every trial (e.g. trial 1: new ENTRY 306501105, old HOLD-END 306501108, EXIT 306501109). The old
  run's EXIT leaves depth 1 (the new run's), i.e. the decrement is not lost in these trials.
* No leaked depth with no run alive was observed (the §3 interleaving was not forced on the real entry).

### 7c. What this does and does NOT establish
Established (measured): on this toolchain the language server starts the re-elaborated command while the
cancelled run of the old version is still inside the synthesis entry, so the new run takes the NESTED branch
(it does not reset the per-process caches) — with and without prompt interrupt checks.
NOT established: a wrong module produced in an ordinary editing session. The wrong result in 7a needs a stale
same-named child-cache entry, which the probe PLANTED; whether the old run can leave one that the new run reads
under a real edit is not measured. Batch builds (`lake build`) are unaffected by reading (§1: one run at a time).
No compiler change is proposed here; per ruling 5 (2026-10-14b) this is the reproduction investigation only.
