# A-keccak-2 — the interval after `composedNR 1`; the probe repaired; the proposal (round par/a-26)

STATE: **WRITTEN, NOT BUILT, NOT RUN.** [R] read in the source; [M] measured
by the integrator's run `20261013-101653-sponge-step2` (its progress file
`~/sparkle-work/keccak-sponge-step.log`, `samples.txt`, and the first run's
`log.txt`), read here; [P] prediction. Base `052d4b51`, branch `par/a-26`.
New files: `Tests/Compiler/KeccakSpongeStepProbe2.lean`, this note. Nothing
existing is changed.

## (a) What runs between the two progress lines [R]

Both call sites are in ONE function, `generateCoreNR`
(`Tools/ShippingMachineDepthCommandR.lean` 182–562):

    185:  progress s!"{declName}: composedNR {dep}"
    560:  progress s!"{name}: checking"

`composedNR` is not another function: it is the label of `generateCoreNR`'s
start. There is no `progress` call between 185 and 560 in this file, and of
the functions called in between only two can write one, both silent here
[M]: `generateRunOfR` → `generateCombNR` → `generateComposedR` (line 43;
`ShippingMachineComposeRCommand` 57, 293) returns at its first line because
`wKeccakF.machine_composedRA` existed (step 9), and `generateRunOfR` returns
at 167 because `wKeccakF.seq_child_runN_ofR0` existed (step 11).

So the interval is, in order:

| lines | what | on the sponge |
|---|---|---|
| 186–190 | `readMachine f`, `endpointParts` | ≈ 5 s [M: step 1] |
| 194–210 | the children's run theorems | `readMachine c` twice (≈ 20 s), `bndOfComposed`; nothing generated |
| 212–273 | telescope, the families `bsC`, `outsC`, `S` | term building |
| 283–291 | `closesAtNames c` | one more `readMachine c` (≈ 10 s) |
| 292–345 | the children's predicates and premises | term building |
| 346–352 | `machine_linkedT_callsRN`, 1 + 7 `mkDecideProof` | NOT evaluated here (`mkDecideProof` builds the term; the kernel pays after 560) |
| **354–476** | **the per-call loop: `hcalls`, one tactic proof + `Meta.check` per entry** | **27 entries** |
| 477–496 | the chain over the entries, `check hcalls` | `Meta.check` of the whole `hcalls` once more |
| 499–537 | `hrunN`: per entry `closesAtProof` + one `exact` | 27 entries, identical up to `k` |
| 538–559 | the second chain, the boundary bundle, the final term | term building |

**The per-call loop IS in the interval** (it is most of it). What the run
adds to round a-25's reading [M]: steps 9, 10, 11 — everything
`#machine_design_svNR` does before `generateCoreNR`'s own work — cost 12.6,
2.6, 12.7 s; step 14 wrote `composedNR 1` at once and never wrote
`checking` in 38 min: the kernel check (560–561), `generateShipsNR` and
`compose` were NOT reached. The time is in 186–559.

Corrected culprit analysis: unchanged in substance, sharper in location.
Candidates inside the interval, by reading: the loop (27 × 26 = 702 argument
facts, each with a reduction of the parent's reflected `let` through
`typedVal`; 27 × 25 `split`s on a goal carrying the remaining arguments; 27
final `rfl`s through the 26-deep `extendBits` nest; then `Meta.check` of
each entry AND of all of `hcalls` again at 495); `hrunN` (27 ×
`closesAtProof`, cheap by reading: a handful of `isDefEq` on premise types).
NOT in the interval: any `decide` of the parent's data in the kernel, the
kernel check of the theorem. Which piece of the loop dominates is still not
known: the pieces never ran (next section). Memory [M]: the same curve as
before — ≈ 0.95 GB at t = 300 s, 2.68 GB at t ≈ 1050 s (`memory.high`),
throttled from then on; so of the "38 minutes" about 13 were unthrottled.

## Why steps 12–13 left no line [M]+[R]

Not the logging path. `KeccakSpongeStepProbe.lean` line 632 still reads
`runStep … needs do` (the integrator's rename fixed 585 and 630; 632 is the
third use). `needs` being a token since line 556, the `elab "#sponge_calls"`
did not compile; its two uses (719, 725) were then errors of the build's
message log only — in the first run's log the same shape is visible:
`719:0: elaboration function for … «command#sponge_calls_____At[_,,]Needs[_,,]» has not been implemented`.
`#sponge_fn` (585 only) was repaired by the rename, hence steps 8–11 and 14.
My error; the lesson is the integrator's: no local named like a declared
keyword.

## (b), (c) The repaired probe: `Tests/Compiler/KeccakSpongeStepProbe2.lean`

Sub-functions of `generateCoreNR` that are separate `def`s [R]:
`readMachine`, `endpointParts`, `generateSeqChildN`, `generateRunOfR`
(→ `generateCombNR`, `bndOfComposed`), `closesAtNames`, `closesAtProof`
(→ `andParts`, `closingThm?`, `reflectAt?`), `nameCases`, `sigAtPos`,
`findCall`, `rangeSyntax`, `memTactic`, `proveByTacticT`, `conj`, `projs`,
`addTheorem`. The loop body, `hrunN`'s body and the chains are INLINE: not
callable. So the copy approach stays, now covering the whole interval:

* pieces `setup.read`, `setup.children`, `setup.names` call the separate
  defs; the 8 parent decides are kernel-checked alone (what the kernel would
  pay after 560);
* per chosen entry: `hrunN.closing`, `hrunN.tactic` FIRST (cheap by
  reading), then `refine`, `r`, `l`, `b`, `f.refine`, `f.fin`, `f.hb`,
  `f.hv.simp`, `f.hv.split`, `f.hv.leaf j` (one piece per leaf),
  `instantiate`, `Meta.check`;
* every piece writes `START` before and `OK (ms)` / `FAILED (ms) — message`
  after, to the progress FILE; a failed or over-budget piece does not stop
  the others;
* budgets: per piece a HEARTBEAT limit (`Core.Context.maxHeartbeats` with
  the counter restarted, caught by `tryCatchRuntimeEx`; for the kernel
  pieces the option `maxHeartbeats`); per step a soft wall limit checked
  BEFORE each piece. Achievable granularity: one `Tactic.run` call (10 per
  entry + one per leaf). Inside one call there is no wall-clock check — only
  the heartbeat limit, which counts allocations, not seconds;
* commands `#sp2_*` with the keyword `given`; no identifier of the file is
  `given`, `budget`, `wall` (checked by a scan of the code after the first
  `elab`); step `0d` runs the pieces command on `Nat` — its `FAILED` line in
  the file proves the command exists, seconds into the file;
* the full `generateCoreNR` / `generateShipsNR` / `generateDesignNR` (steps
  15–17) run only with `SPARKLE_SPONGE_FULL` set: by default nothing in the
  file can eat the limit.

Run:

    SPARKLE_MACHINE_PROGRESS=$HOME/sparkle-work/keccak-sponge-step2.log \
      ~/sparkle-work/bin/cgrun.sh -n sponge-step3 -m 3G -s 0 -t 2400 -- \
      lake build Tests.Compiler.KeccakSpongeStepProbe2

Budget [P]: steps 0–11 ≈ 3.5 min [M for 2–11]; step 12 (k = 0) and step 13
(k = 1, 26): 20 000 k heartbeats per piece, soft limit 420 s each. Reading
the result: the pieces' `OK (ms)` of k = 0 times 27 is the loop's cost;
k = 1 against k = 0 says whether anything is reused between entries.

Risks: the copy is now ≈ 330 lines (the children's premises 283–345 and
`hrunN` 499–537 added); a slip is a `FAILED` line of that piece or of the
step. Heartbeat budgets are not seconds: a piece may take minutes within
20 000 k; under `memory.high` everything is slower.

## (d) Proposal: prove the argument facts once per group

A change of `generateCoreNR` (and its non-R twin `generateCoreN`,
`ShippingMachineDepthCommand.lean` 234–343, the same loop) — a decision for
the user; nothing is written under `Tools/` in this round. To be confirmed
by the probe first: it is the right change if `f.hb + f.hv.*` dominate an
entry; if `f.fin` or `b` dominate, see "if the probe says otherwise".

**What depends on what** [R], in an entry's proof (439–470):

| part | depends on |
|---|---|
| `A`, `B` (401–409) | the callee and the call's argument Signals: the GROUP (callee, argument lets) |
| `case l` (`args_facts`), `case r` (`InRange`) | the group |
| `decoded_eq`'s `hb : boolsOf … = A`, `hv : bitsOf … = B` (457–470) | the group |
| `k'`, the `rfl`s of the skeleton, `fun τ => rfl`, the final `.trans rfl` | the entry |
| `case b` | the callee (and `k` only through `rfl`) |

**Minimal change.** Before the loop, group the entries by `(c, argsK)` (the
reader's `shape.insts` already carries both). Per group, ONCE, build `A`,
`B` and prove three local facts with the tactic text that is there now:

    hbG : boolsOf Dc bsInE vs = A            -- the first `by` of 457–463
    hvG : bitsOf Dc bsInE vs = B             -- the second `by` of 464–470
    hlG, hrG                                 -- `case l`, `case r`

bound as local hypotheses and abstracted into the entries' proofs the way
`hclC` is at 534–536 (`mkLambdaFVars #[h] pr |>.beta #[proof]`), so the term
shares them. Per entry the tactic becomes

    refine ⟨rfl, args, rfl, ?b, hlG, hrG, k', _, _, rfl, rfl, ?f, fun τ => rfl⟩
    case f => exact (congrArg (fun l => l[k']?) (decoded_eq srcS hbG hvG)).trans rfl

Counts on the sponge: 702 argument facts → 26; 27 × 25 `split`s → 25; per
entry remain the skeleton, `case b` and the final `rfl`. The per-entry
`check proofK` (475) and `check hcalls` (495) stay.

**What it does not change.** The STATEMENT of `f.machine_composedNR{n}`
(the type is computed from the head and its arguments before the loop), so
no statement downstream (`machine_ships_hierNR`, `machine_design_svNR`,
`machine_design_noPortsNR*`, the closed forms, the goal gaps). Only proof
terms.

**Which built endpoints it regenerates.** Every `#machine_design_svNR` in
the tree (and the old `#machine_design_svN` / `#machine_composedN` if the
twin is changed too): `parent`, `mid`, `chained`, `grand` (2), `two`,
`loopParent`, `grandH` (1, 2), `mid2`, `mixD1` (1, 2), `topD2` (2, 3),
`mixDeep` (2), `engineOnce`, `twinCalls`, `mesh2x2`. All must stay `isDefEq`
in their statements; the family tests' compare path
(`#machine_no_ports_kids` on an existing endpoint rebuilds and compares,
`…_regen`) and every audit's premise inventory then pass unchanged.

**How to do it without risk to the built state** (the repository's rule: new
compiler pieces in new files). A NEW file
`Tools/ShippingMachineDepthCommandRG.lean` with `generateCoreNRG` writing
`f.machine_composedNRG{n}`, the old generator untouched. A test generates
both on the built declarations and asserts `isDefEq` of the two statements
and standard axioms. Only then is `generateCoreNR` pointed at the new body
(one line), `AllTests` rebuilt.

**Validation without the sponge.** `mesh2x2` (`Tests/Compiler/
MultiInstanceTest.lean` 46–55): four instances of `pe`, two fields each = 8
entries in 4 groups of 3 arguments: 24 argument facts → 12 [P]; `twinCalls`
similarly. Measurable: wall time of `generateCoreNR` against
`generateCoreNRG` on `mesh2x2` under `SPARKLE_MACHINE_PROGRESS` (the two
existing lines bracket it), expected ratio for the argument-fact part 2 : 1,
for the whole less. `mesh2x2` shows that the sharing is CORRECT on several
groups (the grouping key matters there; the sponge has one group); the
SIZE of the gain shows only on a wide group — `KeccakSpongeStepProbe2`'s
`f.hb + f.hv.*` against the entry's total is the prediction for the sponge:
if they are a fraction φ of an entry, the loop drops from 27 T to about
(27 − 26 φ) T.

**If the probe says otherwise** [P]:

* `f.hv.leaf` dominates (the `rfl` through `typedVal`): the sharing still
  divides it by 27; if 26 leaves are still too slow, a lemma giving
  `(letObsB …)[l]?` for a `let` whose term is an input / a slot read /
  one operator, instead of evaluating `letVal` over all lets;
* `f.hv.split` dominates: besides the sharing, replace `repeat' split` by a
  lemma `extendBits_apply` (at its own position; at another position) and a
  `decide`d position list — no `simp` over the arguments;
* `f.fin` dominates (per entry, not shared): state the entry's output by a
  lemma "the extension at position `kD + k` is the `k`-th term" generated
  with `machineExt` (one `rfl` per entry at definition time, when the nest
  is being built) instead of peeling the nest in the caller;
* `Meta.check` dominates: drop the per-entry `check` (475) — the kernel
  checks the theorem anyway; keep `check hcalls` (495) or neither;
* `b` dominates: `case b`'s `decide` is the same for every entry of a
  callee — once per callee.

## Run records: `KeccakSpongeStepProbe2` (integrator, 2026-10-13) — log-only, claims nothing

1. `20261013-110527-sponge-step3`: the pieces stopped at `setup.children` — the per-piece heartbeat budget was a tenth of
   Lean's default (`cfg.hbK * 1000` in `Core.Context.maxHeartbeats` is option-units × 1; the error printed
   "maximum number of heartbeats (20000)"). Integrator fix: the unit (three places). Also: the reason steps
   12–13 of the FIRST probe left no line was my incomplete rename there (a third `needs` at line 632).
2. `20261013-111028-sponge-step4` (3 GiB, swap 0, limit 2400 s): result=success, memory_peak_file=1385451520, no throttling.
   MEASURED, entries k = 0 and k = 1 of the sponge's per-call loop (the copy's pieces, not the generator's own run):

   | piece | k = 0 | k = 1 |
   |---|---|---|
   | `b` — the child's run theorem at the instance (+ decide of argPorts' length) | 92 866 ms | 93 265 ms |
   | `f.hb` — the Bool family | 11 957 ms | 11 921 ms |
   | `f.hv.split` | 2 107 ms | 2 105 ms |
   | `r`, `f.hv.simp`, `f.fin`, `f.refine`, `refine`, `l`, `hrunN.*` | < 0.5 s each | same |
   | parent decides (kernel, alone) | 1–27 ms each | same |
   | set-up (read 5 s, children's theorems 20 s, names 10 s) | once | once |

   The last piece `f.hv.leaf 0` FAILED in the copy (`rfl` failed: a slip of the copied tactic, not a
   finding), so the entry's proof was not completed and `Meta.check` / the kernel check were not measured.
   Term sizes logged: the parent's extension body ≥ 5 000 000 nodes (capped), the Bool extension's body
   2 184 227.

   Reading: about 108 s per entry × 27 entries ≈ 49 minutes before any checking — consistent with the
   earlier timeout inside this interval. The dominant piece is `b` (≈ 86 %), NOT the argument-family
   facts the first analysis pointed to (`f.hb` + `f.hv.*` ≈ 13 %). All 27 entries are fields of ONE
   instance with the same argument lets, so `b` is the same statement 27 times.

```
P2   setup.head done: tree sizes (capped at 5000000) — the calls' premise 35995, the runs' premise 449 [VmRSS:	 2269744 kB] [VmHWM:	 2352844 kB]
P2   OK call 0: hrunN.closing (closesAtProof Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF) (1 ms) [VmRSS:	 2269748 kB] [VmHWM:	 2352844 kB]
P2   OK call 0: hrunN.tactic (machineRunNC_of_real, the closing derived) (91 ms) [VmRSS:	 2243588 kB] [VmHWM:	 2352844 kB]
P2   pieces of Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW: tree sizes (capped at 5000000) — the extension's body 5000000, the Bool extension's body 2184227, the let obser
P2   call 0 of Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF: field l0 = the child's output 0; argument lets [7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
P2   OK call 0: refine (the skeleton) (58 ms) [VmRSS:	 2255824 kB] [VmHWM:	 2352844 kB]
P2   OK call 0: r (InRange of 27 inputs) (403 ms) [VmRSS:	 2246908 kB] [VmHWM:	 2352844 kB]
P2   OK call 0: l (args_facts: decide, simp of the let observations' length) (26 ms) [VmRSS:	 2234808 kB] [VmHWM:	 2352844 kB]
P2   OK call 0: b (the child's run theorem at the instance; decide of argPorts' length) (92866 ms) [VmRSS:	 2418444 kB] [VmHWM:	 2441608 kB]
P2   OK call 0: f.refine (congrArg … (decoded_eq … ?hb ?hv) |>.trans ?fin) (87 ms) [VmRSS:	 2390368 kB] [VmHWM:	 2441608 kB]
P2   OK call 0: f.fin (rfl: the child's source at field 0 on the families = the parent's extension at position 37) (197 ms) [VmRSS:	 2390928 kB] [VmHWM:	 2441608 kB]
P2   OK call 0: f.hb (the Bool family: funext, simp only [extendBools], split, close) (11957 ms) [VmRSS:	 2266192 kB] [VmHWM:	 2441608 kB]
P2   OK call 0: f.hv.simp (funext, simp only [extendBits] with zetaDelta) (398 ms) [VmRSS:	 2254200 kB] [VmHWM:	 2441608 kB]
P2   OK call 0: f.hv.split (repeat' split) (2107 ms) [VmRSS:	 2243852 kB] [VmHWM:	 2441608 kB]
P2   FAILED call 0: f.hv.leaf 0 (bitsOf_at (decV_valsOf rfl (by decide) rfl), or rfl) (816 ms) — Tactic `rfl` failed: The left-hand side
P2   setup.head done: tree sizes (capped at 5000000) — the calls' premise 35995, the runs' premise 449 [VmRSS:	 2278472 kB] [VmHWM:	 2441608 kB]
P2   OK call 1: hrunN.closing (closesAtProof Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF) (1 ms) [VmRSS:	 2278472 kB] [VmHWM:	 2441608 kB]
P2   OK call 1: hrunN.tactic (machineRunNC_of_real, the closing derived) (88 ms) [VmRSS:	 2249568 kB] [VmHWM:	 2441608 kB]
P2   pieces of Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW: tree sizes (capped at 5000000) — the extension's body 5000000, the Bool extension's body 2184227, the let obser
P2   call 1 of Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF: field l1 = the child's output 1; argument lets [7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
P2   OK call 1: refine (the skeleton) (56 ms) [VmRSS:	 2259820 kB] [VmHWM:	 2441608 kB]
P2   OK call 1: r (InRange of 27 inputs) (383 ms) [VmRSS:	 2249952 kB] [VmHWM:	 2441608 kB]
P2   OK call 1: l (args_facts: decide, simp of the let observations' length) (23 ms) [VmRSS:	 2249984 kB] [VmHWM:	 2441608 kB]
P2   OK call 1: b (the child's run theorem at the instance; decide of argPorts' length) (93265 ms) [VmRSS:	 2415664 kB] [VmHWM:	 2466072 kB]
P2   OK call 1: f.refine (congrArg … (decoded_eq … ?hb ?hv) |>.trans ?fin) (92 ms) [VmRSS:	 2377536 kB] [VmHWM:	 2466072 kB]
P2   OK call 1: f.fin (rfl: the child's source at field 1 on the families = the parent's extension at position 38) (201 ms) [VmRSS:	 2345484 kB] [VmHWM:	 2466072 kB]
P2   OK call 1: f.hb (the Bool family: funext, simp only [extendBools], split, close) (11921 ms) [VmRSS:	 2205660 kB] [VmHWM:	 2466072 kB]
P2   OK call 1: f.hv.simp (funext, simp only [extendBits] with zetaDelta) (403 ms) [VmRSS:	 2187084 kB] [VmHWM:	 2466072 kB]
P2   OK call 1: f.hv.split (repeat' split) (2105 ms) [VmRSS:	 2186380 kB] [VmHWM:	 2466072 kB]
P2   FAILED call 1: f.hv.leaf 0 (bitsOf_at (decV_valsOf rfl (by decide) rfl), or rfl) (818 ms) — Tactic `rfl` failed: The left-hand side
```
