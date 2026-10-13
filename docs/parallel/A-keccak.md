# A-keccak — `wKeccakF` as a proper test; where the sponge's depth endpoint spends its time (round par/a-25)

STATE: **WRITTEN, NOT BUILT, NOT RUN.** Nothing below is measured in this
round. [R] = read in the source at the line given; [M] = measured by the
integrator's run `20261013-080244-keccak-probe` (the record under
`~/sparkle-work/runs/`, the probe's own file `.lake/keccak-probe.log`), read
here, not re-run; [P] = PREDICTION.

Base: `7a2039ec` (`poc/roundtrip-proof`), branch `par/a-25`. Files of this
round (all new, nothing existing is changed, nothing under `Sparkle/`,
`Tools/`, `IP/`):

| file | what | in `AllTests`? |
|---|---|---|
| `Tests/Compiler/KeccakSpongeLogLib.lean` | logging helpers (the Keccak probe's `clipStr`, `probeToFile`, `describeRead`, restated: that file cannot be imported, it generates the constants) | no (imported by the two below) |
| `Tests/Compiler/OneOutWKeccakFTest.lean` | `wKeccakF` AS AN ENTRY: the built commands + the family audit | **target-only** (recommendation, §2) |
| `Tests/Compiler/KeccakSpongeStepProbe.lean` | log-only probe of the depth generator's sub-steps on the sponge | target-only, never imported |
| this note | | |

The three test files generate the same constants (`keccakRcHW.gate_*`,
`wKeccakF.machine_*`) as `Tests/Compiler/KeccakProbeTest.lean`: NEVER import
two of {`KeccakProbeTest`, `OneOutWKeccakFTest`, `KeccakSpongeStepProbe`}
together.

## 0. Corrections to `B-keccak.md`, from the run's own files [M]

1. **The sponge has 27 call entries, not 26.** Step 4's line: `call
   entries=27 … distinct (callee, argument lets) groups (1): [wKeccakF with
   argument lets [7 … 32]]; instFields (27): [l0 … l24, round, done]`. A
   structure call gives one entry per FIELD of the result structure, read or
   not (`entriesOfCalls`, `Tools/ShippingMachineCommand.lean` 2079–2083 [R]).
   So `kf.round`, which the source never reads, IS an entry; `B-keccak.md`
   §3 item 3 ("an unread child output … ports READ or all ports") does not
   arise at the reader's level: all 27 outputs of the child are entries of
   the one instance. Other data of that line: `nDecl=37`, `binders=129`
   (37 + 30 slots + 35 lets + 27 entries), `lets=35`, 26 argument lets.
2. **The generators' `progress` lines were never going to appear.** The
   run's `env.sh` has no `SPARKLE_*` line: `SPARKLE_MACHINE_PROGRESS` was not
   set. The probe then wrote to its fallback `.lake/keccak-probe.log`, and
   `Tools.ShippingMachineCommand.progress` (548–555 [R]) writes ONLY when the
   variable is set. "The generator's own progress lines stop at the START
   line" therefore implies NOTHING about where the generator was.
3. **"RSS peak ≈ 2.3 GB" is mostly the mapped oleans.** VmHWM was 1.83 GB at
   step 0a, before any Keccak command. The cgroup's `memory.current`
   (`samples.txt`) was 0.73–0.85 GB from t = 60 s to t = 320 s — the whole of
   steps 0–12 (197 s by the probe's clock) lies in that window.
4. **Step 13 was throttled for about three quarters of its time.** `memory.current` grew
   almost linearly from ≈ 0.75 GB (t ≈ 300 s) to `memory.high` = 2.74 GB at
   t = 989 s (≈ 2.6 MB/s), then crept to 3.0 GB at t = 3590 s
   (`memory.events`: `high 64280`, no `max`, no OOM). From t ≈ 989 s on the
   process ran under reclaim throttling. What the run establishes is: step 13
   needs more than ≈ 2 GB above the level it started at, reached within
   ≈ 11 min of generation. It does NOT establish that step 13 needs more
   than an hour of computation, nor that it diverges.

## 1. `wKeccakF`: `Tests/Compiler/OneOutWKeccakFTest.lean`

Modelled on `OneOutMidHTest.lean` (BUILT): first a `run_cmd` that LOGS the
reader's data of `wKeccakF` and `keccakRcHW` and throws only on a wrong name
or a name clash; then the built commands in the probe's order —
`#gate_child keccakRcHW`, `#machine_endpoint`, `#machine_linked`,
`#machine_composed`, `#machine_closes_at`, `#machine_design_svHR` on
`wKeccakF` (the probe's steps 5–8, 10, 11; step 9 is the sponge's and is not
in this file) —; `#machine_oneout_try wKeccakF "GENERATED"`;
`Tests.Compiler.OneOutFamilyTest.audit wKeccakF [keccakRcHW] false` (premise
lists, `other` = the closing premise only / NONE, the eight checker
constants neither written nor hidden, standard axioms of every generated
constant, the goal-gap theorem with no NOT ALLOWED line); last the scope
facts asserted on the reader's data (one call entry `keccakRcHW`,
`instFields = []`, 27 registers = 1606 bits, `nDecl = 27`, outputs `l0 …
l24, round, done`) and the summary line with the SCOPE.

| endpoint | premise of `wKeccakF.machine_design_svHR` | predicted state |
|---|---|---|
| `wKeccakF.machine_design_svH_full` (+ `_closed`) | A₁ `shipsHierHCheck D.modules b` | WRITTEN, NOT BUILT — predicted absent [P]; the generator returned GENERATED once inside the log-only probe [M], nothing kept, nothing audited |
| | A₂ `kidsComb D.modules (checkedOptimize b).body` | predicted absent, pending build |
| | A₃ `designCheck (childMap D.modules) 0 (checkedOptimize b)` | predicted absent, pending build |
| | A₄ `outsCheck (childMap D.modules) 0 (checkedOptimize b)` | predicted absent, pending build |
| | `MachineClosesAt wKeccakF` (open form) | predicted absent in `_closed`, pending build |
| | `hr`, `MachineDefines wKeccakF`, `EntryDefines keccakRcHW`, `ChildBnd` | run boundary: they stay premises |

Not known before the build [P]: the audit's parts that the probe did not run
(the `hidden` expansion on statements over a 124-binder shape, `collectAxioms`
on ≈ 30 constants, `gapOf`). Their COST on this declaration is unmeasured.

SCOPE: ONE declaration, `wKeccakF`, as an entry, depth 0; data conditions
decided per declaration; the run, the two reflections and `ChildBnd` stay
premises; compiler guards with fallback; `DesignSV` of the module list — not
the SV string, not `#sim`. Not `wKeccakF` as a child; not Keccak's function.

## 2. `AllTests` or target-only — what was found

* **How lake schedules [M].** `cgrun.sh -j N` does one thing: `export
  LEAN_NUM_THREADS=N` (default 2; `~/sparkle-work/bin/cgrun.sh` 34, 87 [R]).
  It does not limit lake's jobs separately; lake's job parallelism comes from
  the same task pool. Of the 800 saved run records, 119 have
  `max_concurrent_lean=2`, 654 have 1, 27 have 0 — every one of the 119 with
  `threads=2`. So under the default TWO `lean` processes run at once: the
  peak in an `AllTests` build is NOT per-file-and-sequential. (No record with
  `-j 1` and two buildable targets was looked for; that `-j 1` gives one
  process is [P].)
* **How big the file is [M].** Charged memory 0.73–0.85 GB over the probe's
  steps 0–12 (which include the sponge's endpoint, not in this file); ≈ 2 min
  of generation for this file's seven commands (5.3 + 23.0 + 13.8 + 13.5 +
  12.8 + 33.1 + 19.9 s) + two reader runs (≈ 10 s each) + the audit
  (unmeasured).
* **Recommendation: TARGET-ONLY.** Reasons, in order: (1) with two
  concurrent `lean` processes its charge adds to a neighbour's (the last
  full-size records are 0.5–0.95 GB for small test groups; together ≈ 1.8 GB
  against `memory.high` 2.74 GB — it fits, but the margin is what the
  3 GiB cap is for); (2) the 0.8 GB is with a warm page cache; cold, the
  1.8 GB of mapped oleans are charged to the build as reclaimable file
  pages, and a build at `memory.high` is throttled, as step 13 was; (3)
  ≈ 3 min more on every rebuild of an imported generator, for one
  declaration; (4) no other test imports it. To move it into `AllTests`
  later: build it alone under `-m 3G -s 0 -j 1` with a cold cache and decide
  on `memory_peak_file` of the record (not on VmHWM).

## 3. What `#machine_design_svNR f 1` does, step by step [R]

`Tools/ShippingMachineDepthCommandR.lean` (the R heads) on
`Tools/ShippingMachineDepthCommand.lean`'s helpers. `f` = the sponge (P:
`d` = `keccak256SpongeHW.machineData`: 37 declared binders, 30 slots, 35
lets, 27 entries E, 1 group of 26 argument lets), `c` = `wKeccakF` (C: 27
declared binders = 26 hardware inputs I, 27 slots, 69 lets, 27 outputs, one
gate call).

| # | sub-step (lines) | generated constant | decided / reduced | scales with |
|---|---|---|---|---|
| a | `preClose` 658–676 | none here (`wKeccakF.machine_closes_at` exists: probe step 10) | `readMachine` f, c (twice), `keccakRcHW` (refused, caught): ≈ 25 s [M: 5.4 + 10.2 s per read] | reader |
| b | `generateCoreNR` 183–185: first line `progress "f: composedNR 1"` | | | |
| c | `generateRunOfR c 0` → `generateCombNR c 0` 40–66 → `generateComposedR c (atW := true)` (`ShippingMachineComposeRCommand` 54–296) | `c.machine_composedRA` — in the probe's run it EXISTED already: `#machine_design_svHR c` (step 11) generates it (`generateShipsHR`, `ShippingMachineComposeRCommand` 311), so this sub-step returned at once there | when absent: the child's composed theorem from the `RA` head; progress lines `c: composedR …`, `…machine_composedRA: checking` | C (child's data); its cost is inside the 33 s of probe step 11 [M] |
| d | `generateCombNR` 49–65 | `c.machine_composedNRH0` | 2 `decide`s on `c`'s shape (`instFields = []`, `insts ≠ []`) | constant |
| e | `generateRunOfR` 165–180 (`seqChildRunN_of_composedC`, `ShippingMachineDepthRunR` 116–146) | `c.seq_child_runN_ofR0` | 10 `decide`s on `c`'s data, among them `∀ o ∈ outs, outNameOk o.name` over 27 output names and the binder-kind lists (124 binders); `extTactic` on `c.machineExt` (1 call entry: one `split`) | C: outputs, binders |
| f | 212–273 | — | the families `bsC`, `outsC`, `S`, `PC` as `if n = c then … else …` over the callee names (1 callee) | callees |
| g | 283–336 | — | `closesAtNames c` (a reader run of `c`, the binders of `c.machine_closes_at`); the child's premise type | constant |
| h | 346–352: `machine_linkedT_callsRN` + 1 + 7 `mkDecideProof` | — | `hfe`, `hkD`, `hI`, `hIlen`, `hSL`, `hSlen`, `hLlen`, `hNIn` on `d` (129 binder kinds; no name comparison). `mkDecideProof` does NOT evaluate: the kernel pays at (l) | P binders |
| **i** | **354–476: the per-call loop, one tactic proof per ENTRY** | — | see below | **E × I, and more** |
| j | 499–552: `hrunN`, one proof per entry | — | per entry: `machineRunNC_of_real … (by decide)` (`insts ≠ []`) and `closesAtProof` (unification of `c.machine_closes_at`'s premises with the boundary's parts) | E |
| k | 477–494, 538–552: the two chains `forall_getElem?_cons` | — | 27 links each | E |
| l | 560–561: `progress "…machine_composedNR1: checking"`, `addTheorem` | `f.machine_composedNR1` | the KERNEL checks everything of (h)–(k) | all of the above |
| m | `generateShipsNR` 566–630 | `f.machine_ships_hierNR1` | `machine_ships_hierC` with 12 inferred arguments; 1 `decide` (the output-width premise, 5 outputs) | statement size |
| n | `generateDesignNR` 634–637 → `compose` (`ShippingShipsDesignSVCommand` 48–73) | `f.machine_design_svNR1` | `ships_design_svN_all` with 9 inferred arguments; `collectAxioms` | statement size |

Is the child's `machineData` embedded in the parent's statements? Only BY
NAME (`c.machineData` as a constant in `bsC`, `outsC`, `PC`, the premise
types); it is unfolded where something is computed from it: `bsIn` /
`portIdx` in (i), the decides of (e). `declsOf` and the name-separation
decide are NOT in this command (they are in `#machine_no_ports_kids`'
`oneOutKidTheorem`, `Tools/ShippingNoPortsKidsCommand.lean` 182–189: step 15
of the Keccak probe, never reached). `kidsChild_of_real` is not used by this
command either (`machineRunNC_of_real` per entry is, in (j)).

### (i) — the per-call loop

For EACH of the 27 entries `k` the generator elaborates the tactic of
439–470 from scratch, then `Meta.check`s the proof (475); the kernel checks
it a third time at (l). Per entry:

1. `A`, `B` (401–409): the child's input families as a nest of 1
   `extendBools` + 25 `extendBits` carrying the call's 26 argument Signals
   (the SAME 26 terms for every entry: one group).
2. `refine ⟨rfl, args, rfl, ?b, ?l, ?r, k', _, _, rfl, rfl, ?f, fun τ => rfl⟩`.
3. `case b`: the child's run theorem at the instance; `decide` of the port
   count against `c`'s data.
4. `case l`: `args_facts (by decide) (by simp [letObsB, …])` — 26 argument
   lets `< 35`.
5. `case r`: `InRange`, 26 conses.
6. `case f`, Bool family: `funext; simp only [extendBools]; repeat' split`,
   1 leaf closed by `decB_valsOf rfl (by decide) rfl`.
7. `case f`, bit-vector family: `funext p n; simp only [extendBits]
   (zetaDelta)` puts **25 nested `dite`s** with the 25 argument Signals into
   the goal; `repeat' split` splits them one by one — each `split` re-runs
   `simp` on the remaining goal (25, 24, …, 1 arguments: ≈ 25²/2 = 312
   argument traversals per entry) — leaving 26 leaves.
8. each of the 25 positive leaves: `bitsOf_at (decV_valsOf rfl (by decide)
   rfl)`. The last `rfl` is `lsrc[args[q]]? = some (fun τ => (a_q.val
   τ).toNat)`: `lsrc` is `letObsB d …` (`Tools/ShippingMachineSeqLinked.lean`
   203–226 [R]) — `d.ls.map fun l => … eval (typedVal …) l.2` — so the
   unifier EVALUATES the parent's REFLECTED let `args[q]` through `typedVal`
   (`Tools/ShippingMachineDenote.lean` 459–463: `letVal` over ALL 35 lets on
   `slotVal` over 30 slots: every leaf lookup peels up to 65 `set` layers)
   and compares it with the call's SOURCE argument (`Signal.mux start m_q
   (s_q ^^^ Signal.mux isOne m_{17+q} m_q)`, unfolded to its `.val`). The
   `(by decide)` evaluates `portIdx` on `c.machineData.bsIn`.
9. the final `.trans rfl`: the child's `machineSource` at field `k'` on the
   families `A`, `B` against the parent's extension at position `37 + k` —
   `machineExt` is a nest of 26 `extendBits`: reaching entry `k` peels
   `26 − k` layers; then the two `wKeccakF …` applications are compared
   argument by argument, each argument on the `B` side behind up to 25
   `extendBits` layers (≈ 25²/2 layer reductions per entry).

Counts: the argument facts of 6–8 are proved **27 × 26 = 702** times (the
built `mid2`: 2 entries × 1 argument = 2; factor 351), although they depend
only on the (callee, argument lets) GROUP — 1 group here — and not on the
entry: only `k'`, step 2's `rfl`s and step 9 depend on `k`. The `dite`
splitting adds a factor of the remaining depth (≈ 27 × 312 ≈ 8 400 argument
traversals in `simp`), step 8 a factor (lets + slots) = 65 per leaf lookup
(702 × ≈ 5 leaves × 65 ≈ 230 000 layer reductions per pass), and everything
is done three times (tactic, `Meta.check`, kernel). The whole loop runs in
ONE `MetaM` action: its metavariable context and caches are released only
when the command ends — a steadily growing memory is what this predicts.

### Most likely place of the blow-up [P], and the evidence

**The per-call loop (i), i.e. between the generator's lines `f: composedNR
1` and `…machine_composedNR1: checking`** — inside it, by reading, first
candidate the bit-vector family of `case f` (7 + 8), second the final `rfl`
(9). Evidence:

* by reading: (i) is the only sub-step whose work is a PRODUCT of the
  parent's entries and the child's inputs, with further factors; every
  other sub-step is linear in one declaration's data and has a built
  analogue of the same order that took ≤ 50 s on these declarations (the
  probe's steps 6–12);
* [M] the memory curve of step 13: no plateau, ≈ 2.6 MB/s from about 100 s
  after `START 13` until the throttle — a long run of retained elaboration,
  not one kernel reduction (a `decide` falling into unary arithmetic grows
  differently: in the kernel, with nothing retained by the elaborator; this
  cannot be told apart from (l) by the curve alone, hence the probe);
* what the run does NOT show: which piece; whether the loop ended and the
  kernel (l) was running. Not decidable by reading.

### How to confirm it cheaply: `Tests/Compiler/KeccakSpongeStepProbe.lean`

Which sub-steps are individually callable [R]: `closingCandidates`,
`generateComposedR`, `generateCombNR`, `generateRunOfR`, `generateCoreNR`,
`generateShipsNR`, `generateDesignNR` are public `def`s — the probe calls
each as its own step (8–11, 14–16) under the options the command sets. The
per-call loop and `hrunN` are NOT callable alone: they are the body of
`generateCoreNR`. For the loop the probe carries a COPY of the body for
chosen entries (steps 12: k = 0; 13: k = 1 and k = 26), cut into timed
pieces — `refine`, `b`, `l`, `r`, `f.refine`, `f.hb`, `f.hv.simp`,
`f.hv.split`, `f.hv.close` (per leaf), `f.fin`, `instantiate`, `Meta.check`
— and, before them, the 8 decided conditions of (h), each kernel-checked
alone (as a theorem that is removed again). It also logs the tree sizes of
the extension, the 27 call arguments and the entry's goal. Nothing of 12–13
is kept.

Run (the variable SET, an absolute path, a fresh file):

    SPARKLE_MACHINE_PROGRESS=$HOME/sparkle-work/keccak-sponge-step.log \
      ~/sparkle-work/bin/cgrun.sh -n sponge-step -m 3G -s 0 -t 2400 -- \
      lake build Tests.Compiler.KeccakSpongeStepProbe

Budget [P]: steps 0–7 ≈ 2.5 min (the probe's 5–10 [M] + two reads), 8–11
≈ 1–2 min (step 9 generates `wKeccakF.machine_composedRA` itself: this
probe does not run `#machine_design_svHR`), then 12. 2400 s is enough to see step 12 end or not; the file's
last line names the step and the piece. Reading the result:

| the file ends in … | meaning | next unit |
|---|---|---|
| step 9, 10 or 11 | not the loop: the child's `RA` composed theorem / its depth-0 run theorem on a 27-output wrapper | the generator's line before it; a unit on `wKeccakF` alone |
| step 12, a `parent decide j` line | a decided condition on the parent's data is expensive in the kernel | that condition as a per-declaration lemma |
| step 12, piece `f.hv.split` or `f.hv.close` | the argument facts (7 / 8) | the sharing below; for 8, a lemma giving a `let`'s observation without evaluating `typedVal` |
| step 12, piece `f.fin` | the final `rfl` (9) | state the entry's output as `machineExt` at a position by a lemma (`extendBits` at its own position) instead of by reduction |
| step 12 ends: T₀ ms, ΔRSS₀ | the loop costs ≈ 27 × T₀ and retains ≈ 27 × ΔRSS₀ before the kernel starts; compare with 989 s / 2 GB | if 27 × T₀ fits a limit, raise the limit for step 14 only; else the sharing |
| step 13 ≪ step 12 | caches carry over between entries | the loop is cheaper than 27 × T₀ |
| step 14 after `…: checking` | the kernel check (l) | split the theorem: one lemma per entry, so the kernel's work is released per entry |
| steps 15 / 16 | `machine_ships_hierC` / `compose` on the sponge's statement | read which unification |

If only the smallest instrumentation is wanted instead of the probe: four
`progress` lines in `generateCoreNR` (a `Tools/` edit, the integrator's) —
`call {k}: tactic` before 418, `call {k}: check` before 475, `hrunN {k}`
at 503, and one after 496 (`hcalls checked`). With the variable set, the
existing two lines already split the command in three (before the loop /
loop + `hrunN` / kernel).

The COST unit this points to [P] (a generator change, not written here;
`Tools/` is the integrator's and the statement proved does not change):
prove `decoded_eq`'s two family equations and `InRange` / `args_facts` ONCE
per (callee, argument lets) group and reuse them in the group's entries —
702 argument facts become 26, the per-entry part keeps `k'` and one `rfl`.

## 4. The sponge: what a successful run of the BUILT generators would give

`mid2`'s class (`NoPortsKidsMid2Test`, BUILT): `#machine_design_svNR f 1`,
`#machine_closes_deep f`, `#machine_no_ports_kids f 1`,
`#machine_boundary_close`. With `f` = `keccak256SpongeHW`, `c` = `wKeccakF`,
`g` = `keccakRcHW`:

| endpoint | premise | state |
|---|---|---|
| `f.machine_design_svNR1` (the base) | asks `shipsHierCheck`, `kidsMaskedN`, `designCheck … 1`, `outsCheck … 1`, `MachineClosesAt f`, and the boundary `ChildBnd ∧ MachineDefines c ∧ (names) ∧ ∀ contexts …` | NOT GENERATED: the probe's step 13 did not return [M] |
| `f.machine_design_noPortsNR1` | `shipsHierCheck (childMap D.modules) b` | not reached — would be absent [P] |
| | `kidsMaskedN D.modules b.body` | not reached — would be absent [P] |
| | `designCheck (childMap D.modules) 1 (checkedOptimize b)` | not reached — would be absent [P] |
| | `outsCheck (childMap D.modules) 1 (checkedOptimize b)` | not reached — would be absent [P] |
| `f.machine_design_noPortsNR1_closed` | `MachineClosesAt f` | not reached — would be absent by `f.closes_deep` [P] |
| `f.machine_design_noPortsNR1_closedB` (+ `_gap`) | the boundary's `MachineDefines c`, `True`, ∀-contexts conjunct | not reached — only `ChildBnd` would stay under the existentials [P] |
| | `hr`, `MachineDefines f`, `MachineDefines c`, `EntryDefines g`, `ChildBnd` | run boundary: they would stay premises |

What stands between the present state and that:

1. **Cost [M]: the base endpoint is not generated.** §3. This is the only
   thing KNOWN to stand in the way.
2. **Shape, by reading the scope test** (`scopeK`,
   `Tools/ShippingNoPortsKidsCommand.lean` 75–127 [R]): no refusal line
   applies — `f` has an endpoint, calls, registers, `instFields ≠ []`; its
   one callee `c` has an endpoint, registers, calls under the one-output
   closing of ONE callee `g` with `g.gate_peel`; `c.oneout_*`,
   `c.machine_portsRawH` are what `#machine_oneout c` leaves (it returned
   GENERATED in the probe [M]); `c.closes_deep` is what `#machine_closes_deep
   f` leaves (never run on these: the probe's step 14 was not reached);
   depth 1. So by reading it is cost only — with these UNTESTED points, none
   of which is a known obstacle:
   * 27 entries of ONE instance (built: 2 entries of one instance, `mid2`'s
     `k.n`, `k.hit`); the unread field `round` is an ordinary entry (§0.1);
   * a WRAPPER as the sequential child (`c`'s value is an application; the
     depth-0 run theorem `c.seq_child_runN_ofR0` on it: the step probe's
     step 11) and as the `OneOutKid`;
   * domain polymorphism of the parent: `mid2` is the built polymorphic
     entry of this class; here the child's source is indexed by the domain
     too (`srcAt` 243–250 handles both);
   * the decided data conditions of `#machine_no_ports_kids` at this size:
     `c.machine_oneOutKid`'s `self` clause is a name-separation `decide`
     over `declsOf c.machineData` (line 189: the CHILD's module size, 124
     binders — Name comparisons in the kernel), `f.machine_kidsK1`'s `hall`
     over 27 entries (314–315), and the 20-odd `decide`s of the four run
     theorems (382–466) on `d`.
3. Not a shape question: a multi-output gate child (none), a memory, a
   `Signal.loop`, several callees.

## 5. Risks of this round's files

* Nothing is built. `KeccakSpongeStepProbe`'s `callPieces` is a hand copy of
  ≈ 150 generator lines with the tactic cut at its `case`s; a slip there is
  a failure of the probe file (step 12 logs `FAILED — message`, the other
  steps still run), not a Keccak result. The cut relies on the goals' tags
  after `refine` being `b`, `l`, `r`, `f` (and `hb`, `hv`, `fin`): the tags
  are logged before they are used.
* The pieces' times are those of the copy, not of the generator's single
  tactic block: elaboration order inside `case f` differs slightly
  (`refine … ?hb ?hv … ?fin` instead of `exact … (by …) (by …) … rfl`).
* `kernelProbe` adds a theorem and puts the environment back; under
  `Elab.async false` (set by `deep`) that is synchronous [P].
* Step 14 of the step probe is the step that did not end before: with
  `-t 2400` the run is expected to END IN A TIMEOUT there unless 12–13 show
  it to be affordable — the progress file is the result.
* `OneOutWKeccakFTest`: the audit was built on 8-bit declarations; its cost
  on `wKeccakF` is unknown.

## Build record: `wKeccakF` (integrator, 2026-10-13)

`Tests.Compiler.OneOutWKeccakFTest` built at the first attempt on poc cfbab0db + this round's files (worker
files unchanged). TARGET-ONLY, not in AllTests (heavy; never co-import with `KeccakProbeTest` /
`KeccakSpongeStepProbe`). Established for `wKeccakF` (the hardware-module wrapper of `keccakF1600HW`:
27 registers = 1606 bits, a 27-field result, one one-output call of the gate child `keccakRcHW`): against
`wKeccakF.machine_design_svHR` the four check premises `shipsHierHCheck`, `kidsComb`, `designCheck`,
`outsCheck` are absent from `wKeccakF.machine_design_svH_full`; closed form "other" NONE, goal gap none NOT
ALLOWED; standard axioms. First IP-level (non-test) declaration with a check-free, gap-free endpoint.
Because the test is target-only, AllTests does not re-check it: rebuild this target after generator changes.

```
20261013-101039-a25-wkeccak: lake build Tests.Compiler.OneOutWKeccakFTest 
result=success
exit=0
memory_peak_file=1349103616
Build completed successfully (568 jobs).
n:189:0: ONEOUT FAMILY Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF: Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.machine_design_svH_full (13 lines; other: the closing premise only) and Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.machine_design_svH_full_closed (13 lines; other: NONE) — none of the four check premises of Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.machine_design_svHR (shipsHierHCheck, kidsComb, designCheck, outsCheck), no residual; goal gap Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.machine_design_svH_full_closed_gap: 4 lines, none NOT ALLOWED. SCOPE of this statement: (1) data conditions decided per declaration by the kernel for Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF (Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.oneout_callsOk, _slotLen, _domB, _insts, _instFields, _outTy, _nomem, _slots, _outChars, _outScalar, _callArgs at the nume
```
