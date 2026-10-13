# A-depth-grouped — the depth generator with the per-call facts proved once per group (round par/a-27)

STATE: **WRITTEN, NOT BUILT, NOT RUN.** [R] read in the source at the place
given; [M] measured by the integrator's run `20261013-111028-sponge-step4`
(its progress file `~/sparkle-work/keccak-sponge-step2.log`, read here in
full, not re-run); [I] inferred from [R] + [M], not observed; [P] prediction.
Base `b1d63c39`, branch `par/a-27`. Nothing existing is changed.

| new file | what |
|---|---|
| `Tools/ShippingMachineDepthCommandRG.lean` | `generateCoreNRG(S)`, `generateShipsNRG`, `generateDesignNRG`, `#machine_design_svNRG f n [as_old]`, two lemmas |
| `Tests/Compiler/DepthGroupedFamilyTest.lean` | 17 built endpoints: `NRG` statements `isDefEq` the built `NR` ones, standard axioms, groups vs entries |
| `Tests/Compiler/KeccakSpongeGroupedProbe.lean` | log-only: the sponge by `#machine_design_svNRG … 1 as_old`, then the downstream commands |
| this note | |

lakefile (the integrator's; `Tests.*` needs none, it is under `lean_lib «Tests»`):

    lean_lib «Tools.ShippingMachineDepthCommandRG» where
      roots := #[`Tools.ShippingMachineDepthCommandRG]

## 1. What piece `b` proves, and the grouping key

[R] `Tools/ShippingMachineCallsLinkedTNR.lean` 21–39: an entry's goal is
`MemFacts … ∨ SeqFactsRN (childMap dsn.modules) n d.shape dsn m.body (lsrc i bools bits) d.ls.length (d.bsIn.drop kD) kD (extB i bools bits) (ext i bools bits) bsC outsC (S i) PC k c`, and

    SeqFactsRN … k c :=
      memChild? c = none ∧ ∃ args, (shape.insts.map (·.2.1))[k]? = some args ∧
      (b) (∀ mc, PC c mc → SeqChildRunN children dsn n mc (bsC c) (outsC c) (S c) ∧ (argPorts mc).length = args.length) ∧
      (l) (∀ q (hq : q < args.length), args[q] < nL ∧ ∃ g, lsrc[args[q]]? = some g) ∧
      (r) (∀ τ, InRange (valsOf lsrc args τ) ((bsC c).filter (·.2 != .domain))) ∧
      ∃ k' o f, (outsC c)[k']? = some o ∧ o.name = shape.instFields.getD k "" ∧
        (S c (valsOf lsrc args))[k']? = some f ∧
        ∀ τ, posEnc (extB · τ) (ext · · τ) (kD + k) … = f τ

* **`b` does not depend on the entry's field at all** [R]: `k` and `k'` do
  not occur in it. It mentions the callee `c` (through `PC c`, `bsC c`,
  `outsC c`, `S i c`), the family index `i`, and of the argument list only
  its LENGTH. The tactic (`generateCoreNR` 428–438 [R]) instantiates the
  child's run theorem `c.seq_child_runN` (a child without calls) or
  `c.seq_child_runN_ofR{n-1}` (a child with calls: on the sponge
  `wKeccakF.seq_child_runN_ofR0`) at the child's index and the hypothesis
  `PC c mc`, and decides `argPorts`' length after a rewrite with the
  theorem's sixth component. So no `∀ field` form is needed: `b` is one
  proposition per (callee, argument list).
* `l`, `r`: the argument list and the callee only [R].
* The last equation is the only part that reads `k` and `k'`. Its proof
  (454–470 [R]) is `congrArg (·[k']?) (decoded_eq src hb hv) |>.trans rfl`
  with `hb : decoded Bool family = A`, `hv : decoded bit-vector family = B`,
  where `A`, `B` (401–409 [R]) are built from the callee's declared binders
  and the CALL's argument Signals. `hb`, `hv` do not read `k`, `k'`.

**Grouping key**: (callee, argument lets, `A`, `B`) — `A` and `B` compared
as terms (`Expr ==`). The reader's (callee, argument lets) is the expected
key; the two families are in the key so that two calls with equal lets but
different argument terms can never share a fact (then they are two groups,
and each group's facts are proved on its own families: soundness does not
rest on the key, only the amount of sharing does).

**How an entry takes the group's proof** (`entryProof`): the five facts are
local hypotheses `gfB{g}, gfL{g}, gfR{g}, gfHb{g}, gfHv{g}`; the entry is

    right; unfold SeqFactsRN
    refine ⟨rfl, args, rfl, gfB, gfL, gfR, k', _, _, rfl, rfl, ?_, fun τ => rfl⟩
    exact (congrArg (fun l => l[k']?) (decoded_eq (bools' := famA) (bits' := famB) famS gfHb gfHv)).trans rfl

and the hypotheses are bound ONCE around the chain over the entries:
`hcalls = fun i bools bits k c hk => (fun gf… => chain k c hk) proofs…`.
(`hclC` at 534–536 is substituted into each entry by `.beta`; here the
redex is kept, so `Meta.check` and the kernel see a group proof once by
construction, not by a cache.) The statements of the facts are read off the
first entry's goal by the old skeleton (`?b ?l ?r`) and by `decoded_eq … ?hb
?hv` — the path the probe measured — not rebuilt by hand.

The statement of `machine_composedNRG{n}` is `inferType` of
`machine_linkedT_callsRN … hcalls chain` under the same binders: it does not
mention the proof `hcalls`. Same code, same head, same arguments ⇒ the same
statement as `machine_composedNR{n}` [R; to be confirmed by the family test].

**Repair after the first build (integrator's log, 3d31437a; the generator
file BUILT, the family test failed on every endpoint).** `proveGroup` read
`hb`/`hv`'s statements off `refine (congrArg … (decoded_eq … ?hb ?hv)).trans
?fin`. For `parent` (child `cnt`, whose source does not read its bit-vector
inputs) the goal does not determine `decoded_eq`'s implicit `bits`: the
`refine` failed ("don't know how to synthesize implicit argument `bits`"),
its goal `f` stayed, and the tag lookup then reported "no goal tagged hb"
(the lookup itself erases macro scopes and had found `b`, `l`, `r`, `f`
before; it was not the defect). In the old tactic the `rfl` INSIDE the `by`
block fixes that family. Now the two statements are built directly,
`baseA = A` and `baseB = B` on the generator's own decoded families, and in
the entry `decoded_eq`'s `bools`, `bits` are fixed by the types of the
hypotheses `gfHb`, `gfHv`. Both variants (split, absorb chain) prove these
same two statements and the entries' skeleton is one function
(`entryProof`), so the two passes of the test share it. The sentence above
"read off … by `decoded_eq … ?hb ?hv`" holds for `b`, `l`, `r` only.

**Second repair (integrator's log, a656010d: the 11 one-group endpoints
PASS, the 6 with two or more groups failed with "synthetic hole has already
been defined with an incompatible local context").** `proveGroup` runs the
old skeleton only to READ the statements of `b`, `l`, `r`; its named holes
`?b ?l ?r ?f` therefore stayed UNASSIGNED in the metavariable context (in
the old loop every entry closes them, so the name is free again). A named
hole is looked up by name in the whole context: the second group's skeleton
found the first group's four holes, declared under the first group's local
definitions `famA … famS`. Now the skeleton runs under
`withoutModifyingState` and only the three statements (checked free of
metavariables) leave it. No other named hole is left open anywhere: the
group facts are proved on fresh goals by tactics without named holes, the
entry uses `?_`, the absorb chain has none, `memTactic`'s holes are closed
by its own `all_goals rfl`. Memory entries are not in any group (`ents`
holds `none` for them).

**Round par/a-28: the sponge run of 930d7012 stood after "l (args_facts):
proved".** [R] The only operation between that line and the next one was
`check pr` in `groupFact` (then line 208): `Meta.check` of `l`'s proof,
`args_facts (by decide) (by simp [letObsB, letObsLoop, letObsComb])`. The
kernel-alone checks ran only after all five facts (then 387–391), so
`SPARKLE_DEPTH_GROUP_KERNEL` played no part; `r`'s START line is written
before any of its work. The old generator does not avoid this check: it
`Meta.check`s every entry's whole proof (475), `l` included, and all of
`hcalls` again (495) — so the old loop, too, must have stood there at entry
0, [I]: that, not 27 × 108 s, may be what the earlier 38 minutes were.
Changed (logging and checks only, no proof content): `Meta.check` of group
facts, entries and the chain runs only with `SPARKLE_DEPTH_GROUP_CHECK` set
(`metaCheckG`; otherwise a SKIPPED line) — it only localises an ill-formed
proof earlier, the kernel checks the theorem, and the sanity test (no
`sorryAx`, no metavariable) stays; every operation has a START line before
it; the kernel-alone checks are collected (`kernelLater`) and run LAST,
after the theorem is added, `b` after the other facts (`kernelPending`).
Open [P]: the kernel must still check `l`'s proof inside the theorem; if the
`: checking` line is the last one, the next step is a proof of `l`'s length
premise that does not go through `simp` over the let observations.

## 2. Two findings of the reading (they change what the sponge's numbers mean)

**(i) The old loop does not stop at a failing entry** [R]. `case b => …`,
`case l`, `case r`, `case f` are `closeUsingOrAdmit` (Lean 4.32.1
`Elab/Tactic/BuiltinTactic.lean` 584, `Basic.lean` 345–357): with error
recovery on — `Tactic.run`'s default, which `proveByTacticT` uses — a failing
case is LOGGED (message log, shown when the command ends) and its goal
ADMITTED, runtime exceptions included (`tryCatchRuntimeEx`). The proof with
`sorryAx` passes `check proofK`; the loop goes on; the theorem is refused
only at the very end (`addTheorem`'s axiom check). On built declarations
nothing is wrong (no error is logged, the axiom check passes). On the sponge
it means: **the 38-minute run did not have to be 27 successful entries** — it
would look the same if every entry's `f` failed after ≈ 108 s.

**(ii) "The slip" of `f.hv.leaf 0` in the probe: I found no textual slip**
[R]. The probe's leaf tactic and its `funext`/`simp`/`repeat' split` texts
are the generator's 464–470 character for character. What the log shows
[M]: `f.hv.split left 1 leaves` after 2107 ms, and the failing goal is
`bitsOf … p✝ n✝ = if h : p✝ …` — the `simp only [extendBits]` DID unfold the
family, and `repeat' split` did NOT split the outermost `if`. Then the
leaf's first alternative cannot apply (`rename_i hp` renames `n✝`) and `rfl`
fails: the logged message. The structural differences of the copy
(separate `Tactic.run` calls, `refine … ?fin` for `.trans rfl`) do not touch
`split`. So, [I]: **the generator's own `hv` tactic fails on the sponge in
the same way**, and by (i) the generator logged it and went on — which is
why the full run neither stopped at entry 0 (≈ 2 min in) nor finished.
Probable cause [I, not confirmed]: `split` simplifies the WHOLE target with
`simp` (`Meta/Tactic/SplitIf.lean` 284–294, 316–324) under the default
`maxSteps` = 100 000; the bit-vector family is 1 994 507 tree nodes [M],
the Bool family, where `split` worked (`f.hb` OK), 205 205 [M]. Confirm with
`set_option trace.split.failure true` / the message of a bare `split` on
that goal. Whatever the cause, [M] is that the tactic leaves the goal
unsplit.

Consequences taken here: no `case` in the new generator (a failure is an
error at once; a proof containing `sorryAx` is refused at once), and a
second proof of the family facts that does not use `split`:

    extendBools_absorb : X = bools → X pos = sig → X = extendBools bools pos sig
    extendBits_absorb  : X = bits → X pos w = sig → X = extendBits bits pos w sig

chained once per Bool / bit-vector input, the per-input fact being the old
leaf's `boolsOf_at (decB_valsOf rfl (by decide) rfl)` / `bitsOf_at
(decV_valsOf rfl (by decide) rfl)`. `familyFact` tries the old tactic first
and the chain where it fails (state restored in between); with `absorb :=
true` the chain alone. The family test runs BOTH on every declaration.

Also read [R]+[M]: the old loop calls `readMachine c` per ENTRY (387);
`readMachine wKeccakF` is 10.2 s [M] — 27 × 10 s on the sponge, on top of
the 108 s. Here it is read once per callee.

## 3. What is restated, what is imported

`generateCoreNR` is one 380-line function; its set-up, the loop, `hrunN` and
the chains are inline. Restated UNCHANGED (assembled from the old file's
line ranges by a script, not retyped): 186–353 (168 lines), 355–369 (15),
477–490 (14, re-indented), 496–559 (64); `generateShipsNR` 570–627 (58) with
the composed theorem's and the result's names as parameters. Restated with a
change: the entry's data 379–410 (callee read cached, the bases of the
families kept). New: `proveGroup`, `entryProof`, `groupFact`, `familyFact`,
`kernelAlone`, `aliasOf`, the two lemmas, the two-phase loop. Called by
import: `readMachine`, `endpointParts`, `generateSeqChildN`,
`generateRunOfR` (→ `generateCombNR`, `bndOfComposed`, and the OLD
`generateCoreNR` for children with multi-output calls unless `as_old`),
`closesAtNames`, `closesAtProof`, `nameCases`, `sigAtPos`, `findCall`,
`rangeSyntax`, `memTactic`, `proveByTacticT`, `conj`, `projs`, `addTheorem`,
`compose`, `preClose`, `generateDesignNR` (in `as_old`).

Not grouped: `hrunN` (499–537): 0.1 s per entry [M].

## 4. `as_old`: what the downstream commands need

[R] `#machine_no_ports_kids` (`ShippingNoPortsKidsCommand` 509–516, 645),
`ShippingNoPortsDeepCommand` 476, `ShippingShipsFreeCommand` 264,
`ShippingShipsFreeMaskedCommand` 109, `ShippingNoKidsCommand` 139,
`ShippingShipsNoOutsCommand` 147, `#machine_closes_at` (307),
`#machine_final_goal` (174) take `f.machine_ships_hierNR{n}` /
`f.machine_design_svNR{n}` BY NAME, and the ships theorem's VALUE must be
`machine_ships_hierC` applied to 25 arguments (`compose` reads it too). So a
`G`-named ships theorem cannot serve them, and a mere alias under the old
name cannot either. `#machine_design_svNRG f n as_old`:

1. `f.machine_composedNR{n}` := `f.machine_composedNRG{n}` (another name;
   nothing reads the composed theorem's value [R: grep]) — when absent;
2. the OLD `generateDesignNR f n`, which finds 1. and builds
   `machine_ships_hierNR{n}`, `machine_design_svNR{n}` in the old form;
3. `machine_ships_hierNRG{n}`, `machine_design_svNRG{n}` := those (other
   names).

Children with multi-output calls are generated by the grouped loop first,
under both names, so `generateRunOfR` finds them. Safe: an added name
carries the statement of the theorem it names, by construction; if the old
name exists it is left alone. `#machine_closes_deep f` and
`#machine_boundary_close thm` need no alias.

## 5. Expected cost on the sponge [P], and the next wall

One group (27 entries of one `wKeccakF` instance [M]).

| part | once | basis |
|---|---|---|
| set-up (read, children's theorems, names) | ≈ 35 s | [M] |
| `b` tactic | ≈ 93 s | [M] |
| `b` `Meta.check` | unknown, ≤ the same order | never measured (the probe's entry never completed) |
| `l`, `r` | < 1 s | [M] |
| `hb` (split; 1 Bool input) | ≈ 12 s | [M] |
| `hv` split attempt, fails | ≈ 3 s | [M] |
| `hv` absorb chain: 25 per-input facts (`wKeccakF`: 1 Bool + 25 × 64-bit inputs [M]) | **unknown** | no bit-vector leaf has ever run on the sponge; the one Bool leaf is inside the 12 s of `hb` ⇒ if comparable, ≤ ≈ 5 min |
| 27 entries: data (≈ 2 s each [M: 12 s − 10 s read]), skeleton + last `rfl` (≈ 0.3 s [M]), `Meta.check` | ≈ 1–2 min | [M] for the pieces |
| `hrunN` | ≈ 3 s | [M] |
| kernel check of `machine_composedNRG1` | **unknown** | never reached by any run |
| `generateShipsNR`, `compose` (old code) | unknown | never reached |

So ≈ 5 min + the three unknowns, against ≥ 27 × 120 s ≈ 54 min of the old
loop before any check.

**The next wall is one of the unknowns, in this order of likelihood [P]:**
(1) the `hv` chain's 25 facts (each an `rfl` reducing the parent's let
observation at one let to the call's argument Signal — the reduction
A-keccak-2 first suspected; first time it runs); (2) the kernel's check of
the composed theorem (the `b` proof's conversion — 93 s in the elaborator —
plus 26 + 27 + 27 `rfl`s over an extension body of ≥ 5 000 000 tree nodes
[M]; the kernel's unfolding order is not the elaborator's, so the 93 s
predict nothing); (3) memory: 2.44 GB peak RSS in the pieces [M], 3 GiB cap.

**How the probe shows which**: the generator's own lines in the progress
file — per fact `START`, `proved (ms)`, `Meta.check (ms)`; per entry one
line; `…machine_composedNRG1: checking` and `: checked` bracket the kernel.
A run that stops shows its last `START`. With
`SPARKLE_DEPTH_GROUP_KERNEL=1` each group fact is ALSO checked by the kernel
alone (a throw-away theorem; `kernel alone START / OK (ms) / FAILED`) before
the entries: the kernel's time on `b` and on `hv` separately. What then
remains of the kernel's time is the 27 entries' own `rfl`s — not split
further here.

If (1): replace the per-input `rfl` by a lemma about one `let`'s observation
(A-keccak-2 "if the probe says otherwise", first item). If (2) on `b`: state
the child's run theorem for the parent's family (`S i c`, `bsC c`, `outsC c`
by `if_pos` rewriting instead of conversion).

## 6. The family test

`Tests/Compiler/DepthGroupedFamilyTest.lean`, target-only for now (it could
be in `AllTests`: every import is one of `AllTests`', and it adds only
`…NRG…` names). 17 endpoints: `parent`, `chained`, `two`, `mid`, `loopParent`,
`mid2`, `engineOnce`, `twinCalls`, `mesh2x2` at 1; `grand`, `mixDeep` at 2;
`grandH`, `mixD1` at 1 and 2; `topD2` at 2 and 3. Left out: nothing built in
`AllTests`' closure; the target-only `NoPortsSlotlessSeqFamilyTest`,
`RemainingProbeTest`, `KeccakProbeTest` repeat the same declarations. Per
endpoint: absorb-only variant (undone), default variant (kept); each:
three statements `isDefEq` the built ones (and whether they are the same
term), standard axioms; logged: entries, groups formed, groups predicted by
the reader, wall time. `mesh2x2`: the reader's data is asserted to be 8
entries in 4 groups (the prediction; remove the line if the reader says
otherwise).

NOT covered by it: the grouped recursion into children (`as_old` on a
parent whose child has multi-output calls and no theorem yet) — only the
sponge probe would take it, and the sponge's child `wKeccakF` has no
`instFields`, so it does not either. Unexercised code: 3 lines.

A mismatch of statements is not necessarily a defect of the loop: a depth
endpoint's statement depends on which closing theorems of the children
exist when it is generated (`closesAtNames`); the test's error names those
present.

## 7. Run

    lake build Tools.ShippingMachineDepthCommandRG
    lake build Tests.Compiler.DepthGroupedFamilyTest

    SPARKLE_MACHINE_PROGRESS=$HOME/sparkle-work/keccak-sponge-grouped.log \
      ~/sparkle-work/bin/cgrun.sh -n sponge-grouped -m 3G -s 0 -t 2400 -- \
      lake build Tests.Compiler.KeccakSpongeGroupedProbe

(family test first: the sponge probe is worth its 40 min only if the
generator elaborates.) Second sponge run, if the first stands in the kernel:
the same with `SPARKLE_DEPTH_GROUP_KERNEL=1`.

## 8. What may not elaborate (not built), most likely first

1. `extendBits_absorb` / `extendBools_absorb` (new tactic proofs, modelled on
   `extendBits_val` / `extendBools_val`): `subst` direction, `rw [dif_pos h]`
   then `obtain` on `h`, the `cast_eq` step. A failure here blocks the file.
2. The absorb chain's elaboration (`exact extend…_absorb (…) (bitsOf_at …)`
   nested): the expected type must reach the inner `rfl`s; the base `rfl`
   needs the elaborator's decoded family to be the generator's `bitsOf Dc
   bsIn vs` up to literals.
3. `entryProof`: `gfHb : X = A` used where `decoded_eq (bools' := famA)`
   expects `X = famA` (a local definition against its value), and the three
   hypotheses in the anonymous constructor (their types are read off the
   group's FIRST entry; they must be the later entries' expected types).
4. Reading the facts' statements off the goals (`goalTaggedG`, mvars left in
   `hb`/`hv`'s statements — a fallback states them on the generator's
   family).
5. do-notation layout of the two-phase loop (`try … catch` around a
   multi-line call, mutation inside `match` arms), the two `elab`s sharing a
   prefix (`… n` / `… n as_old`).
6. The family test's statement comparison (see §6, the closing theorems).

## 9. Decision text (for the user) — not done here

> Switch `#machine_design_svNR` to the grouped loop? Proposed, once
> `DepthGroupedFamilyTest` is green (17 statements `isDefEq`, standard
> axioms, both variants): replace lines 354–495 of
> `Tools/ShippingMachineDepthCommandR.lean` by the two-phase loop of
> `…RG.lean` (the helpers move with it; `…RG.lean` keeps only the `G`
> command as a thin wrapper or is removed), and the same for the twin
> `generateCoreN` (`ShippingMachineDepthCommand.lean` 234–343). No generated
> statement changes; every depth endpoint is regenerated; `AllTests` must
> be rebuilt and its time compared. Three behaviours change and each is a
> choice: (a) a failing entry is an ERROR at once instead of logged and
> admitted until the end [recommended: yes]; (b) the family facts fall back
> to the absorb chain where `split` fails [yes if the sponge needs it;
> otherwise leave it out of the switch]; (c) `check hcalls` is replaced by
> the checks of its parts [yes: the kernel checks the theorem anyway].
> Alternative: keep both generators and use the grouped one only for wide
> instances (≥ N entries per group).

## Build record (integrator, 2026-10-13)

Third build of par/a-27 (930d7012; the first two failed in the family test: the `bits` implicit not fixed
by the goal for a child that reads no bit-vector input; then named holes of one group left open for the
next). Worker files unchanged. `Tools.ShippingMachineDepthCommandRG` and
`Tests.Compiler.DepthGroupedFamilyTest` (target-only) built; AllTests green on the same tree.

No premise is removed: the grouped generator `#machine_design_svNRG` proves the per-call facts once per
(callee, argument lets) group and produces statements `isDefEq` the built ones for 17 of 17 endpoints
(`parent`, `chained`, `two`, `mid`, `loopParent`, `mid2`, `engineOnce`, `twinCalls`, `mesh2x2` at depth 1;
`grand`, `mixDeep` at 2; `grandH`, `mixD1` at 1 and 2; `topD2` at 2 and 3), standard axioms, both with the
split-free absorb chain and with the old split chain. `mesh2x2`: 8 call entries in 4 groups, as predicted.
The old command `#machine_design_svNR` is unchanged; switching it is a later decision. Not yet run: the
sponge probe.

```
20261013-115521-a27c-family: lake build Tools.ShippingMachineDepthCommandRG Tests.Compiler.DepthGroupedFamilyTest 
result=success
exit=0
memory_peak_file=929374208
Build completed successfully (588 jobs).
20261013-115806-a27c-alltests: lake build Tests.AllTests 
result=success
exit=0
memory_peak_file=132730880
Build completed successfully (1250 jobs).
.lean:206:0: DEPTH GROUPED: extendBools_absorb, extendBits_absorb — standard axioms
.lean:215:0: DEPTH GROUPED Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent at depth 1: reader — 2 call entries, 2 sequential, 1 predicted groups (distinct callee × argument lets). [family facts by the absorb chain: 986 ms; 2 call entries (2 sequential) in 1 groups; absorb chain: Bo
.lean:218:0: DEPTH GROUPED Sparkle.Tests.Compiler.ShippingMachineSeqTest.chained at depth 1: reader — 4 call entries, 4 sequential, 2 predicted groups (distinct callee × argument lets). [family facts by the absorb chain: 1804 ms; 4 call entries (4 sequential) in 2 groups; absorb chain: 
.lean:221:0: DEPTH GROUPED Sparkle.Tests.Compiler.ShippingChildBoundaryTest.two at depth 1: reader — 4 call entries, 4 sequential, 2 predicted groups (distinct callee × argument lets). [family facts by the absorb chain: 2028 ms; 4 call entries (4 sequential) in 2 groups; absorb chain: B
.lean:224:0: DEPTH GROUPED Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid at depth 1: reader — 2 call entries, 2 sequential, 1 predicted groups (distinct callee × argument lets). [family facts by the absorb chain: 964 ms; 2 call entries (2 sequential) in 1 groups; absorb chain: Bool 
.lean:227:0: DEPTH GROUPED Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand at depth 2: reader — 2 call entries, 2 sequential, 1 predicted groups (distinct callee × argument lets). [family facts by the absorb chain: 1294 ms; 2 call entries (2 sequential) in 1 groups; absorb chain: Bo
.lean:230:0: DEPTH GROUPED Sparkle.Tests.Compiler.ShippingMachineSeqLoopTest.loopParent at depth 1: reader — 1 call entries, 1 sequential, 1 predicted groups (distinct callee × argument lets). [family facts by the absorb chain: 745 ms; 1 call entries (1 sequential) in 1 groups; absorb c
.lean:233:0: DEPTH GROUPED Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH at depth 1: reader — 2 call entries, 2 sequential, 1 predicted groups (distinct callee × argument lets). [family facts by the absorb chain: 1345 ms; 2 call entries (2 sequential) in 1 groups; absorb chain
.lean:236:0: DEPTH GROUPED Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH at depth 2: reader — 2 call entries, 2 sequential, 1 predicted groups (distinct callee × argument lets). [family facts by the absorb chain: 1354 ms; 2 call entries (2 sequential) in 1 groups; absorb chain
.lean:239:0: DEPTH GROUPED Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2 at depth 1: reader — 2 call entries, 2 sequential, 1 predicted groups (distinct callee × argument lets). [family facts by the absorb chain: 1355 ms; 2 call entries (2 sequential) in 1 groups; absorb chain: Bool 
.lean:242:0: DEPTH GROUPED Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1 at depth 1: reader — 4 call entries, 4 sequential, 2 predicted groups (distinct callee × argument lets). [family facts by the absorb chain: 2380 ms; 4 call entries (4 sequential) in 2 groups; absorb chain: Bool
.lean:245:0: DEPTH GROUPED Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1 at depth 2: reader — 4 call entries, 4 sequential, 2 predicted groups (distinct callee × argument lets). [family facts by the absorb chain: 2385 ms; 4 call entries (4 sequential) in 2 groups; absorb chain: Bool
.lean:248:0: DEPTH GROUPED Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2 at depth 2: reader — 2 call entries, 2 sequential, 1 predicted groups (distinct callee × argument lets). [family facts by the absorb chain: 1375 ms; 2 call entries (2 sequential) in 1 groups; absorb chain: Bool
.lean:251:0: DEPTH GROUPED Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2 at depth 3: reader — 2 call entries, 2 sequential, 1 predicted groups (distinct callee × argument lets). [family facts by the absorb chain: 1382 ms; 2 call entries (2 sequential) in 1 groups; absorb chain: Bool
.lean:254:0: DEPTH GROUPED Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep at depth 2: reader — 6 call entries, 6 sequential, 3 predicted groups (distinct callee × argument lets). [family facts by the absorb chain: 3831 ms; 6 call entries (6 sequential) in 3 groups; absorb chai
.lean:257:0: DEPTH GROUPED Sparkle.Tests.Compiler.MultiInstance.engineOnce at depth 1: reader — 2 call entries, 2 sequential, 1 predicted groups (distinct callee × argument lets). [family facts by the absorb chain: 925 ms; 2 call entries (2 sequential) in 1 groups; absorb chain: Bool fa
.lean:260:0: DEPTH GROUPED Sparkle.Tests.Compiler.MultiInstance.twinCalls at depth 1: reader — 2 call entries, 2 sequential, 1 predicted groups (distinct callee × argument lets). [family facts by the absorb chain: 873 ms; 2 call entries (2 sequential) in 1 groups; absorb chain: Bool fam
.lean:263:0: DEPTH GROUPED Sparkle.Tests.Compiler.MultiInstance.mesh2x2 at depth 1: reader — 8 call entries, 8 sequential, 4 predicted groups (distinct callee × argument lets). [family facts by the absorb chain: 24637 ms; 8 call entries (8 sequential) in 4 groups; absorb chain: Bool fam
.lean:271:0: DEPTH GROUPED COUNTS Sparkle.Tests.Compiler.MultiInstance.mesh2x2: 8 call entries in 4 groups, as predicted
.lean:286:0: DEPTH GROUPED FAMILY: 17 of 17 endpoints generated by the grouped loop with statements isDefEq the built ones and standard axioms; FAILED (built theorems present, the grouped ones not generated — see the errors above): []; left out (built theorems absent here): []
```

## Run record: the grouped sponge probe (integrator, 2026-10-13) — log-only, claims nothing

`20261013-115814-sponge-grouped`: `SPARKLE_MACHINE_PROGRESS=… SPARKLE_DEPTH_GROUP_KERNEL=1 lake build
Tests.Compiler.KeccakSpongeGroupedProbe`, 3 GiB, swap 0, limit 2400 s: result=timeout,
memory_peak_file=3077693440, events: low 0 high 44950 max 0 oom 0 oom_kill 0 oom_group_kill 0  (throttled at memory.high, no OOM kill).

Reached: base steps OK; `#machine_design_svNRG keccak256SpongeHW 1 as_old` started; the grouped loop
opened ONE group for the 27 call entries; group fact `b`: proved in 92 700 ms, `Meta.check` 30 346 ms;
group fact `l` (args_facts): proved in 161 ms. After that line nothing more was written until the limit.
So the next wall is whatever follows "l … proved" in `proveGroup` with `SPARKLE_DEPTH_GROUP_KERNEL` set
(the check of `l`, a kernel-alone timing, or the start of `r`) — not yet read; the run does not say
which. Not reached: `r`, `hb`, `hv`, the 27 entries, the composed theorem's check.

```
209474955 Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.machine_composedRA: checking [VmRSS:	 2227340 kB]
209505401 Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW: grouped loop, 27 call entries [VmRSS:	 2245940 kB]
209516002 Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW: call 0 opens group 0 (Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF, lets[..]) [VmRSS:	 2277760 kB]
209516059 Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW: group 0 (Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF, lets[..]): b (the child's run theorem at the instance; argPorts' length): START [VmRSS:	 2264820 kB]
209608759 Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW: group 0 (Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF, lets[..]): b (the child's run theorem at the instance; argPorts' length): proved (92700 ms) [VmRSS:	 2400628 kB]
209639105 Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW: group 0 (Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF, lets[..]): b (the child's run theorem at the instance; argPorts' length): Meta.check (30346 ms) [VmRSS:	 2406020 k
209639106 Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW: group 0 (Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF, lets[..]): l (args_facts): START [VmRSS:	 2406020 kB]
209639267 Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW: group 0 (Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF, lets[..]): l (args_facts): proved (161 ms) [VmRSS:	 2394424 kB]
```

## Run record 2: the grouped sponge probe after the logging / optional-check change (integrator, 2026-10-13)

par/a-28 113eb615 (`Meta.check` of group facts, entries and the chain opt-in via `SPARKLE_DEPTH_GROUP_CHECK`;
START lines everywhere; kernel-alone timings last). `20261013-124054-a28-family`: the family test rebuilt — 17 of 17
endpoints `isDefEq` the built statements, standard axioms. `20261013-124156-sponge-grouped2` (3 GiB, swap 0, limit 2400 s, no
kernel option): result=success, memory_peak_file=1722933248, no throttling.

- Step 8, `#machine_design_svNRG keccak256SpongeHW 1 as_old`: **OK in 488.9 s.** One group for the 27 call
  entries; each entry's tactic 0.33–0.38 s from the group's facts; the chain built;
  `keccak256SpongeHW.machine_composedNRG1`: checking → checked (the KERNEL accepted the composed theorem);
  `machine_composedNR1`, `machine_ships_hierNR1`, `machine_design_svNR1` added under the old names.
  This is a probe: nothing is kept, and `…svNR1` still carries its four check premises — it is the BASE
  endpoint the check-free generators start from. What blocked every earlier run was `Meta.check` of the
  group fact `l` (and before the grouping, 27 instantiations of the child's run theorem).
- Step 9, `#machine_closes_deep keccak256SpongeHW`: FAILED after 42 s — "closes_deep was not generated:
  wKeccakF.iface_deep: the generated proof fails: [maximum recursion depth has been reached …
  `set_option maxRecDepth <num>` to increase limit]". The next wall; a recursion-depth limit, not a refusal.
- Steps 10–11 on `wKeccakF` (`#machine_design_svHR`, `#machine_oneout`): OK (19 s each).
- Steps 12–13 (`#machine_no_ports_kids`, `#machine_boundary_close` on the sponge): SKIPPED — they need
  `wKeccakF.closes_deep`.

```
SPG STEP START 8 keccak256SpongeHW #machine_design_svNRG 1 as_old [VmRSS:	 2197972 kB] [VmHWM:	 2291496 kB]
keccak256SpongeHW: grouped loop, 27 call entries [VmRSS:	 2232464 kB]
keccak256SpongeHW: call 0 opens group 0 (wKeccakF, lets[..]) [VmRSS:	 2249604 kB]
keccak256SpongeHW: group 0 (wKeccakF, lets[..]): b (the child's run theorem at the instance; argPorts' length): tactic START [VmRSS:	 2250104 kB]
keccak256SpongeHW: group 0 (wKeccakF, lets[..]): b (the child's run theorem at the instance; argPorts' length): tactic OK (92847 ms); sanity test (no sorry, no metavariable) START [VmRSS:	 2396148 kB]
keccak256SpongeHW: group 0 (wKeccakF, lets[..]): b (the child's run theorem at the instance; argPorts' length): sanity test OK (1 ms) [VmRSS:	 2396148 kB]
keccak256SpongeHW: group 0 (wKeccakF, lets[..]): b (the child's run theorem at the instance; argPorts' length): Meta.check SKIPPED (SPARKLE_DEPTH_GROUP_CHECK not set; the kernel checks the theorem) [VmRSS:	 2396148 kB]
keccak256SpongeHW: group 0 (wKeccakF, lets[..]): l (args_facts): tactic START [VmRSS:	 2396148 kB]
keccak256SpongeHW: group 0 (wKeccakF, lets[..]): l (args_facts): tactic OK (20 ms); sanity test (no sorry, no metavariable) START [VmRSS:	 2396152 kB]
keccak256SpongeHW: group 0 (wKeccakF, lets[..]): l (args_facts): sanity test OK (0 ms) [VmRSS:	 2396152 kB]
keccak256SpongeHW: group 0 (wKeccakF, lets[..]): l (args_facts): Meta.check SKIPPED (SPARKLE_DEPTH_GROUP_CHECK not set; the kernel checks the theorem) [VmRSS:	 2396152 kB]
keccak256SpongeHW: group 0 (wKeccakF, lets[..]): r (InRange): tactic START [VmRSS:	 2396152 kB]
keccak256SpongeHW: group 0 (wKeccakF, lets[..]): r (InRange): tactic OK (378 ms); sanity test (no sorry, no metavariable) START [VmRSS:	 2373260 kB]
keccak256SpongeHW: group 0 (wKeccakF, lets[..]): r (InRange): sanity test OK (0 ms) [VmRSS:	 2373296 kB]
keccak256SpongeHW: group 0 (wKeccakF, lets[..]): r (InRange): Meta.check SKIPPED (SPARKLE_DEPTH_GROUP_CHECK not set; the kernel checks the theorem) [VmRSS:	 2373296 kB]
keccak256SpongeHW: group 0 (wKeccakF, lets[..]): hb (the Bool family) [split]: tactic START [VmRSS:	 2373360 kB]
keccak256SpongeHW: group 0 (wKeccakF, lets[..]): hb (the Bool family) [split]: tactic OK (11810 ms); sanity test (no sorry, no metavariable) START [VmRSS:	 2325816 kB]
keccak256SpongeHW: group 0 (wKeccakF, lets[..]): hb (the Bool family) [split]: sanity test OK (1 ms) [VmRSS:	 2325820 kB]
keccak256SpongeHW: group 0 (wKeccakF, lets[..]): hb (the Bool family) [split]: Meta.check SKIPPED (SPARKLE_DEPTH_GROUP_CHECK not set; the kernel checks the theorem) [VmRSS:	 2325820 kB]
keccak256SpongeHW: group 0 (wKeccakF, lets[..]): hv (the bit-vector family) [split]: tactic START [VmRSS:	 2325820 kB]
keccak256SpongeHW: group 0 (wKeccakF, lets[..]): hv (the bit-vector family) [split]: tactic OK (3706 ms); sanity test (no sorry, no metavariable) START [VmRSS:	 2292912 kB]
keccak256SpongeHW: group 0 (wKeccakF, lets[..]): hv (the bit-vector family) [split]: NOT proved — keccak256SpongeHW: group 0 (wKeccakF, argument lets [7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27
keccak256SpongeHW: group 0 (wKeccakF, lets[..]): hv (the bit-vector family) [absorb chain]: tactic START [VmRSS:	 2292920 kB]
keccak256SpongeHW: group 0 (wKeccakF, lets[..]): hv (the bit-vector family) [absorb chain]: tactic OK (233778 ms); sanity test (no sorry, no metavariable) START [VmRSS:	 2564312 kB]
keccak256SpongeHW: group 0 (wKeccakF, lets[..]): hv (the bit-vector family) [absorb chain]: sanity test OK (1 ms) [VmRSS:	 2564312 kB]
keccak256SpongeHW: group 0 (wKeccakF, lets[..]): hv (the bit-vector family) [absorb chain]: Meta.check SKIPPED (SPARKLE_DEPTH_GROUP_CHECK not set; the kernel checks the theorem) [VmRSS:	 2564312 kB]
keccak256SpongeHW: grouped loop done [VmRSS:	 2374224 kB]
keccak256SpongeHW.machine_composedNRG1: checking [VmRSS:	 2343820 kB]
keccak256SpongeHW.machine_composedNRG1: checked [VmRSS:	 2056280 kB]
keccak256SpongeHW.machine_composedNR1: added as another name of keccak256SpongeHW.machine_composedNRG1 [VmRSS:	 2061960 kB]
keccak256SpongeHW.machine_ships_hierNRG1: added as another name of keccak256SpongeHW.machine_ships_hierNR1 [VmRSS:	 2062136 kB]
keccak256SpongeHW.machine_design_svNRG1: added as another name of keccak256SpongeHW.machine_design_svNR1 [VmRSS:	 2062132 kB]
keccak256SpongeHW.machine_design_svNRG1: done [VmRSS:	 2062132 kB]
SPG STEP 8 keccak256SpongeHW #machine_design_svNRG 1 as_old: OK (488904 ms) [VmRSS:	 2058036 kB] [VmHWM:	 2627852 kB]
SPG STEP START 9 keccak256SpongeHW #machine_closes_deep [VmRSS:	 2060084 kB] [VmHWM:	 2627852 kB]
SPG STEP 9 keccak256SpongeHW #machine_closes_deep: FAILED (42295 ms) — keccak256SpongeHW: closes_deep was not generated: wKeccakF.iface_deep: the generated proof fails: [maximum recursion depth has been reached
SPG STEP START 10 wKeccakF #machine_design_svHR [VmRSS:	 2143536 kB] [VmHWM:	 2627852 kB]
SPG STEP 10 wKeccakF #machine_design_svHR: OK (19196 ms) [VmRSS:	 2060376 kB] [VmHWM:	 2627852 kB]
SPG STEP START 11 wKeccakF #machine_oneout [VmRSS:	 2060376 kB] [VmHWM:	 2627852 kB]
SPG STEP 11 wKeccakF #machine_oneout: OK (19610 ms) [VmRSS:	 2055452 kB] [VmHWM:	 2627852 kB]
SPG STEP 12 keccak256SpongeHW #machine_no_ports_kids 1: SKIPPED — not in the environment: [wKeccakF.closes_deep] [VmRSS:	 2055768 kB] [VmHWM:	 2627852 kB]
SPG STEP 13 keccak256SpongeHW #machine_boundary_close: SKIPPED — not in the environment: [keccak256SpongeHW.machine_design_noPortsNR1_closed] [VmRSS:	 2056296 kB] [VmHWM:	 2627852 kB]
SPG STEP END: in the environment [keccakRcHW.gate_child, wKeccakF.machine_sound, wKeccakF.machine_closes_at, wKeccakF.machine_composedRA, wKeccakF.machine_composedNRH0, wKeccakF.seq_child_runN_ofR0, keccak256SpongeHW.machine_sound
```
