# B-memseqgen2: why `#machine_design_svR0 seqTwoMem` failed, and a declaration inside the built base scope (round par/b-25)

Status: **READ, NOT BUILT**. The diagnosis below is by reading the generator; no build confirmed it.
Branch `par/b-25`. New files: `Tests/Compiler/NoPortsMemSeqGenNew2Test.lean`, this note. Nothing edited.

## 1. The site

`Tools/ShippingMachineSeqCommand.lean` 127–137, `memTactic` — the tactic for ONE memory call's facts:

    refine ⟨$cbE, $(lit aw), $(lit dw), ?A, ?D, ?E, ?R, $(lit l0), …,
      rfl, rfl, ?h0, by decide, ?h1, by decide, ?h2, by decide, ?h3, by decide, rfl, ?hx⟩
    case hx => (intro j; rfl)
    all_goals rfl

It is called once per memory ENTRY (`Tools/ShippingMachineSeqCommandR.lean` 124–126 for `#machine_design_svR0`;
also `ShippingMachineSeqCommand.lean` 254, `ShippingMachineDepthCommand.lean` 279, `…DepthCommandR.lean` 822,
`…DepthCommandRG.lean` 783, `…DepthCommandROld.lean` 244), each time through `proveByTacticT` inside ONE
`MetaM` run, i.e. one metavariable context, with the same local context (the memory branch adds no local).

The synthetic holes `?A ?D ?E ?R ?h0 ?h1 ?h2 ?h3` carry NO call index. They are closed by `all_goals rfl`,
which leaves their user names in the metavariable context; only `?hx` is closed through `case`, which clears
the tag. On the SECOND memory entry `?A` … resolve to the first entry's (assigned) holes: `?A` is then the
first memory's write-address signal, of type `Signal D (BitVec aw₁)`, where `Signal D (BitVec aw₂)` is
expected, and the nested `⟨…⟩` of the existential can no longer be elaborated — the reported
"Invalid ⟨...⟩ notation: The expected type of this term could not be determined". (With equal widths the
reuse would give the wrong witnesses and fail at a `rfl` instead.)

Supporting reading: the memory-ONLY route's generator names the same holes per call
(`Tools/ShippingMachineMemCommand.lean` 34–35: `?A{k}`, `?D{k}`, …, `?hx{k}`), and it is built on `twoMems` /
`mixedMems`. The sequential branch of the same loop closes all its holes (`?b ?l ?r ?f`) through `case`, and is
built on four sequential entries (`chained`, `two`). The error is not wrapped in "call k:" — only the
sequential branch is (`ShippingMachineSeqCommandR.lean` 211) — which fits the memory branch.

It does not depend on the number or kinds of leaf callees: `two` (two different leaf callees) is built.

## 2. A limitation of the base generator: its built scope

Sequential route (`#machine_composedTS`, `#machine_composedTSR`, `#machine_design_svR0`, the depth commands):
any number of leaf callees and entries, **at most ONE memory entry** per declaration. Built: `seqMem` (one leaf
callee, one combinational memory), `two`, `chained`, `parent`. `seqTwoMem` (two memory entries) is outside.
Consequence for `#machine_no_ports_memseq`: its per-entry-widths support (two or more placeholders) cannot be
exercised until the base generator is changed; its code path for several placeholders stays unbuilt-on-data.

## 3. The minimal change (for the integrator; NOT made)

In `memTactic` only: give it the call index and name the holes per call, exactly as
`Tools.ShippingMachineMemCommand.callsTactic` does (`hole s := ?{s}{k}`; `case hx{k} => (intro j; rfl)`).
(Closing them through `case` instead is not available: `?A ?D ?E ?R` are assigned by unification, not goals.)
  Signature `memTactic (k : Nat) (cb : Bool) (aw dw : Nat) (args : List Nat)`; six call sites pass their `k`.
  No statement changes; every built endpoint with one memory elaborates the same term up to hole names.

After that change `Tests/Compiler/NoPortsMemSeqGenNewTest.lean` (par/b-21, db9d0b84) is the test for two
placeholders of different kinds and widths; nothing else in it needs the change.

## 4. The declaration inside the built scope: `seqAccSync`

`Tests/Compiler/NoPortsMemSeqGenNew2Test.lean`: `cnt en`, `acc rs`, ONE `Signal.memory wb wd en wb`
(synchronous, aw 3, dw 8). New for the memseq generator against `seqMem`: two different leaf callees (three
keys; three-way `Or.elim`; `leafNe0_1`; two reflections in the closing), a synchronous read, another address
width. Steps and audit as the earlier test (reader data logged first; no refusal block — those four were
logged by the integrator's build already).

| endpoint | premise | predicted state |
|---|---|---|
| `seqAccSync.machine_design_noPortsR0` | `shipsHierCheck`, `kidsMixed`, `designCheck 0`, `outsCheck 0` | WRITTEN, NOT BUILT — predicted absent, pending build |
| | `MachineClosesAt seqAccSync` | stays, the one NOT ALLOWED |
| `seqAccSync.machine_design_noPortsR0_closed` | `MachineClosesAt seqAccSync` | predicted absent; `MachineDefines cnt`, `MachineDefines acc` added (allowed); 0 NOT ALLOWED |
| `…_closed_gap` | gap hypotheses | predicted none |

Known from the built log of `seqTwoMem`: `#machine_endpoint` accepts a synchronous memory in a `circuit do`
next to `cnt` and `acc`; entries are one per callee OUTPUT (`acc` gives `s` and `odd`). Not known: `memTactic`
with `cb = false` in the sequential route (first use).

Integration: no new `Tools/` file (whether a test target needs a lakefile entry is the integrator's convention, not read); AllTests import possible after a
first target-only build — every name is under `…NoPortsMemSeqGenNew2Test.seqAccSync` plus three helpers in
`Tests.Compiler.NoPortsMemSeqGenNew2Test`; imports (`ShippingChildBoundaryTest`, `NoPortsTwoTest`) are in
AllTests already.

Risks, most likely first: (1) the sequential route's memory step for a synchronous read; (2) the generator's
three-key paths (table `if` chains, three-way `orElim`), first run on data; (3) the audit's `3` proposition
binders of the base / open endpoints, read off `seqMem` only.

## 5. The change, MADE (authorised; WRITTEN, NOT BUILT) — supersedes "NOT made" in §3 and "Nothing edited" in the header

Commit "memTactic: synthetic holes named per call index" on `par/b-25` (base c45f545c = the poc head, which
already contains the depth switch bf32874b / f3ee9c57 / 77b3ba4f: no rebase was needed).

Diff (6 files, 19 insertions, 11 deletions):

| file | lines | change |
|---|---|---|
| `Tools/ShippingMachineSeqCommand.lean` | 126–145 | `memTactic (k : Nat) (cb : Bool) (aw dw : Nat) (args : List Nat)`; `hole s := ?{s}{k}` built as `ShippingMachineMemCommand.lean` 34–35 builds it; holes `?A{k} ?D{k} ?E{k} ?R{k} ?h0_{k} ?h1_{k} ?h2_{k} ?h3_{k} ?hx{k}`; `case hx{k} => (intro j; rfl)`; doc comment |
| same | 262 | call site: `memTactic k cb aw dw argsK` |
| `Tools/ShippingMachineSeqCommandR.lean` | 126 | call site |
| `Tools/ShippingMachineDepthCommand.lean` | 279 | call site |
| `Tools/ShippingMachineDepthCommandR.lean` | 822 | call site (grouped loop) |
| `Tools/ShippingMachineDepthCommandRG.lean` | 783 | call site |
| `Tools/ShippingMachineDepthCommandROld.lean` | 244 | call site (old loop: old-vs-new stays like-for-like) |

At every site `k` is the loop variable of `for k in [0:calls.length]`, the index of the call entry (read at
each site on this head).

Why no name, statement or premise changes: `memTactic` only produces the tactic that proves ONE disjunct
`MemFacts … k c` of the calls' premise for a goal that is fixed before the tactic runs (`goalK`); the change
renames the user names of the metavariables that tactic creates. The proof term after `instantiateMVars` has
no metavariable; the witnesses (`cb, aw, dw`, the four signals found by `rfl`) are determined by the goal. For
a declaration with ONE memory entry the elaboration is the same up to those names. What changes is which
declarations the commands accept: a second memory entry no longer meets the first one's holes.

NOT covered by the change (as before): one command that runs the calls loop TWICE over the same declaration in
one `MetaM` run with the same local context would meet `?A{k}` again. No such use is known (each generator
runs the loop once per theorem); it is the situation the old names had for every pair of calls.

Also restored, unchanged from db9d0b84: `Tests/Compiler/NoPortsMemSeqGenNewTest.lean` (`seqTwoMem`: two leaf
callees, a combinational (4, 8) and a synchronous (3, 8) memory) — now the two-placeholder / per-entry-widths
test. It and `NoPortsMemSeqGenNew2Test` (`seqAccSync`) do not clash: declarations in
`Sparkle.Tests.Compiler.NoPortsMemSeqGenNewTest` / `…New2Test`, helpers in
`Tests.Compiler.NoPortsMemSeqGenNewTest` / `…New2Test`; `cnt.machine_leafKid`, `acc.machine_leafKid` and the
children's base data are imported, not created; the refusal block adds no name.

## 6. Acceptance list for the integrator

`Tools/ShippingMachineSeqCommand.lean` is imported by nearly every generator, so the edit RECOMPILES most of
the tree; "affected" below means: the generated proofs go through `memTactic`.

1. The six edited `Tools` files (syntax of the new `hole` / `case $(…):ident`).
2. Tests whose commands reach `memTactic` (a memory entry in the sequential or depth route) — by grep, only:
   `Tests.Compiler.ShippingChildBoundaryTest` (`#machine_design_svR0 seqMem`, `#machine_composedTS seqMem`:
   seqMem's defining test), then its dependants `NoPortsMemSeqMemTest`, `NoPortsMemSeqMemClosedTest`,
   `NoPortsMemSeqGenCompareTest` (statements must stay `isDefEq`: the compare test checks it).
   `ShippingMachineSeqLoopTest` runs `#machine_composedTS withMemory` (a memory-only parent: by reading
   `ShippingMachineSeqCommand.lean` ~400 it is sent to the memory-only route, not to `memTactic` — rebuild it
   anyway).
3. NOT through `memTactic` (they use `ShippingMachineMemCommand.callsTactic`, untouched): the memory-only
   family (`ShippingMachineMemLinkedTest`, `ShippingDesignSVMemTest`, `NoPortsMemOnly*`, `NoPortsMemGen*`).
   `DepthSwitchTypeTest`: no memory declaration is named in it (grep) — it recompiles (both loops' files are
   edited, like-for-like) but its generated terms do not pass through `memTactic`.
4. The two new tests, target-only: `NoPortsMemSeqGenNew2Test` (one memory: inside the old scope, tests the
   generator) THEN `NoPortsMemSeqGenNewTest` (two memories: tests this change and per-entry widths).
5. `Tests.AllTests`.
6. Target-only Keccak tests: no memory callee (`keccak256SpongeHW` / `wKeccakF` call `keccakRcHW` /
   `wKeccakF` only, by the commit records) — generated terms unaffected; they DO recompile, since they import
   the edited depth command files (the 454 s endpoint is rebuilt if its target is requested).

Risks, most likely first: (1) the diagnosis itself is by reading — if the failure has another cause,
`seqTwoMem` still fails at the same line and the change is merely harmless; (2) `case $(mkIdent …):ident`
on its own line inside the quoted tactic block (the memory-only generator has it with `;` separators);
(3) `seqTwoMem` beyond the base: the generator's four-key paths and `memNe0_1`, first run on data;
(4) the cost of the rebuild.

## Build record (integrator, 2026-10-13)

Verified tree `04743a3727d5fb9a40d1fcddb55543786d427f21` = poc d9d5c6b5 + par/b-25 (4a6421c6 the fix, 2dd0ed58 / 65ef1e4b the tests; worker files
unchanged) + two imports in `Tests/AllTests.lean`. cgrun 3 GiB, swap 0.
- `20261013-153248-b25-tests`: the six generator files, both new tests and AllTests — result=success, memory_peak_file=1325559808; Build completed successfully (1278 jobs).
- `20261013-154038-b25-alltests` (with the two tests imported): result=success; Build completed successfully (1277 jobs).

The diagnosis is confirmed by the build: with per-call hole names in `memTactic` the base command
`#machine_design_svR0` goes through on a parent with TWO memory entries. AllTests (incl. the old-vs-new type
comparison `DepthSwitchTypeTest`, the seqMem tests and the compare tests) is green: no generated statement
changed.

Established by `#machine_no_ports_memseq`, for two NEW declarations:
- `seqAccSync` (register parent; leaf register children `cnt` and `acc`; one sync memory, aw 3, dw 8) and
- `seqTwoMem` (the same two leaves; a combo memory (4, 8) and a sync memory (3, 8) — per-entry widths):
against `f.machine_design_svR0` (generated in the same file by the built command) the premises
`shipsHierCheck`, `kidsMixed`, `designCheck … 0`, `outsCheck … 0` are absent from
`f.machine_design_noPortsR0`, and `MachineClosesAt f` from `…_closed`; under the existentials
`ChildBnd ∧ MachineDefines` of the leaf callees; 0 NOT ALLOWED; goal-gap theorem; standard axioms (the tests'
audits throw otherwise). Scope: one declaration each, depth 0, decided data conditions, runtime boundary,
`DesignSV` of the module list, not the SV string, not `#sim`.

```
st.lean:114:0: NOPORTS MEMSEQ Sparkle.Tests.Compiler.NoPortsMemSeqGenNew2Test.seqAccSync: GENERATED
st.lean:149:0: NOPORTS MEMSEQ NEW2 AUDIT Sparkle.Tests.Compiler.NoPortsMemSeqGenNew2Test.seqAccSync: GENERATED by #machine_no_ports_memseq; Sparkle.Tests.Compiler.NoPortsMemSeqGenNew2Test.seqAccSync.machine_design_noPortsR0, Sparkle.Tests.Compiler.NoPortsMemSeqGenNew2Test.seqAccSync.machine_design_noPortsR0_closed, Sparkle.Tests.Compiler.NoPortsMemSeqGenNew2Test.seqAccSync.machine_design_noPortsR0_closed_gap and 39 named lemmas Sparkle.Tests.Compiler.NoPortsMemSeqGenNew2Te
t.lean:129:0: NOPORTS MEMSEQ Sparkle.Tests.Compiler.NoPortsMemSeqGenNewTest.seqTwoMem: GENERATED
t.lean:164:0: NOPORTS MEMSEQ NEW AUDIT Sparkle.Tests.Compiler.NoPortsMemSeqGenNewTest.seqTwoMem: GENERATED by #machine_no_ports_memseq; Sparkle.Tests.Compiler.NoPortsMemSeqGenNewTest.seqTwoMem.machine_design_noPortsR0, Sparkle.Tests.Compiler.NoPortsMemSeqGenNewTest.seqTwoMem.machine_design_noPortsR0_closed, Sparkle.Tests.Compiler.NoPortsMemSeqGenNewTest.seqTwoMem.machine_design_noPortsR0_closed_gap and 43 named lemmas Sparkle.Tests.Compiler.NoPortsMemSeqGenNewTest.seqTwoMe
```
