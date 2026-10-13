# B — the generators after the injective module names: no per-declaration candidate proofs (round par/b-30)

Branch `par/b-30` from `poc/roundtrip-proof` bfa5f5fe. Worker B.

**NOTHING HERE IS BUILT.** No `lean`, `lake` or simulator was started. Every
change is WRITTEN, NOT BUILT. Marks: **[R]** read at bfa5f5fe; **[B]** built
per the record of 812061e5 (not re-run); **[I]** inferred.

**No endpoint loses a premise in this round, and none is claimed to.** By
the census of `B-name-discharge.md` no generated endpoint of the built tree
has a name binder. What changes is the PROOF of generated closings and name
lemmas; every generated endpoint keeps its NAME and its TYPE. Where a
generated lemma disappears or a refusal is removed, it is listed.

Commits, smallest first (build in this order; each builds without the next):

| | commit | subject |
|---|---|---|
| 1 | 32c90389 | `#machine_no_ports_mem` |
| 2 | 25ef0de2 | the closing generators |
| 3 | bc6dadbf | `#machine_no_ports_memseq` |
| 4 | this file | |

One switch serves commits 2 and 3: `set_option shipping.nameCandidates true`
(`Tools/ShippingNameMode.lean`, new in commit 2) gives the previous proofs
and refusals. Commit 1 keeps its previous path as a second command name
instead (it was written first and must build alone).

## 1. Commit 1 — `#machine_no_ports_mem`

Files: `Tools/ShippingNoPortsMemCommand.lean`;
`Tests/Compiler/NoPortsMemGenFamilyTest.lean` (target-only),
`Tests/Compiler/NoPortsMemGenCompareTest.lean` (in `AllTests`),
new `Tests/Compiler/NoPortsMemGenOldNamesTest.lean` (target-only).

Change: `f.noPortsMem_closes` is
`Tools.ShippingMemOnlyNames.machineClosesAt_of_memOnlyData_names
f.noPortsMem_data f.noPortsMem_closeData` ([B] at 812061e5) instead of
`machineClosesAt_of_memOnlyData … sepT parentT`.

The memory-only declarations the command is run on [R:
`NoPortsMemGenFamilyTest.lean` 73–93; `NoPortsMemGenCompareTest.lean` 40]:
`memCounter`, `twoMems`, `mixedMems` (`ShippingMachineMemLinkedTest`),
`syncNarrow`, `memWide` (`ShippingDesignSVMemTest`), `withMemory`
(`ShippingMachineFuseTest`).

| generated declaration | name | type | proof |
|---|---|---|---|
| `f.machine_design_noPortsR0`, `…_closed` (and `…_closed_gap`) | same | same | same text (they apply `f.noPortsMem_closes`) |
| `f.noPortsMem_closes` | same | same (`MachineClosesAt … f f.machineData.shape`, no premise) | CHANGES |
| `f.noPortsMem_entry … _closeData` (20 lemmas) | same | same | same |
| `f.noPortsMem_notin{j}`; for ≥ 2 placeholders `…_at{j}`, `…_namesNe{i}_{j}`, `…_sep`, `…_parent` | NO LONGER GENERATED | — | — |

The previous path: `#machine_no_ports_mem_oldnames f`,
`#machine_no_ports_mem_oldnames_try f "…"` (the same generator with
`oldNames := true`).

How to check name and type:

* `Tests.Compiler.NoPortsMemGenCompareTest` (`AllTests`, [B] before this
  change): the command on `memCounter` beside the HAND test; it asserts
  `isDefEq` of the generated `machine_design_noPortsR0` / `…_closed`
  statements with the hand ones, and of `memCounter.noPortsMem_closes` with
  the hand `memCounter_closes` (65–70). Unchanged except that `notin0` is no
  longer expected.
* `Tests.Compiler.NoPortsMemGenOldNamesTest` (new): after the family test's
  six generations, the previous path on `memCounter` and `mixedMems` in the
  same environment → the command's compare path on every shared name
  (`emit` / `addOrCompare`: rebuilt as `…_regen`, statement `isDefEq` or an
  error); then asserted: `noPortsMem_closes_regen`,
  `machine_design_noPortsR0_regen`, `…_closed_regen` exist with `isDefEq`
  statements; the new closing applies `…_names`, the regenerated one the
  theorem with name hypotheses; the old name lemmas appear only now.
* `NoPortsMemGenFamilyTest` audit: the old name lemmas are ABSENT; the
  closing's proof term applies `…_names` and not the old theorem.

Risks: (i) `return` inside `unless c.oldNames do … return` in
`closingTheorems`; (ii) the default-valued structure field
`Ctx.oldNames` — `Tools/ShippingNoPortsMemSeqCommand.lean` builds this `Ctx`
too, by structure-instance notation (`m := { f, s := default, log }`, [R]
1005 after commit 3), so the default applies; (iii) in the old-path
compare run, `core` closes the regenerated open endpoint with the EXISTING
`noPortsMem_closes` — the regenerated closing is compared by statement only.

## 2. Commit 2 — `closesAtCore`, `closesAtCoreG`, `closesDeep`, `ifaceDeep`

Files: new `Tools/ShippingNameMode.lean` (two options);
`Tools/ShippingMachineClosesAtGen.lean`, `…AtGenG.lean`,
`Tools/ShippingChildIfaceGen.lean`; tests `OneOutTwoCalleeTest`,
`ShippingCallsCloseTest`, `ShippingChildBoundaryTest`,
`ShippingCallsCloseDeepTest` (wording only), new
`Tests/Compiler/NameGenCompareTest.lean` (target-only).

| condition | before | now (default) | binder when |
|---|---|---|---|
| `hnames` / `hsep` | one callee: `decide` on Names; several: `Enc.hnames_of _ (by decide)` if `sepB`; else BINDER | `Tools.ShippingNameDischarge.names_inj _` always | never (the statement is true of all names) |
| `hparent` | `Enc.hparent_of _ _ (by decide)` if `sepB`; else BINDER | `parent_ne _ _ (by decide)` if no callee IS the parent (`k != c`) | a call entry is a call of the parent itself (condition false) |
| `hparentD`, `hselfD`, `hdisjD` (`closesDeep`) | all leaves: `by decide`; `namesSep`: `Enc.not_mem_map_of` / `Enc.disjoint_map_of` on `sep`; else THREE BINDERS | all leaves: unchanged; `namesOk` (the same three conditions on the declarations): `not_mem_map` / `disjoint_map` with `decide` on Names | `namesOk` false — `mixDeep` (`midH` callee and descendant of `mid2`): the same three binders `hN_…_parentD/_selfD/_disjD`, same text as before |
| `hself` (`ifaceDeep`) | `Enc.not_mem_map_of _ _ (by decide)` if `sepB`; else BINDER | `not_mem_map (by decide)` if the declaration is not among its descendants | it is (condition false) |
| `hfresh` | unchanged | unchanged | unchanged |

Nothing is refused that was accepted; no branch throws where it produced a
binder. The binder branch is now taken exactly when the condition on the
`Name`s is false. Two consequences, both outside the built tree [R]:
a parent of declarations that `sepB` could not separate (Finding H's
`«#ccp.k»` / `«#ccp».k`) would have got name binders and now gets none (its
TYPE would differ from what the old generator gave — no such closing exists
in the tree); `mixDeep`'s generated `closes_deep` (not run in the tree:
`NoPortsMixDeepTest` deliberately omits it) keeps its three binders, of
which `hdisjD` is false.

Generated declarations whose PROOF changes (name and type expected
unchanged): every `c.machine_closes_at` (`#machine_closes_at`, and the
depth command `Tools/ShippingMachineDepthCommandR.lean` 1027), every
`c.closes_deep` and `c.iface_deep` (`#machine_closes_deep`, the depth
command 1035, `#machine_closes_shared` through `ifaceDeep`). Explicit
command lines [R: grep]: `caller`, `callerTwice`, `callerNested`, `callerD`,
`midH`, `callerMix`, `callerL`, `callerLN`, `hftByte`, `callerABA`,
`callerRep`, `parent`, `chained` (`ShippingCallsCloseTest`), `loopParent`,
`wKeccakF`, `callerInner`, `mesh2x2`, `twinCalls`, `mid`, `callerBad`,
`innerPick`, `two`, `engineOnce`; deep: `grand`, `grandH`, `mixD1`, `topD2`
(with `mid`, `midH`, `mid2` below them). Those made implicitly by
`#machine_design_svNR` / `#machine_oneout…` I did not enumerate.
Everything that APPLIES these theorems (`_closed` endpoints, the no-ports
endpoints) keeps its proof text.

The previous proofs: `set_option shipping.nameCandidates true in …`. A
second set of deep closings beside the first: additionally
`set_option shipping.deepSuffix "_x" in …` (names `c.closes_deep_x`,
`c.iface_deep_x`).

How to check name and type:

* Existing statement audits, unchanged and in `AllTests`:
  `ShippingCallsCloseTest` (`auditClosed f 1|2`: the premise COUNT of
  `machine_closes_at` and that each is a reflection), `OneOutTwoCalleeTest`
  (exactly one `EntryDefines` per callee, no binder mentioning `ofDecl`),
  `ShippingCallsCloseDeepTest` 100–112 (`closes_deep` of `grand`, `grandH`,
  `mixD1`, `topD2`: 2, 2, 3, 3 premises, all reflections).
* `closesAtTheorem` itself: for an EXISTING `c.machine_closes_at` it
  regenerates the statement and requires `isDefEq` ([R] 228–247). So
  `set_option shipping.nameCandidates true in #machine_closes_at f`, run
  after the default generation, is an old-against-new `isDefEq` of the type
  (and of each `_closed` endpoint, `closeEndpointAt` 279–287) with the old
  proof kernel-checked and dropped.
* `Tests.Compiler.NameGenCompareTest` (new): `callerMix` (two callees),
  `parent` (the general closing) → `…machine_closes_at_candidates` by the
  previous path, statement `isDefEq`; `grand` → `grand.closes_deep_candidates`,
  `mid.closes_deep_candidates`, `mid.iface_deep_candidates`, each `isDefEq`
  its default twin. Extend by one line per declaration.
* `DepthSwitchPinTest` (target-only): fingerprints of the 51 depth
  statements — a secondary check; equal fingerprints are NOT `isDefEq`.

What the changed test assertions now check (all on the DIRECT constants of a
proof term, `ti.value.getUsedConstants`; none inspects which names were
compared):

| test | before | now |
|---|---|---|
| `OneOutTwoCalleeTest.twoCallee` 106–112 | `Enc.hnames_of` AND `Enc.hparent_of` occur in `f.machine_closes_at`'s proof | `Tools.ShippingNameDischarge.names_inj` AND `parent_ne` occur, and NEITHER `Enc.hnames_of` NOR `Enc.hparent_of` does. Together with the unchanged binder checks: the name conditions are discharged in the proof, from the declaration names |
| `ShippingCallsCloseTest.auditClosed` (187) and `auditClosedNR` (616) | `provedNames` := `Enc.hparent_of` occurs | `provedNames` := `parent_ne` occurs. The surrounding logic is unchanged: an error if the name condition is neither stated in the closed endpoint nor `provedNames` |
| `ShippingChildBoundaryTest.closingAudit` (225) | the same for `midH.machine_closes_at` | the same with `parent_ne` |

Risks: (i) `register_option` at the root of a new file and
`shipping.nameCandidates.get (← getOptions)` inside the generators'
`CommandElabM` code (pattern of `vc.shareAlts`, `Tools/ShippingChildVC.lean`);
(ii) `parent_ne _ _ (by decide)` as an argument whose `parent` comes from the
expected type — the previous `Enc.hparent_of _ _ (by decide)` had the same
dependency and built; the same lemma with `(by decide)` built in
`NameDischargeTest` on literal lists, not on `f.machineData.shape.insts`;
(iii) the four new `by decide` statements of `closesDeep` (`∀ k, k < n → c ∉
List.getD kds k []`, and the two with `a ≠ b → …`): bounded quantifiers over
`Nat`, an implication, `∉` on `List Name` — the previous ones decided
`(… .all …) = true` under the same quantifiers; (iv) `namesOk` (generation
time) and the kernel `decide` must agree: both read `Node.decls` /
`$kds`, as `namesSep` did; if they disagree the generated proof fails (class
"the generated proof fails"), it is not silently a binder; (v) kernel cost
of the new decides: expected far below `sepB` (no enumeration), NOT measured.

## 3. Commit 3 — `#machine_no_ports_memseq`

Files: new `Tools/ShippingMemSeqNames.lean`;
`Tools/ShippingNoPortsMemSeqCommand.lean`; new
`Tests/Compiler/NoPortsMemSeqGenOldNamesTest.lean` (target-only).

General lemmas (over `memModule_name`, [B]):

```lean
theorem decl_ne_memName (c : Lean.Name) (cb : Bool) (aw dw : Nat) :
    ofDecl c ≠ (memModule cb aw dw).1.name
theorem decl_not_mem_memName (c : Lean.Name) (cb : Bool) (aw dw : Nat) :
    ofDecl c ∉ [(memModule cb aw dw).1.name]
theorem memName_ne {cb cb' : Bool} {aw dw aw' dw' : Nat}
    (h : ¬ (cb = cb' ∧ aw = aw' ∧ dw = dw')) :
    (memModule cb aw dw).1.name ≠ (memModule cb' aw' dw').1.name
```

Declarations the command is run on [R]: `seqMem` (compare path, beside the
hand test), `seqTwoMem`, `seqAccSync`.

| generated declaration | name, type | proof |
|---|---|---|
| the two endpoints, `f.noPortsMemSeq_closes`, `_sep`, `_parent`, `_parentD`, `_disj`, every other lemma and table | same | same text |
| `f.noPortsMemSeq_notinP{j}`, `…_leafNotin{i}_{j}` | same | `decl_not_mem_memName _ _ _ _` (was `by name_not_mem`) |
| `…_leafNeParent{i}`, `…_leafNe{i}_{j}` | same | `ofDecl_ne (by decide)` on Names (was `Enc.sep_ne (by decide)` on `sep`) |
| `…_memNe{i}_{j}` | same | `memName_ne (by decide)` on the parameters (was `decide` on two strings) |

Refusals (generation time, `scope` 253–274 [R]):

| refusal | state | why |
|---|---|---|
| parent's `ofDecl` = a memory module's name | REMOVED | cannot hold: `decl_ne_memName` covers every declaration and every memory module |
| a leaf's `ofDecl` = a memory module's name | REMOVED | the same lemma |
| two leaves not separated by `sep` | REMOVED | the leaves are distinct `Name`s (`eraseDups`, 185); `ofDecl_ne` covers all distinct declarations |
| two placeholders with one module name | REMOVED | distinct placeholders have distinct `(combo, aw, dw)` (`memParamsOf` is injective on its pattern [R] 121–126); `memName_ne` covers them |
| a leaf not separated from the parent by `sep` | KEPT, restated on the names: refused iff the leaf IS the parent (`c == f`) | `ofDecl_ne` needs `c ≠ f`. By reading it cannot fire (a leaf callee has no call, `f` has); kept so that a false condition is a REFUSED line, not a failed proof |

Nothing that was accepted is refused. A parent that was refused only because
`sep` (candidate renderings) did not separate two DIFFERENT names is now
accepted — no such declaration is in the tree. Under
`shipping.nameCandidates` the five previous refusals and the previous proofs
are back.

How to check: `Tests.Compiler.NoPortsMemSeqGenCompareTest` (`AllTests`):
the command beside the hand `seqMem` test, endpoint statements `isDefEq`.
`NoPortsMemSeqGenNewTest` / `…New2Test` (`AllTests`): their audits list the
name lemmas by name — unchanged, they still exist. New
`NoPortsMemSeqGenOldNamesTest`: `seqTwoMem` again under
`shipping.nameCandidates` → compare path on EVERY generated name; then
`isDefEq` asserted for the ten name lemmas, `sep`, `parent`, `parentD`,
`disj`, `closes` and the two endpoints, and which lemma each proof applies;
it also LOGS the direct constants of the previous `notinP0` (which branch
`name_not_mem` took).

Risks: (i) `decl_not_mem_memName _ _ _ _` against the stated
`… ∉ ([(memModule true 4 8).1.name] : List String)` — unification of the
three parameters with literals; (ii) `ofDecl_ne (by first | decide | decide
+kernel)` on two quoted names; (iii) `memName_ne (by …)` with goal
`¬ (true = false ∧ 4 = 4 ∧ 8 = 8)`; (iv) the `if … then … else` around the
refusal loops in `scope`.

## 4. Build order and integrator lines

`lakefile.lean` (not edited):

```lean
lean_lib «Tools.ShippingNameMode» where
  roots := #[`Tools.ShippingNameMode]

lean_lib «Tools.ShippingMemSeqNames» where
  roots := #[`Tools.ShippingMemSeqNames]
```

`Tests/AllTests.lean`: nothing to add. The three new tests are target-only:
`NoPortsMemGenOldNamesTest` MUST stay out (it imports the target-only family
test); `NameGenCompareTest` and `NoPortsMemSeqGenOldNamesTest` add only new
names and may be added at the integrator's choice (cost: the previous
path's proofs).

Order:

1. commit 1: `Tools.ShippingNoPortsMemCommand` → `Tests.AllTests`
   (`NoPortsMemGenCompareTest`) → targets `NoPortsMemGenFamilyTest`,
   `NoPortsMemGenOldNamesTest`.
2. commit 2: `Tools.ShippingNameMode` → the three generators →
   `Tests.AllTests` (the closing and depth tests are most of it) → target
   `NameGenCompareTest`; optionally `DepthSwitchPinTest`.
3. commit 3: `Tools.ShippingMemSeqNames` → `Tools.ShippingNoPortsMemSeqCommand`
   → `Tests.AllTests` → target `NoPortsMemSeqGenOldNamesTest`.

A statement that may be recorded only after the build: "the proofs of
⟨list⟩ no longer evaluate candidate renderings; names and types unchanged
(isDefEq against the previous path for ⟨the compared ones⟩)". Not: "an
endpoint lost a premise".

## 5. After this round: who still evaluates candidate renderings of `Name.toString`

In the KERNEL (a `decide` over `sepB` / `sep` / `cands`), with default
options:

| user | what | why it is left |
|---|---|---|
| `Tools/ShippingCallsKidsSGen.lean` 54–101 (`#machine_closes_shared`; `CallsKidsSharedMixDeepTest`, not in `AllTests`) | `Enc.hnames_of`, `Enc.hparent_of`, `Enc.not_mem_map_of` with `(by decide)` on `sep`; generation-time `sepB` guards that THROW (54, 56) | not in this round's list; it is worker A's shared-descendant generator. Same replacement applies (`names_inj`, `parent_ne`, `not_mem_map`) |
| `Tools/ShippingNoPortsKidsCommand.lean` 189, `Tools/ShippingNoPortsDeepCommand.lean` 344 | the `self` field of a generated kid fact: `Enc.not_mem_map_of _ _ (by decide)` | not in this round's list. One line each: `Tools.ShippingNameDischarge.not_mem_map (by decide)` |
| hand tests `NoPortsGrandTest` 225, `NoPortsGrandHTest` 205, `NoPortsTopD2Test` 248 | the same `self` proof by hand | hand proofs, built; not touched |
| hand test `NoPortsMemSeqMemClosedTest` 190 | `Enc.sep_ne (by decide)` (`cnt` against `seqMem`) | hand proof, built |
| `Tools/ShippingLegacySemSuffix.lean` 17–19 (`endsWith_false_of`), used by `Tests/Compiler/LegacySemInstanceTest.lean` | hypothesis `((cands c).all fun x => !x.endsWith suffix) = true`, over `Tools.ShippingNameSep.cands` and `toString_mem` — OUTSIDE the `Enc` namespace | this one is about `Name.toString` ITSELF: the legacy handlers test the head's printed name by suffix (`name.toString.endsWith ".register"`), which the compiler still does. It is not a module-name condition and the injective encoding says nothing about it. It STAYS |
| `Tests/Compiler/NameSepTest.lean`, `NameSepFastTest.lean` | tests of the machinery (`sepB`, `sepC`, `hnames_of'`) | they test `ShippingNameSep` itself |
| the previous paths kept for one round | `#machine_no_ports_mem_oldnames`, `shipping.nameCandidates` | only when asked |

Users of `Tools.ShippingNameSep` OUTSIDE `Enc` (theorems / definitions, not
the `Enc.*` wrappers) [R: grep at the head of this branch]: `cands`,
`toString_mem` — `ShippingLegacySemSuffix`; `sepB`, `sep` as generation-time
Booleans — `ShippingCallsKidsSGen` (default path), and the three closing
generators and `ShippingNoPortsMemSeqCommand` on the previous path only;
the tactic `name_not_mem` — `ShippingNoPortsMemCommand` (old path only),
`ShippingNoPortsMemSeqCommand` (old path only), and seven hand tests
(`NoPortsMemOnlyClosed{MemCounter,SyncNarrow,TwoMems,MixedMems,MemWide}Test`,
`NoPortsMemWithMemoryTest`, `NoPortsMemSeqMemClosedTest`); `open
Tools.ShippingNameSep` — the two `NameSep` tests. `name_not_mem` is not a
candidate enumeration: it is `Enc.not_mem_cons_mem` (structural) or a
`decide` evaluating `ofDecl`; which one runs is what
`NAMEDISCHARGE MEASURED` (812061e5's build log) and the new
`NOPORTS MEMSEQ OLDNAMES COMPARE` line report — I do not have those logs.

So after this round, on the default path, the generated closings of the
one-output, general and deep generators, and the generated memory-only and
memory-with-leaf endpoints evaluate NO candidate rendering in the kernel.
What still does: `#machine_closes_shared`, the `self` field of the two
no-ports kid generators, four hand proofs, and the legacy suffix lemma
(legitimately).

When the previous paths are dropped (next round), `Tools.ShippingNameSep`
is needed only for `cands` / `toString_mem` (the legacy suffix test) and its
own two tests — provided the three remaining generator sites and the hand
proofs are moved.

## 6. What I could not determine by reading

* Whether every existing statement really is unchanged: the generators'
  conditions were re-derived by reading; the compare tests and the existing
  audits decide it.
* The complete list of `machine_closes_at` / `closes_deep` / `iface_deep`
  generated implicitly by the depth and one-out commands.
* Kernel time and memory of the new `decide`s, and of the previous path in
  the three compare tests.
* Which branch `name_not_mem` takes (logged by the tests, not readable).
* Whether `leaf == parent` can occur for `#machine_no_ports_memseq` in some
  shape I did not consider (argued impossible from `insts.isEmpty` of a leaf).

## Integrator's build record (2026-10-13)

BUILT on tree `5f13c1cf6a807af24643a9b0e88f0d75ced6a924` (poc 0c103301 + par/b-30's files), cgrun 3 GiB swap 0.
`b30-all` (AllTests + the three compare tests + NoPortsMemGenFamilyTest + NoPortsKeccakSpongeTest): exit 1,
peak 2.16 GB — ONE failing file, `NameGenCompareTest` (parse error at the two option-setting expressions);
everything else built first attempt, generators unchanged by the integrator. `b30-cmp`: exit 1 (my rewrite
had `Lean.Option.set`'s arguments in the wrong order). `b30-cmp2`: exit 0, 1301 jobs, peak 0.39 GB.
The integrator edited `NameGenCompareTest.lean` once while `b30-all` was still running on the tree (the
file had already failed in that run); the final run `b30-cmp2` rebuilt it.

Old path vs new path ON ONE TREE (kernel `isDefEq` of the types, asserting tests, target-only):
* `NameGenCompareTest`: `callerMix.machine_closes_at`, `parent.machine_closes_at`, and `grand`'s deep
  closings against their `_candidates` twins — statements isDefEq; the new proofs apply
  `names_inj` / `parent_ne`, the old `Enc.hparent_of` (/ `Enc.hnames_of`).
* `NoPortsMemGenOldNamesTest`: `memCounter`, `mixedMems` — `noPortsMem_closes`,
  `machine_design_noPortsR0`, `_closed` against `_regen`.
* `NoPortsMemSeqGenOldNamesTest`: `seqTwoMem`, the generated names against `_regen`.
Compared: those declarations only. Every other regenerated closing is covered by the existing audits in
AllTests (premise lists, axiom audits, `DepthSwitchPinTest` fingerprints — a fingerprint is not defEq),
not by an old-vs-new type comparison.

No endpoint's type changed; no endpoint lost a premise. `mixDeep` keeps its three name binders.
