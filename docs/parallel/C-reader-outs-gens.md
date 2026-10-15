# Worker C (`par/r-5`): the reader's output facts in the other generators

Base poc `c1c651a0`. **WRITTEN, NOT BUILT.** Nothing here was compiled or run.
READ = read in this tree; PREDICTED = worked out by reading.

Ruling (reviewer, 2026-10-15): connect the general lemmas usable on the REAL
reader (`Tools/ShippingReaderOutsInv.lean` `outTy_of_core` /
`outScalar_of_core`; `Tools/ShippingReaderOutNames.lean` `outNames_of_core`,
`outsNodup_of_core`, `outsNe_of_core`, `outsOk_of_core`) to the generators
that still decide those facts per declaration; per generator: which
generated decide / premise disappears, a type comparison old vs new on one
tree (old path kept as a flag), axioms. Lemmas are not progress.

## 0. Commits, files, build order

| commit | generator | files |
|---|---|---|
| `2f613eac` | `#machine_no_ports_memseq` | `Tools/ShippingNoPortsMemSeqCommand.lean`; `Tests/Compiler/NoPortsMemSeqGen{New,New2,Compare}Test.lean` (name lists); NEW `Tests/Compiler/NoPortsMemSeqGenOldDataTest.lean` (target-only) |
| `99cbb099` | `#machine_oneout` | `Tools/ShippingOneOutGenCommand.lean`; consumers `Tools/ShippingNoPortsKidsCommand.lean`, `Tools/ShippingNoPortsDeepCommand.lean`, `Tests/Compiler/NoPortsGrandHTest.lean`; `Tests/Compiler/OneOutFamilyTest.lean` (audit); NEW `Tests/Compiler/OneOutGenOldDataTest.lean` (target-only) |
| `3686278a` | `#machine_oneout_any` | `Tools/ShippingOneOutAnyGenCommand.lean`; `Tests/Compiler/OneOutAnyFamilyTest.lean` (audit); NEW `Tests/Compiler/OneOutAnyGenOldDataTest.lean` (target-only) |
| (this) | — | this record |

No file under `Sparkle/` changed. No existing theorem statement changed
(every generated STATEMENT is the same text; only proofs differ). ALLOWED
unchanged. No new `Tools` module: **no lean_lib line**. New test modules are
under the `Tests` glob.

Build order (serial):

1. `lake build Tools.ShippingNoPortsMemSeqCommand` (adds `import Tools.ShippingReaderOutsInv`, BUILT).
2. `lake build Tools.ShippingOneOutGenCommand Tools.ShippingOneOutAnyGenCommand Tools.ShippingNoPortsKidsCommand Tools.ShippingNoPortsDeepCommand`.
   The cone is large: `ShippingNoPortsKidsCommand` is imported by `ShippingNoPortsMemCommand` → `ShippingNoPortsMemSeqCommand`, `ShippingNoPortsMemKidCommand`, `ShippingDesignCoverage`, …; let `lake` rebuild it.
3. AllTests modules whose text changed: `Tests.Compiler.NoPortsMemSeqGenNewTest`, `NoPortsMemSeqGenNew2Test`, `NoPortsMemSeqGenCompareTest`, `OneOutFamilyTest`, `OneOutAnyFamilyTest`, `NoPortsGrandHTest`. Rebuilt through imports (they run the switched commands): `OneOutTwoCalleeTest`, `OneOutCallerBadTest`, `OneOutInnerPickTest`, `OneOutCallerInnerTest`, `OneOutMidHTest`, `OneOutCallerFullTest` and everything importing the changed `Tools` (practically every `NoPorts*` / `OneOut*` test). Then `Tests.AllTests` + `DesignCoverageTest` (census should be unchanged: suite population only).
4. Target-only, ONE AT A TIME:
   * `Tests.Compiler.NoPortsMemSeqGenOldDataTest` — NEVER with `NoPortsMemSeqGenOldNamesTest` (both add `…_regen` of `seqTwoMem`);
   * `Tests.Compiler.OneOutGenOldDataTest`;
   * `Tests.Compiler.OneOutAnyGenOldDataTest`.
   Also worth a run (target-only consumers of a one-output callee): `Tests.Compiler.NoPortsKeccakSpongeTest` (`wKeccakF` through `oneOutKidTheorem`).

## 1. `#machine_no_ports_memseq` (`2f613eac`)

**Removed per declaration (2 decides):** `f.noPortsMemSeq_outTy`
(`∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width`) and
`f.noPortsMemSeq_outScalar` (`… scalarTy o.ty = true`), each a `decided`
(`first | decide | decide +kernel`). READ: their only readers were the four
run theorems; `closingTheorems`, `leafKid`, `endpointTerm` never read them.

**In their place** (inside the run theorems, which bind `hcore`, `entry`):

    runFacts / outsG0 / mixedG / designP0 : … $ne $outTyT …
      outTyT     := Tools.ShippingReaderOutsInv.outTy_of_core hcore entry
      outScalarT := Tools.ShippingReaderOutsInv.outScalar_of_core hcore entry   (designP0)

**Old path:** `Ctx.oldData`; `#machine_no_ports_memseq_olddata[_try]`.

**Comparison** (`Tests/Compiler/NoPortsMemSeqGenOldDataTest.lean`, target-only):
imports `NoPortsMemSeqGenNewTest` + `NoPortsMemSeqGenNew2Test` (default path,
in AllTests), runs `#machine_no_ports_memseq_olddata_try f "REBUILT"` on
`seqTwoMem`, `seqAccSync`; the old path takes the built compare path (`…_regen`,
`isDefEq` of the types, an error otherwise). Asserted: every shared name
(each audit's own lemma list minus the two, plus the two endpoints) has an
`isDefEq` `_regen` on standard axioms; the four run theorems' direct
constants: new `outTy_of_core` (designP0 also `outScalar_of_core`) and not the
decided lemma, `_regen` the reverse; the two decided lemmas exist now without
`_regen`. **Exact count: 43 (seqTwoMem) + 39 (seqAccSync) = 82**, non-zero.
Number of syntactically equal types logged.

Audits updated (in AllTests): `NoPortsMemSeqGenNewTest`, `…New2Test`,
`…CompareTest` drop `outTy` / `outScalar` from their lists and THROW if
either is generated.

## 2. `#machine_oneout` (`99cbb099`)

**Removed per declaration (2 decides):** `f.oneout_outTy` and
`f.oneout_outScalar` (`dataLemma … (by decide)`).

**In their place**, in the six head lemmas (`mkThm` binds `hcore`, `entry`):
`outTy_of_core hcore entry` in `machine_factsH`, `_outsH`, `_portsRawH`,
`_portsShippedH` (inside `core_hierGate_any`), `_hierTypedH`,
`_designFullH`; `outScalar_of_core hcore entry` in `_portsRawH`,
`_hierTypedH`, `_designFullH`.

**Consumers of the two names (READ, changed):** a one-output CALLEE `k`
consumed by `#machine_no_ports_kids` / `#machine_no_ports_deep`
(`oneOutKidTheorem`: `OneOutKid` fields `outTy`, `outScalar`) and the hand
`midH_kid` in `NoPortsGrandHTest`. No run of `k` is in scope there (only
`MachineDefines k`), so the reader lemmas DO NOT APPLY: those fields are now
`by first | exact k.oneout_outTy | decide`, and the two names left the
prerequisite lists of both scopes. So for a consumed callee the two decides
MOVE to the consumer (net 0 for e.g. `midH`, `wKeccakF`); for every other
`#machine_oneout` declaration they are gone.

**Old path:** `#machine_oneout_olddata[_try]`. `emitOrVerify` gained
`(keep : Bool := false)`; the old path keeps the scratch `n.oneout_expected`
of every PARENT name (data lemmas, `kidIns`, the six) instead of dropping it,
so the test can inspect it; callee facts compared and dropped as before
(several parents share `pick`).

**Comparison** (`Tests/Compiler/OneOutGenOldDataTest.lean`, target-only):
imports `OneOutFamilyTest`; `#machine_oneout_olddata_try f "PRESENT"` on
`caller`, `callerTwice`, `callerD`, `callerNested`, `callerRep`. Asserted per
declaration: 17 shared parent names (10 data lemmas, `kidIns`, six lemmas)
with an `isDefEq` scratch on standard axioms; direct constants of the six
(new: `outTy_of_core`, three with `outScalar_of_core`; old: the decided
lemmas); `f.oneout_outTy` / `_outScalar` exist now without a scratch.
**Exact count: 5 × 17 = 85**, non-zero.

`OneOutFamilyTest.audit` (used by 8 tests): `generatedNames` without the two;
THROWS if either exists (`readerNames`).

## 3. `#machine_oneout_any` (`3686278a`)

**Removed per declaration (2 decides):** the PARENT's `f.oneout_outTy`,
`f.oneout_outScalar`; the six lemmas as in §2.

**NOT removed:** a machine-leaf callee's `c.leaf_outTy`, `c.leaf_outScalar`
(fields of `SlotlessLeaf`, proved with only `MachineDefines c`; no run of `c`).

**Old path:** `#machine_oneout_any_olddata[_try]` (keep mode for parent names).

**Comparison** (`Tests/Compiler/OneOutAnyGenOldDataTest.lean`, target-only):
imports `OneOutAnyFamilyTest`; `…_olddata_try f "PRESENT"` on `callerL`,
`callerLN`, `hftByte`, `callerMix` (`callerMix`'s names were generated by the
default `#machine_oneout`; the old any-path is compared against them).
**Exact count: 4 × 17 = 68**, non-zero. `OneOutAnyFamilyTest.condsOf`
without the two; `auditAny` THROWS if either exists.

## 4. What else decides an output fact (READ), and why not switched here

| decided | where | why not from the reader lemmas here |
|---|---|---|
| `outTy` / `outScalar` of a CALLEE interface | `leafKidTheorem` (`ShippingNoPortsCommand`), `combKidTheorem` (`ShippingCombLeafCommand`), `GenKid` (`ShippingNoPortsDeepCommand` 322/327), `genKidM` (`ShippingNoPortsMemKidCommand`), `oneOutKidTheorem`, `leaf_outTy` / `leaf_outScalar` (`ShippingOneOutAnyGenCommand`) | the structures are built from `MachineDefines c` alone; `outTy_of_core` needs a RUN of `c`'s entry (`hcore`). Would need a reader lemma from `MachineDefines` + an environment fact, or the child's run threaded into these structures |
| the head premise `houtTy` | `#machine_ships_hier` (`ShippingMachineShipsHierCommand` 129–131, `mkDecideProof`), `ShippingMachineComposeRCommand` 345–346, `ShippingMachineDepthCommand` 473–474 (+ heads copied from those by `ShipsNoOuts`, `ShipsFree`, `OneOut`, `NoPorts*` commands) | `houtTy` is an argument of the HEAD theorems (`machine_ships_hier*`) BEFORE the run binders; using `outTy_of_core` needs NEW head alternatives that take it under the run. Not a generator-only change; follow-up |
| `outChars`, `outHead` (charOk / first char) | all memory / one-output generators | NOT implied by the reader (R-reader-outs-inv-2 §2.3) |

`outNames_of_core`, `outsNodup_of_core`, `outsNe_of_core`, `outsOk_of_core`:
READ every `elab "#…"` under `Tools/` again — no generator decides
`outNameOk`, the names' `Nodup` or `outs ≠ []` separately (they are conjuncts
of `MachineData.ok`, decided once as `f.machine_ok`). **No decide removed by
them in this round** (as R-reader-outs-inv-2 §2.2 found).

## 5. Predicted axioms

Every generated theorem on both paths: `[propext, Classical.choice,
Quot.sound]` (the reader lemmas are, MEASURED in R-reader-outs-inv-2's
integration for `outTy_of_core` / `outScalar_of_core`; `emit` checks the
three for every generated constant). No `sorry`, no new axiom, no
`native_decide`.

## 6. Risks (PREDICTED)

1. `first | exact k.oneout_outTy | decide` relies on `first` catching the
   unknown-identifier error (the same reliance as par/r-2's
   `MemParentFreeTest`, BUILT). The `decide` on `wKeccakF`'s outputs runs in
   the consumer now (same proposition as the former `by decide` in the
   generator; cost unchanged, moved).
2. `outTy_of_core hcore entry` must elaborate against the head's
   hypothesis type `∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width`:
   `shape` is fixed by `entry : MachineDefines … f (d).shape`, `M := raw` by
   `hcore`. Hygiene: `hcore` / `entry` are written in a separate quotation
   from the binder's (the same elab run, as `hB hcore hpost entry closes`
   already are).
3. `emitOrVerify (keep := oldData) name cond fun id => …`: named argument
   before the positional ones (the new parameter is LAST, after `mk`). All
   other callers unchanged (default `false`).
4. Keep mode: `name.oneout_expected` for a definition (`kidIns`) and for
   theorems; `emit` is the built one (adds, checks the axioms).
5. The class of the old runs: `PRESENT` (the endpoint exists; rebuilt from
   the existing lemma names, recorded marker equal). For `caller` / `callerL`
   (hand endpoints) the `_gen` exists already from the default run and is
   compared.
6. `getUsedConstants` of the six / four run theorems: `outTy_of_core` is an
   explicit argument (not inside a `by` block), so it is a direct constant.

## Integration (integrator, 2026-10-15) — BUILT; one test list updated
Applied on poc f9807b42. Run `c2` (cgrun, 3 GiB, swap 0, `-j 1`): `Tools.ShippingNoPortsMemSeqCommand`, the
four generator commands, `Tests.AllTests` + `DesignCoverageTest` (census 134 / 133, unchanged), and the three
target-only comparison tests: exit 0. MEASURED:
* `NOPORTS MEMSEQ OLDDATA COMPARE: 82 pairs over 2 declarations, all isDefEq (82 syntactically equal); per
  declaration the default path decides 2 output facts fewer (noPortsMemSeq_outTy, noPortsMemSeq_outScalar).`
* `ONEOUT OLDDATA COMPARE: 85 pairs over 5 declarations, all isDefEq (85 syntactically equal); … 2 fewer
  (oneout_outTy, oneout_outScalar).`
* `ONEOUT ANY OLDDATA COMPARE: 68 pairs over 4 declarations, all isDefEq (68 syntactically equal); … 2 fewer.`
The target-only `NoPortsKeccakSpongeTest` failed at its step 1 because its prerequisite list required
`wKeccakF.oneout_outTy` / `oneout_outScalar`, which `#machine_oneout` no longer generates (for a consumed
callee they are decided inside `oneOutKidTheorem` — net zero for `wKeccakF`); integrator fix: the two names
removed from that list (comment added). Run `c2s`: exit 0.
Net effect: two per-declaration decides removed from every parent generated by these three commands; for
consumed one-output callees (`midH`, `wKeccakF`) and leaf callees the two facts are still decided (no run of
the callee in scope). The head premise `houtTy` is still decided (`#machine_ships_hier`, ComposeR, Depth).
