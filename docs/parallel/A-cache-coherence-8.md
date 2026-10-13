# A: cache coherence, step 8 — the walk on every constructor, a census, `EntryOk` generated

Round par/a-41, base poc `202093d6`. **WRITTEN, NOT BUILT**: nothing here was
compiled or run by its author; every "PREDICTED" is from reading. No file
under `Sparkle/`, no built file, no endpoint, no generator of another worker,
no law is changed. `mixDeep` stays OPEN; options 1 and 3 of
`A-det-decision.md` are not touched.

## 1. What is widened

### 1.1 The walk: every constructor of `Term` — `Tools/ShippingWalkStillMore.lean`

`walk_still` (BUILT) covered ten constructors (`wfrag`). The eleven left out
are added, each with the step lemma its BUILT contract uses
(`Tools.ShippingUnifiedRecursion.fuel_contract_leaves`):

| constructor | step rewritten by | arm walked |
|---|---|---|
| `boolLit` | `literal_core` (the core answers `none`) + NEW `step_of_none`, `translateFallback_bool`, `literal_uncached` | one wire, one assign (`emitBoolLiteral`) |
| `bitsNum` | the core's literal arm (`core_literal`, BUILT) with `litValue_numLitE` | one wire, one assign |
| `boolNot` | `boolNot_step`, `translateFallback_bool` | `translateSignalCompare` on the operand and the literal `false` (the IH at `.boolLit false`, as the contract does) |
| `slice` | `slice_step`, `sliceUncached_sliceE` | operand, NEW `emitSlice_S` |
| `sliceF` | `sliceF_step`, `sliceFUncached_sliceFE` | operand, `emitSlice_S` |
| `zextMap` | `zextMap_step`, `setwUncached_zextMapE` | operand, `emitCast_S` (BUILT) |
| `concatLitHi` / `concatLitLo` | `concatLitHi_step` / `concatLitLo_step`, `concatLitUncached_hiE` / `_loE` | NEW `concatActs_S` over NEW `emitConcatConst_S` and the operand |
| `appCompare` | `appCompare_step`, `translateFallback_bool` (`isBoolControl_appCompareE`), `translateBoolUncachedWith_appCompare` | two operands, `emitBool_S` |
| `appBool` | the same with `…_appBool` | two operands, `emitBool_S` |
| `appBool2` | the same with `…_appBool2` | two operands, two `emitBool_S` |

**No constructor is left out, and none reaches a continuation that can touch
the child cache**: each arm is `rec` on operands plus wire / assign
emissions; the legacy hand-over (`translateBoolUncachedWith`'s `legacy`
argument, the `.other` arm of the fallback) is not taken by any constructor
of `Term` — each step lemma rewrites the step to a named certified arm.

Statements:

```lean
def wfragAll {s : SType} (_ : Term s) : Bool := true
theorem step_of_none {fb} {e hint top named}
    (hcore : translateCore rec e hint top named = Pure.pure none)
    (hfb : WSt mctx cctx L mb ctx (fb rec e hint top named)) :
    WSt mctx cctx L mb ctx (translateStepWith fb rec e hint top named)
theorem fuel_still_all (fuel : Nat) … (hbS …) (hvS …) :
    ∀ {s} (e : Term s), e.WF kb kv vw →
      WCh mctx cctx L mb ctx (translateFuelFix translateStep fuel) (quote dom bE vE e)
theorem walk_still_all (hb : ∀ j, j < kb → WBound ctx (bi j)) (hv : ∀ j, j < kv → WBound ctx (vi j))
    {s} (e : Term s) (he : e.WF kb kv vw) :
    WCh mctx cctx L mb ctx (fun e hint top named => translateExprToWire e hint top named)
      (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) e)
```

`walk_still_all` is `walk_still` WITHOUT `wfrag e = true`. So `wfragAll` is
the constant `true`; it exists only so that a measurement can print it.

### 1.2 The consumers

* `entryStill_leaf` (BUILT) takes `HarnessStill` as a hypothesis: parametric,
  reused unchanged.
* `harnessStill_frag` and `entryStill_gate` (BUILT) call `walk_still` with
  `wfrag e = true` inside their proofs: NOT parametric. The smallest refactor
  would be one extra hypothesis "the walk is still on this term" on
  `harnessStill_frag`; that edits a built file, so instead they are
  RE-DERIVED in the new file, the built text with the one call replaced:

```lean
theorem harnessStill_all (he : e.WF kb kv vw) (hb …) (hv …) (hbody : body = quote dom … e) :
    HarnessStill L declName bs body
theorem entryStill_gate_all (hB) (entry) (old) (peel) (he : e.WF kb kv vw) (hb …) (hv …) :
    EntryStill L c
```

(the hypotheses of the built ones minus `wfrag`). `sfc_mixed_val`, `bind_S`,
`emitLeaves_S`, `finishSynth_world` are reused.

## 2. The measurement — `Tools/ShippingFragCensus.lean`, `Tests/Compiler/FragCensusTest.lean`

`#frag_row f` / `#frag_census n` / `#frag_census_summary`: for each
declaration of `Tests.AllTests`' environment with a reflected term
(`f.gateTerm`, else `f.machineData`): `wfrag` of that term (`T` / `F` / `?`)
and, for a machine, whether it has call entries. Kernel `decide` tried in
both polarities inside a saved-and-restored command state (the mechanism of
the built `NoRepeatFamilyTest`); no compiled evaluation of reflected data.
Logs only.

**Meaning.** Since the walk now has no term condition, `wfragAll` is `T` on
every row by definition; the number that says something is `wfrag=F`: the
declarations whose term the first walk did NOT cover and `walk_still_all`
does. And a declaration WITHOUT a row has no reflected term: it is outside
the unit whatever the fragment (legacy route, or no `#machine_endpoint` /
`#gate_child` ran on it).

A row is about the walk's term condition only. `EntryOk` needs more: the
data facts, and for a parent a closing at every invariant world (§3).

**PREDICTED.** The five of the family `wfrag=T` (built theorems say so).
Others: no per-declaration prediction; `F` expected for declarations with
slices, sign / zero extension, numeric literals, Bool negation or
applicative lifts. About 130 rows (B's census: 129 with `machineData`, 3
gate-route).

## 3. `EntryOk` generated — `Tools/ShippingEntryOkCommand.lean`, `Tests/Compiler/EntryOkFamilyTest.lean`

`#entry_ok f` adds `f.entry_ok`:

| kind (read by the compiler's reader on the source) | statement | built from |
|---|---|---|
| gate leaf | `(L) (K) : EntryDefines … f f.gateValue → EntryOk L f K` | `entryOk_leaf`, `entryStill_gate_all`, `childFull_of_real` |
| machine leaf (no call entry) | `(L) (K) : MachineDefines … f f.machineData.shape → EntryOk L f K` | `entryOk_leaf`, `entryStill_leaf`, `harnessStill_all`, `seqChild_of_real`, `f.machine_closes` |
| machine parent (callees with `entry_ok`) | `(L) : refl f → refl d₁ → … → refl dₙ → EntryOk L f (fun k => k = d₁ ∨ … ∨ k = dₙ)` | `entryOk_machine`, `coreVia_of` over `f.closes_deep` / `machine_closes_at` / `machine_closes`, `harnessStill_all`, `hout_of_data`, the callees' `entry_ok` (through `EntryOk.mono`) |

`d₁ … dₙ`: the callees in call-entry order, each followed by its
descendants, first occurrences kept. Helpers: `f.entry_wf`,
`f.entry_callees` (kernel `decide`).

After generation, CHECKED: the statement mentions none of `HarnessStill`,
`EntryStill`, `CoreVia`, `MachineClosesAt`, `MachineCloses`; every
proposition binder is a `MachineDefines` / `EntryDefines`; the conclusion is
an `EntryOk`; standard axioms only. On any failure the environment is put
back (no constant is left).

`#entry_ok_sweep f` / `#entry_ok_summary`: the never-failing form with one
row per declaration. `#entry_ok_same a b`: two statements by `isDefEq`, an
error when they differ.

**The family test.** PREDICTED: `rcH`, `cnt`, `midH`, `mid2` GENERATED (1,
1, 2, 3 premises); `rcH.entry_ok` equal to the stated expectation,
`cnt.entry_ok` to `cnt_entryOk`, `midH.entry_ok` to `midH_entryOk_closed`,
`mid2.entry_ok` to `mid2_entryOk`. `mixDeep`: `FAILED … no closing theorem`
— shown on purpose: `EntryOk` of a parent goes through `CoreVia`, i.e. the
parent's closing at EVERY invariant world, and `mixDeep` has only the
relative `closes_shared`. That is the same open premise as before, seen from
this unit.

**What a GENERATED row is**: `EntryOk` of ONE declaration — a returning run
of its entry from an invariant world of positive depth whose cache satisfies
`Prov` and has no entry for it. Premises: reflections only. It is not an
endpoint, and it says nothing about worlds without `Prov`.

**REFUSED by design**: a memory call entry; a callee without `entry_ok`; a
missing data fact; a parent without a closing theorem. Not covered and not
detected beforehand (they FAIL with the elaboration error in the row):
slotless machine leaves if `seqChild_of_real`'s hypotheses do not hold for
them; a closing theorem under a suffixed name (`ShippingNameMode`).

## 4. Build queue (integrator)

`lakefile.lean` (not edited):

    lean_lib «Tools.ShippingWalkStillMore» where
      roots := #[`Tools.ShippingWalkStillMore]
    lean_lib «Tools.ShippingFragCensus» where
      roots := #[`Tools.ShippingFragCensus]
    lean_lib «Tools.ShippingEntryOkCommand» where
      roots := #[`Tools.ShippingEntryOkCommand]

`Tests/AllTests.lean`: nothing (the three tests are target-only).

Order:

1. `Tools.ShippingWalkStillMore` (imports `Tools.ShippingHarnessStill`).
2. `Tools.ShippingFragCensus`, `Tools.ShippingEntryOkCommand` (both import 1).
3. `Tests.Compiler.EntryOkFamilyTest` (imports
   `Tests.Compiler.MixDeepOutermostTest`): the `ENTRYOK` lines.
4. `Tests.Compiler.FragCensusTest`, alone, last (imports `Tests.AllTests`;
   about 130 declarations × up to four kernel decisions): the `FRAGCENSUS`
   lines.

## 5. UNVERIFIED, in risk order

1. `Tools/ShippingEntryOkCommand.lean` — the largest blind piece: syntax
   quotations with spliced binders and terms (`∀ $x, …`, `($md).packed`,
   `(nDecl := $n)`, the two-alternative `first`), the closing by
   `apply f.closes_deep <;> exact (….ctx hRᵢ)`, `subst` under the generated
   `Or.elim`s, the reader `readMachine` as the classifier.
2. `step_of_none`: the goal after the two `split`s must be
   `translateCore … >>= fun r => match r with …` (as in the built
   `step_of_core`); `subst` then `exact hfb` relies on the `match` reducing.
3. `boolNot_still`: the literal `false` written as the `mkApp3 …` expression
   the built `boolNot_contract` uses; the IH at `.boolLit false` must have
   that type up to unfolding `quote` (the built contract relies on the same).
4. The `rw [….._step …]` argument orders (copied from the built contracts).
5. `harnessStill_all` / `entryStill_gate_all`: copies of built proofs; the
   open lists of the second namespace block.
6. The census: time (a large packed term gives `?`, not an error); the
   message-log save / restore around each `example`.

## 6. Open

* `MachineClosesAt mixDeep` at nested starts; `EntryOk mixDeep` (needs it).
* `EntryOk` for declarations on the legacy route, with memory call entries,
  or without reflected data.
* The sweep of `#entry_ok` beyond the family (not run in this round: the
  census says which declarations have a term; whether each has the data
  facts and a closing is what a wider sweep would measure).

## Integrator's build record (2026-10-13) — MEASURED

BUILT on poc 28adf9af + these files, cgrun 3 GiB swap 0; runs `backlog` (exit 0, peak 0.82 GB) and `backlog2`, worker's files unchanged, FIRST ATTEMPT (all five).
* `walk_still_all` (every constructor of `Term`): built. The walk has no fragment condition.
* `EntryOkFamilyTest`: `f.entry_ok` GENERATED for `rcH` (gate leaf, 1 premise), `cnt` (machine leaf, 1),
  `midH` (parent, 2), `mid2` (parent, 3; 3.7 s) — all reflections, statement check and axiom audit
  passed; the four `ENTRYOK SAME` lines are T (kernel isDefEq against the hand-written statements).
  `mixDeep`: FAILED as predicted (no all-worlds closing theorem) — the same open premise.
* `FragCensusTest` (AllTests environment, kernel-decided, 5 s): 129 declarations with a reflected term
  (126 machine: 88 without calls, 38 with; 3 gate); `wfrag` true 92, false 37, undecided 0. So 37
  declarations are reached only by `walk_still_all`. A row is about the walk's term condition, not about
  `EntryOk` of the declaration.
No endpoint changed; `mixDeep` stays OPEN.
