# A: the certified walk with worlds — round par/a-36

Base: `poc/roundtrip-proof` 5693c63a (par/a-35 BUILT and integrated;
par/a-35-aux NOT built, waiting for a ruling — not extended here). Branch
`par/a-36`. **NOTHING here was built or run**: WRITTEN, NOT BUILT. "READ" =
read at 5693c63a. No built file is modified; `RefLaws` is untouched.

## 0. Result

`EntryStill` and `HarnessStill` are still NOT theorems. What is written is
their common CORE: a returning run of the shipping translator on the
quotation of a term leaves the child cache (`walk_still`), for a FRAGMENT of
the term language given by a `Bool` on terms (`wfrag`) and in a compiler
context that binds the input binders (`WBound`). It is the same induction as
the built soundness of the walk, re-done on worlds, using the built program
equalities to know which arm runs. What is missing between `walk_still` and
`HarnessStill` is the harness SHELL (§3) — ordinary code, not written. Also
written: `CoreVia` for `mid2`; the chain `rcH → midH` as terms with its
non-theorem hypotheses listed (§4). No endpoint is connected or narrowed.

## 1. The walk — READ in full this time

The built soundness is
`synthesizeMixedCertified_term_sound_at`
(`Tools/ShippingUnifiedExecutionSoundness.lean` 618–) →
`translateExprToWire_contract` → `fuel_contract` → `fuel_contract_leaves`
(`Tools/ShippingUnifiedRecursion.lean` 2187–2317): induction on the fuel,
cases on the term, one `…_contract` per constructor, each resting on a
PROGRAM EQUALITY that says which arm the step takes on the quoted node, and
on `Returns`-inversions of that arm. `Returns`
(`Tools/ShippingTranslateSoundness.lean` 57–61) hides the worlds — that is
why none of it speaks of the cache.

The translator's step (`Sparkle/Compiler/Elab.lean`):

| code | lines | what it does to the child cache |
|---|---|---|
| `translateStepWith` | 8215–8228 | validated lookup; `translateCore`; on `some w` the record; on `none` the FALLBACK |
| `translateCore` | 8196–8212 | `.fvar` → `lookupVar`; `Signal.pure` → `translateSignalPureLiteral?`; canonical operator → `translateCanonicalSignalBinary`; else `pure none` |
| `translateFallback` | 8783–8824 | by `fallbackKind` (8738–8779): a certified arm under `translateControlCachedWith`, or `.other` → `translateInstanceOrFallback` |
| `translateInstanceOrFallback` | 8671–8713 | **`childSynthEntry`** (8677–8678, 8695–8696) or the legacy block |
| `translateBoolUncachedWith` | 8141–8178 | certified Bool arms; three alternatives hand over to `legacy` (8159, 8164, 8178) |

The operations that occur on a quoted node, and why each leaves the cache
(each is now a lemma of `Tools/ShippingWalkStill.lean`):

| operation | code | lemma | reason |
|---|---|---|---|
| `CompilerM.makeWire` | `Tools/ShippingChildHarness.lean` 120–134 walks it | `makeWire_S` | builder state (`get`/`set`), and `sparkleWireWidthCache.modify` — `Framed.sideModify _ .wireWidth` (`SideRef.wireWidth`, `ShippingChildInv.lean` 68) |
| `CompilerM.emitAssign` | idem 160–166 | `emitAssign_S` | builder state only |
| `cacheLookupValidated` | Elab 8003–8014 | `cacheLookup_S` | the reader; the translation cache's read — `Framed.exprCacheGetIO` (a ref of type `ExprStructMap String`, not one of the three); the builder's record |
| `recordTranslation` | Elab 8018–8024 | `record_S` | builder state (`modify`); the translation cache's update — `Framed.exprCacheModify` |
| `CompilerM.lookupVar` | Elab 107–109 | in `input_still` | pure: the reader's `varMap` and the builder's `sourceBindings` |
| `translateControlCachedWith` | Elab 8046–8053 | `controlCached_S` | lookup, the uncached arm, record |
| `emitBoolResult` / `emitCastResult` / `emitMuxResult` | Elab 8063–8066, 8251–8255, 1378–1382 | `emitBool_S`, `emitCast_S`, `emitMux_S` | `makeWire`, `emitAssign` |
| `translateSignalCompare`, `translateBoolBinary` | Elab 8082–8086, 8074–8078 | `compare_arm`, `boolBin_arm` | `rec` on the two operands, `emitBoolResult` |
| `translateMuxWith` (result type `pure ty`) | Elab 1796–1803 | `mux_arm` | `rec` ×3, `pure`, `emitMuxResult` |
| `translateConcatWith` / `translateConcatActs` | Elab 8288–8300 | `concat_arm` | `makeWire`, `rec` ×2, `emitAssign` |
| `translateSetWidthUncachedWith` on `setwE` | Elab 8259–8262 | in `setw_still` | `rec`, `emitCastResult` |
| `translateSignalPureLiteral?` | Elab 1363–1370 | `core_literal` | `makeWire`, `emitAssign` |
| `translateCanonicalSignalBinary` (canonical width, both operands Signals) | Elab 1810–1838 | `core_binary` | `pure`, `makeWire`, `rec` ×2, `emitAssign` (the `cachedInferType` / `extractBitVecLiteral` branches are NOT taken: `canonicalSignalBitVecWidth = some n`, kinds `(true, true)`) |

No operation of the walk on a quoted node touches `sparkleChildCache`,
`sparkleChildSynth` or `sparkleSynthDepth`. What CAN touch the cache is not
an operation but two continuations — the `.other` arm and the `legacy`
hand-overs — and the fuel-0 throw is not a returning run. That a quoted node
never reaches them is exactly what the built program equalities say:

| constructor | equalities used (BUILT) |
|---|---|
| `compare` | `compare_step` (`ShippingMixedRecursion.lean` 290), `translateFallback_bool` (`ShippingBoolSourceSoundness.lean` 283), `translateBoolUncachedWith_compare` (`ShippingCompareLoweringSoundness.lean` 174) |
| `boolBinary` | `boolBin_step` (391), `translateFallback_bool`, `translateBoolUncachedWith_boolBin` (317) |
| `boolEq` | `boolEq_step` (426), `translateFallback_bool` |
| `mux` at `.bool` | `boolMux_step` (`ShippingBoolMuxSoundness.lean` 20), `translateFallback_bool` |
| `mux` at `.bits` | `vector_step`, `vectorMuxUncached_muxE` (`ShippingVectorMuxRecursion.lean` 203, 197) |
| `setw` | `setw_step`, `setwUncached_setwE` (`ShippingUnifiedRecursion.lean` 1080, 1065) |
| `concat` | `concat_step`, `concatUncached_concatE` (1613, 1603) |
| `binary`, `bitsLit`, inputs | no equality exists; the core is walked (`core_binary` with `op_checks`, `ShippingEntrySoundness.lean` 1260; `core_literal` as `bits_literal_recorded` 308–; `input_still`) and `step_of_core` shows the fallback is not reached because the core returned a wire |

## 2. What is written — `Tools/ShippingWalkStill.lean`

```lean
def WSI (L) (mb) (w) : Prop := InvV L w ∧ L.val w = mb
def WHo mctx cctx (L) (mb) (ctx : CompilerState) (c : CompilerM α) (Q : α → Prop) : Prop :=
  ∀ st w p w', WSI L mb w → RunsTo (c ctx st) mctx mref cctx cref w p w' → WSI L mb w' ∧ Q p.1
abbrev WSt mctx cctx L mb ctx c := WHo mctx cctx L mb ctx c (fun _ => True)
def WCh mctx cctx L mb ctx (rec : TranslateFn) (e : Lean.Expr) : Prop :=
  ∀ hint top named, WSt mctx cctx L mb ctx (rec e hint top named)

theorem WHo.pure, WHo.bind, WHo.lift, WHo.ofPure
theorem WSt.get, WSt.set, WSt.modify, WSt.getCompilerState, WSt.throw
theorem framedM (hp : Framed m) … : WSI L mb w' ∧ True
theorem wireWidth_S, makeWire_S, emitAssign_S, cacheLookup_S, record_S
theorem controlCached_S (hlower : WSt … (lower e hint top named)) :
    WSt … (translateControlCachedWith lower e hint top named)
theorem emitBool_S, emitCast_S, emitMux_S, compare_arm, boolBin_arm, mux_arm, concat_arm

theorem compare_still (ha : WCh … rec ae) (hb : WCh … rec be) :
    WCh … (translateStepWith translateFallback rec) (compareE le dom n ae be)
theorem boolBin_still, boolEq_still, boolMux_still, vector_still
theorem setw_still (hws : 0 < ws) (hwt : 0 < wt) (ha : WCh … rec ae) : WCh … (…) (setwE dom ws wt ae)
theorem concat_still (hm : 0 < m) (hn : 0 < n) (ha) (hb) : WCh … (…) (concatE dom m n ae be)

theorem step_of_core (hcore : WHo … (translateCore rec e hint top named) (fun r => r ≠ none)) :
    WSt … (translateStepWith fb rec e hint top named)
def WBound (ctx : CompilerState) (id : FVarId) : Prop :=
  ∀ st, (CircuitM.lookupSourceBinding (ctx.varMap.lookup id) id.name st).1 ≠ none
theorem wbound_of_lookup (h : ctx.varMap.lookup id = some wire) : WBound ctx id
theorem input_still (hb : WBound ctx id) : WCh … (translateStepWith translateFallback rec) (.fvar id)
theorem core_literal, bitsLit_still, core_binary

def wfrag : {s : SType} → Term s → Bool     -- inputs, bitsLit, binary, compare, boolBinary,
                                            -- boolEq, mux, setw, concat; `false` elsewhere
theorem fuel_still (fuel) (hbS : ∀ j, j < kb → ∀ fuel, WCh … (translateFuelFix translateStep fuel) (bE j))
    (hvS : …) : ∀ {s} (e : Term s), e.WF kb kv vw → wfrag e = true →
      WCh … (translateFuelFix translateStep fuel) (quote dom bE vE e)
theorem input_fuel (hb : WBound ctx id) : ∀ fuel, WCh … (translateFuelFix translateStep fuel) (.fvar id)
theorem walk_still (hb : ∀ j, j < kb → WBound ctx (bi j)) (hv : ∀ j, j < kv → WBound ctx (vi j))
    (e : Term s) (he : e.WF kb kv vw) (hf : wfrag e = true) :
    WCh mctx cctx L mb ctx (fun e hint top named => translateExprToWire e hint top named)
      (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) e)
```

Side conditions of `walk_still`, all decidable by reading / by `decide`:
`wfrag e` (a `Bool`), `e.WF` (the endpoints' `ok` already decides it,
`Tools/ShippingMachineAuto.lean` 228), `WBound` (the reader's map has the
binder: `wbound_of_lookup`). No hypothesis about runs.

NOT in the fragment (`wfrag = false`; nothing is claimed): `boolLit`,
`bitsNum`, `boolNot`, `slice`, `sliceF`, `zextMap`, `concatLitHi`,
`concatLitLo`, `appCompare`, `appBool`, `appBool2`. Each has its built
`…_step` equality (or, for the literals, the core / `translateFallback_bool`
route); adding one is one `…_still` lemma and one line of `wfrag` and of the
induction — not done to keep the first build small.

Instances — `Tests/Compiler/WalkStillFragTest.lean` (target-only): it LOGS
`wfrag cnt.machineData.packed` and `wfrag midH.machineData.packed`, then
proves them by `decide` and states `cnt_walk`, `midH_walk`. `rcH` is on the
GATE route (its body is not a `MachineData.packed`); it is not instantiated.

## 3. `HarnessStill` — is it literally the same theorem as `EntryStill`'s core? What is missing

Yes for the core: both come down to `walk_still` on the declaration's quoted
body. They differ in the shell:

* `HarnessStill L c bs body` = `walk_still` + the HARNESS SHELL
  (`synthesizeMixedCertified`, Elab 2956–2969): `mkFreshFVarId` ×n
  (`Framed.freshFVar`), `IO.mkRef` (`Framed.mkExprCache`),
  `bindMixedCertifiedInputs` (2947–2954: per binder `makeWire`, `addInput`,
  `withVarMapping` — Elab 128–131, which is what makes each binder
  `WBound`: the reader's `varMap` gets `(id, wire)` in front),
  `emitLeaves` (2154–2191: the clock and counters `Framed.monoMs` /
  `sideGet`, the logger `Diag.profLog`, the translator, the translation
  cache's update, `addOutput`, `emitAssign`), `finishSynth` (2215–2233:
  pure or a throw). Every operation is in the table of §1 or is the built
  `harnessRel_of`'s (`ShippingChildHarness.lean` 304–320). NOT written; the
  two non-trivial points are (i) `WBound` after the binder walk: the body is
  `instFVars ids body` and the leaves of the quotation are `.fvar ids[pos]`
  (`instantiated_quote`, `ShippingUnifiedExecutionSoundness.lean` 819), so
  "every id of `bs.zip ids` is in the reader's map inside the continuation"
  has to be carried through `bindMixedCertifiedInputs`; (ii) `emitLeaves`'s
  do-block (the built proof restates it verbatim, 237–261).
* `EntryStill L c` for a LEAF machine = `core_reads_val` + `sfc_machine_val`
  (BUILT, par/a-35) + `HarnessStill` of its transition + the machine
  synthesis with `shape.insts = []` (a `pure`): `closeLets` / `closeMachine`
  are pure. For a GATE leaf (`rcH`): the same shell under
  `synthesizeCertified` / the mixed arm of `synthesizeFromConst`
  (5270–5282), the entry's prefix and `finally` (`core_reads_val` covers
  them), and the body in the gate's quotation (`quoteDecl` / the mixed
  `Term`) — a second instance of the walk over the gate fragment's steps.

So after this round: `HarnessStill` (machine transitions in the fragment) =
`walk_still` + shell (i)+(ii); `EntryStill` (leaf machines) = that + two
built lemmas; `EntryStill` (gate leaves) = the shell + the gate arm.

## 4. The chain, as terms — `Tests/Compiler/CacheChainMidHTest.lean`

```lean
theorem mid2_coreVia (L) (hRm2 : MachineDefines … mid2 …) (hRm : MachineDefines … midH …)
    (hRr : EntryDefines … rcH rcH.gateValue) : CoreVia L ``mid2 mid2.machineData.shape
theorem rcH_entryOk (L) (K) (hRr) (hstillR : EntryStill L ``rcH) : EntryOk L ``rcH K
theorem midH_callees : ∀ x ∈ midH.machineData.shape.insts, x.1 = ``rcH
theorem midH_entryOk (L) (hRm) (hRr)
    (hstillH : HarnessStill L ``midH midH.machineData.shape.binders midH.machineData.shape.body)
    (hstillR : EntryStill L ``rcH) : EntryOk L ``midH (fun k => k = ``rcH)
```

`mid2.closes_deep`'s two arguments: the order cannot be read (the theorem is
generated; `NoPortsTopD2Test.lean` 260–267 itself tries both), so
`mid2_coreVia` uses the same `first`.

Hypotheses of `midH_entryOk` that are NOT theorems: `hstillH`, `hstillR`
(§3). `hRm`, `hRr` are the reflections every endpoint about `midH` carries.
Everything else is discharged in the term (`midH_coreVia`, `hout_of_data`
over the built `midH.machine_ok` / `machine_body` / `oneout_callsOk` /
`oneout_slotLen` / `oneout_domB`, the callees and the name condition by
`decide`, `rcH.gate_full`).

Where the chain STOPS, and why: `mid2` (needs `EntryOk` of `midH` — written
— plus `HarnessStill mid2` and `mid2`'s data facts by name) and the closing
of `mixDeep` (`machine_closes_of_entryOk` with `hS :=
machineClosesAtS_of_kids …`, `HarnessStill mixDeep`, `EntryOk` of `mid2`,
`midH`, `cnt`, and a `Prov` start world) are not written as terms: each
adds only hypotheses of the two kinds above and the start-world condition
of `A-cache-coherence-3.md` §4 item 3, which is unchanged.

## 5. PROVED (written) vs. NOT shown

| statement | state |
|---|---|
| the `WHo` logic; the operations of §1; the arms; `…_still` per constructor; `step_of_core`; `fuel_still`; `walk_still` | PROVED (written), from `RefLaws` frame laws and BUILT program equalities |
| `cnt_walk`, `midH_walk` | PROVED (written) IF the two `wfrag` Booleans are `true` (logged before they are decided) |
| `mid2_coreVia` | PROVED (written) |
| `rcH_entryOk`, `midH_entryOk` | PROVED (written) relative to `EntryStill rcH`, `HarnessStill midH` |
| the harness shell → `HarnessStill`; `EntryStill` (machine leaf; gate leaf) | **NOT shown** (§3) |
| the eleven constructors outside `wfrag` | **NOT shown** |
| `mixDeep` | not connected; blockers: the above, and the start world |

## 6. Build queue (integrator)

`lakefile.lean` (not edited):

    lean_lib «Tools.ShippingWalkStill» where
      roots := #[`Tools.ShippingWalkStill]

`Tests/AllTests.lean`: nothing (three target-only tests).

Order: (1) `Tools.ShippingWalkStill` (imports
`Tools.ShippingUnifiedRecursion`, `Tools.ShippingCacheCoherentVia`);
(2) `Tests.Compiler.WalkStillFragTest` — read the `WALKFRAG` lines first;
(3) `Tests.Compiler.CacheChainMidHTest` (imports
`Tests.Compiler.CoreViaMidHTest`, `NoPortsTopD2Test`,
`Tools.ShippingCacheCoherentData`); independent of (1)–(2).

## 7. UNVERIFIED, in risk order

1. `core_binary`: the `simp only` that reduces `translateCore`'s three-way
   `match` and `translateCanonicalSignalBinary`'s `if true = true` (no built
   proof does this on the GOAL; the built ones invert a `Returns`
   hypothesis). If it fails, `cnt` / `midH` are not covered (both use
   `binary`); everything else stands.
2. `step_of_core`: the shape of the step after `unfold` / `dsimp only`
   (taken from the built proofs' `split at hr` sequence), the `unless`
   branch (two shapes tried by `first`).
3. `WHo.bind` / `WHo.lift`: `RunsTo.bind` on a `CompilerM` bind applied to
   the reader and the state — the unification `TripleC.bind` /
   `TripleC.lift` (BUILT) rely on, here in a tactic.
4. `WHo.ofPure` instances (`rfl` for `get` / `set` / `modify` /
   `getCompilerState` / `lookupVar` against `pure (a, s)`).
5. `controlCached_S`: `exact rest` against the unfolded wrapper (the join
   point after `dsimp only`).
6. `cacheLookup_S`, `record_S`: the order of the `match` alternatives; the
   lifted cache read as `bind … pure`.
7. The `…_still` lemmas: `rw` with the built equalities on a `WSt` goal (the
   built proofs do the same `rw` inside `ActionSpec`); `show` after
   `apply controlCached_S` (as their `change`).
8. `fuel_still`: `simp only [wfrag, Bool.and_eq_true] at hf`; the wildcard
   alternative `| _ => simp [wfrag] at hf`; the name clashes of the `open`
   list copied from `ShippingUnifiedRecursion.lean` plus
   `Tools.ShippingChildInv`.
9. `WalkStillFragTest`: whether the two Booleans are `true`; `decide` on
   `wfrag` / `WF` of reflected data.
10. `CacheChainMidHTest`: the `first` on `mid2.closes_deep`; `decide` on the
    callees in membership form; `rcH.gate_full hRr hy`'s result as a
    `ChildFull` whose `iface` has the name and the empty design.

## Integrator's build record (2026-10-13)

BUILT on tree `ea0a615a23f5c425081ec7f9c5fd1c111c030d89` (poc 4103e86f + these files), cgrun 3 GiB swap 0.
* `a36-walk`: `Tools.ShippingWalkStill` exit 1, four errors of one kind (`WHo.pure L _ trivial` with the
  postcondition not inferable, lines 320, 427, 439, 518). Integrator fixes: `(Q := fun _ => True)` at the
  four sites (`a36-walk2`: two left); at the two record sites the goal is an `if e.isFVar`, so `split`
  first, then `WHo.pure` / `WHo.bind … (record_S …)`. `a36-walk3`: the file builds (peak 0.40 GB). No
  statement changed. `core_binary`, the risk the worker ranked first, built as written.
* `a36-chain`: `CacheChainMidHTest` exit 0 first attempt; `mid2_coreVia`, `rcH_entryOk`, `midH_entryOk`
  each on `[propext, Classical.choice, Quot.sound]`.
* `a36-walk3` / `a36-frag`: `WalkStillFragTest` — its logging `run_cmd` crashed Lean's code generator
  ("unknown join point 'block_0'", ExplicitBoxing panic) while compiling the evaluation of
  `wfrag ….packed`; replaced by two kernel-decided `example`s. `cnt_walk`, `midH_walk` on standard axioms;
  both `wfrag` Booleans are `true` by kernel `decide`.

STATE: `walk_still` (the translator on a quoted term of the fragment leaves the child-cache value) is a
theorem and holds for the packed bodies of `cnt` and `midH`. `HarnessStill` / `EntryStill` are NOT
theorems: the harness shell is not written. `midH_entryOk` still has those two as hypotheses. Step (b)
not closed; no endpoint changed; `mixDeep` not connected.
