# A: `CoreVia` as a theorem — round par/a-35

Base: `poc/roundtrip-proof` 11e3944b (par/a-34 BUILT and integrated).
Branch `par/a-35`. **NOTHING here was built or run**: WRITTEN, NOT BUILT.
"READ" = read at 11e3944b. No built file is modified. Predecessor:
`A-cache-coherence-3.md` (§3.2 named this unit).

## 0. Result

`CoreVia L c shape` — one of the three statements par/a-34 left — is now a
theorem, `coreVia_of`, from the two route premises the endpoints already
carry (`MachineDefines c shape` in every context, `MachineClosesAt c shape`
in every context) and `RefLaws` frame steps. It is instantiated for `midH`
(`Tests/Compiler/CoreViaMidHTest.lean`). `HarnessStill` / `EntryStill` are
NOT consequences of an existing law (§3): read and answered, not written.
Step (b) is not closed; `mixDeep` is not connected; no endpoint changes.

## 1. What is written — `Tools/ShippingCacheCoherentVia.lean`

```lean
theorem tryFinally_fin (h : RunsTo (tryFinally x fin) mctx mref cctx cref w a w') :
    ∃ w1 u, RunsTo x mctx mref cctx cref w a w1 ∧ RunsTo fin mctx mref cctx cref w1 u w'
theorem keeps_runs (hk : Keeps mctx mref cctx cref I m) (hw : I w)
    (h : RunsTo m mctx mref cctx cref w a w') : I w'

def InvM (L) (mb : Std.HashMap Name Res) (C Dp : Prop) (w) : Prop := InvC L C Dp w ∧ L.val w = mb
theorem invM_pure, invM_framed, invM_depthSet          -- InvM kept by one prefix step
theorem invM_depthModify (h : RunsTo (ST.Ref.modify sparkleSynthDepth f : MetaM Unit) … w u w')
    (hw : InvM L mb C Dp w) : InvM L mb C False w'
-- tactic `peel_val L h hw` (the text of `peel_inv` over these lemmas)

theorem core_reads_val (L) (hB : ∀ L', BodyRel L') (hw : InvV L w) (hdw : L.dval w ≠ 0)
    (h : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (M, D) w') :
    ∃ b envR ci w1 w2 w3 w4 w5 w6,
      RunsTo (getConstInfo declName) … w1 ci w2 ∧ RunsTo getEnv … w5 envR w6 ∧
      RunsTo (synthesizeFromConst … (profLogIO b) declName [] false true
        (entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR))
        (instancePredicate envR)) … w3 (M, D) w4 ∧
      InvV L w3 ∧ L.dval w3 ≠ 0 ∧ L.val w3 = L.val w ∧ InvV L w4 ∧ L.val w' = L.val w4

theorem sfc_machine_val (L) (old : certifiedShape? false [] ci = none)
    (miss : mixedCertifiedShape? false [] ci isInst = none) (hw : InvV L w)
    (hr : RunsTo (synthesizeFromConst … (profLogIO b) declName [] false true ci isInst) … w (m, d) w') :
    ∃ envR w5 w6, RunsTo getEnv … w5 envR w6 ∧
      ∀ shape, machineShape? false [] ci (structEnv envR) = some shape →
        ∃ r w7 w8, RunsTo (synthesizeMachineCertified … (profLogIO b) declName shape) … w7 r w8 ∧
          InvV L w7 ∧ L.dval w7 = L.dval w ∧ L.val w7 = L.val w ∧
          ∀ res, r = some res → L.quiet w8 → res = (m, d) ∧ L.val w' = L.val w8

theorem coreVia_of (L) (hB : ∀ L', BodyRel L') (hH : ∀ L', HarnessRel L')
    (entry : ∀ mctx cctx, MachineDefines mctx mref cctx cref c shape)
    (closes : ∀ mctx cctx, MachineClosesAt mctx mref cctx cref c shape) : CoreVia L c shape
```

READ behind each step (`Sparkle/Compiler/Elab.lean`):

| step of the core run | lines | law |
|---|---|---|
| `IO.getEnv`, the log line, the depth read | 5402–5431 | `Framed.ioEnv`, `Diag.profLog` (quiet start world), `Framed.depthGet` |
| the depth guard | 5432–5433 | a returning run did not throw |
| five saved reads (`if depth == 0 then pure … else ref.get`) | 5446–5492 | `Framed.sideGet` (the `else` branch: depth ≠ 0) |
| the nested resets (NO cache clear at depth ≠ 0) | 5506–5516 | `Framed.sideSet` |
| the depth bump | 5517 | `RefLaws.depthSet` |
| `getConstInfo`, `getEnv` | 5523–5524 | `Framed.constInfo`, `Framed.env` |
| the body `synthesizeFromConst` | 5525–5529 | `BodyRel` (BUILT `bodyRel`): `InvV` at its end |
| `finally`: depth release, six restores | 5532–5541 | `RefLaws.depthModify`, `Framed.sideSet` |
| machine arm: `getEnv`, `pure` | 5288–5292 | `Framed.env` |
| machine arm after a module: log, memo insert, `return` | 5297–5301 | `Diag.profLog` (quiet: `machine_keeps`), `Framed.sideModify` (`SideRef.subModule`) |

`coreVia_of` assembles them exactly as the BUILT
`Tools.ShippingChildInv.machine_run_of_core` does, with the four equations.

Instance — `Tests/Compiler/CoreViaMidHTest.lean` (target-only):

```lean
theorem midH_coreVia (L : RefLaws mref cref)
    (hRm : MachineDefines mctx mref cctx cref ``midH midH.machineData.shape)
    (hRr : EntryDefines mctx mref cctx cref ``rcH rcH.gateValue) :
    CoreVia L ``midH midH.machineData.shape
```

by `coreVia_of` with `MachineDefines.ctx hRm` and the BUILT
`midH.closes_deep (EntryDefines.ctx hRr)` — the two fields `entry` /
`closes` of the BUILT `Tests.Compiler.NoPortsGrandHTest.midH_kid`. `mid2`
goes the same way with `mid2.closes_deep` (its argument list is the one in
`Tests/Compiler/NoPortsTopD2Test.lean` 260–263; not written: that term is
behind a `first`, I could not read which alternative builds). The premises
are reflections every endpoint about `midH` already has; nothing is added to
an endpoint.

## 2. PROVED (written) vs. NOT shown

| statement | state |
|---|---|
| `tryFinally_fin`, `keeps_runs`, `invM_*`, `peel_val` | PROVED (written) |
| `core_reads_val`, `sfc_machine_val` | PROVED (written), from `RefLaws` + `BodyRel` |
| `coreVia_of` | PROVED (written), from `MachineDefines` + `MachineClosesAt` |
| `midH_coreVia` | PROVED (written), from the two reflections |
| `HarnessStill` (per transition), `EntryStill` (per leaf) | **NOT shown** — §3 |
| the depth-0 sibling of `core_reads_val` (after the clear the cache is `{}`) | NOT written (not needed for `CoreVia`; needed only by a depth-0 consumer) |

## 3. `HarnessStill` / `EntryStill`: is "the cache VALUE is unchanged" a consequence of a frame law plus "no `synthesizeChild` call in the body"?

**No — not with what exists. READ:**

1. The frame laws are per OPERATION: `RefLaws.frame`
   (`Tools/ShippingChildInv.lean` 386–388) for the operations listed in
   `Framed` (187–252), `RefLaws.diag` (352–355) for `Diag` in quiet worlds.
   There is no law about a PROGRAM. "The harness leaves the cache" is a
   statement about the translator's composition of such operations WITH
   calls of `childSynthEntry`.
2. The only built statements about that composition are the relative
   theorems `translateRel` / `legacyRel` / `harnessRel_of`
   (`ShippingChildLegacy.lean` 224, 234; `ShippingChildHarness.lean` 304):
   `ChildKeeps L D → Keeps (J L D) …`. Their conclusion is `J`; their
   hypothesis is about `synthesizeChild`, which DOES change the cache on a
   miss. Instantiated with the predicate "the cache is `mb`" the hypothesis
   is false and nothing follows; and `J` cannot hold that predicate anyway
   (`auxInsert`, par/a-34 §2).
3. "No `synthesizeChild` call in the body" is not a notion any law has, and
   it is not a syntactic property of the body. `childSynthEntry` is reached
   from the certified instance arms when the head is tagged in the run's
   environment (`Sparkle/Compiler/Elab.lean` 8674–8678, 8692–8696) AND from
   the legacy handler for an UNTAGGED helper whose inline attempt failed
   (6551–6553) — the probe's `cyc4` / `cyc5` are that case, measured (their
   `keys` hold the untagged helper). So "the body mentions no tagged
   constant" does not give it; what gives it is "the translator, on THIS
   body, never reaches those three sites".

**The smallest honest route** is therefore the certified walk itself, with
worlds. The transition bodies concerned are quoted terms
(`body = quote …`, the `hbody` of every `MachineData`); the built soundness
of the walk on them (`transition_facts`,
`Tools/ShippingMachineEntry.lean` 301–325, by induction on the term) shows
what is RETURNED, on `Returns` — it does not carry the world. The unit:

    walk_still: for a quoted term, a returning run of
      emitLeaves … [("out", instFVars … (quote …))] from a world with InvV
    ends in a world with the same L.val

by the SAME induction as `transition_facts`' core lemma, each case being a
certified arm made of `makeWire` / `emitAssign` / the expression cache /
`rec` on sub-terms — all `Framed` (the `*_tripleC` lemmas of
`ShippingChildHarness.lean` 115–183 list them) — and no instance arm
(`fallbackKind` of a quoted constructor is not `.other`: a fact per
constructor of the term language). Then `HarnessStill` is `walk_still` +
the harness shell (`mkFreshFVarId`, `IO.mkRef`, `bindMixedCertifiedInputs`,
`finishSynth`: the text of `harnessRel_of` with `InvM`). Size: that of the
walk's soundness induction, which I have not read in full; I did not write
it blind. `EntryStill` of a leaf machine is `core_reads_val` +
`sfc_machine_val` + `HarnessStill` of its transition (a leaf has no
closing); of a gate leaf (`rcH`) the same over `synthesizeCertified` / the
mixed arm (`synthesizeFromConst` 5270–5282: the harness, the memo insert,
`return`).

What does NOT help: the run-aware `auxInsert` of branch `par/a-35-aux`
(`docs/parallel/A-reflaws-aux.md`): "nothing was inserted" is a property of
one program, not an invariant.

## 4. Where `mixDeep` stands after this round

Blockers of `A-cache-coherence-3.md` §4: (1) `HarnessStill` ×3 and
`EntryStill` ×2 — OPEN, route in §3; (2) `CoreVia` for `mid2`, `midH` —
`midH` WRITTEN, `mid2` one term away; (3) the consumer's start world —
unchanged (a `Prov` start world; the endpoint's premise ranges over every
`InvW` world of positive depth).

## 5. Build queue (integrator)

`lakefile.lean` (not edited):

    lean_lib «Tools.ShippingCacheCoherentVia» where
      roots := #[`Tools.ShippingCacheCoherentVia]

`Tests/AllTests.lean`: nothing (the instance test is target-only; add
`import Tests.Compiler.CoreViaMidHTest` after its first build if wanted).

Order: (1) `Tools.ShippingCacheCoherentVia`; (2)
`Tests.Compiler.CoreViaMidHTest` (prints the axioms of `midH_coreVia`;
expected: standard).

## 6. UNVERIFIED, in risk order

1. `peel_val` / `stepLemmaV`: a `meta def` and an `elab` copied from
   `Tools/ShippingChildRun.lean` 99–125 into another namespace (the quoted
   lemma names must resolve there; `runHeadIs` comes from
   `Tools.ShippingEntrySoundness`).
2. `core_reads_val`, the `finally`: whether the block is still
   `modify >>= fun _ => if … then … else pure ()` after the proof's
   `simp only` (both shapes are tried: `first | (rcases RunsTo.ite …) | …`);
   the six restores peeled by `peel_val` and the last one by `invM_framed`'s
   default argument.
3. `core_reads_val`: `keeps_runs (hB L.plain _ … prof.isSome declName _ _) …
   h` — unification of the entry's logger closure with `profLogIO
   prof.isSome` (the BUILT `core_reads_inv` relies on the same definitional
   equality in its final `exact`).
4. `tryFinally_fin`: `rename_i u w3 hfin` after the second `split` (the
   built proof does not name them); `exact ⟨w2, u, hx, hfin⟩`.
5. `sfc_machine_val`: the suffix as two binds and a `pure` (the built proof
   peels two binds on `MReturns`); `.sideModify _ .subModule`.
6. `invM_depthModify`: the anonymous constructor of `InvC`.
7. `coreVia_of`: `machine_keeps (mctx := mctx) (cctx := cctx) L.plain …`.
8. `midH_coreVia`: the argument forms of `midH.closes_deep` and
   `MachineDefines.ctx` (copied from `midH_kid`, BUILT).

## Integrator's build record (2026-10-13)

BUILT on tree `dc390745332e67af98c627d66e608a55cbc12304` (poc 35208d70 + these files), cgrun 3 GiB swap 0, first attempt, worker's files
unchanged: `a35-via` (`Tools.ShippingCacheCoherentVia`, exit 0, peak 0.81 GB), `a35-test`
(`Tests.Compiler.CoreViaMidHTest`, target-only, exit 0, 0.32 GB; `midH_coreVia` depends on
`[propext, Classical.choice, Quot.sound]`).

STATE: `CoreVia` is a theorem (`coreVia_of`, from `MachineDefines` and `MachineClosesAt`), instantiated
for `midH`. `HarnessStill` and `EntryStill` are NOT derived (and do not follow from the existing frame
laws — reasons above). Step (b) not closed; no endpoint changed; `mixDeep` not connected.

The sibling branch `par/a-35-aux` (run-aware `RefLaws.auxInsert`, commit 8b266634) is NOT built and NOT
integrated: it changes the structure under `ChildBnd` and one audit (`lawAudit`), and by the worker's own
reading it does not unblock `mixDeep` without a derivation of own-key freshness. It waits for a ruling.
