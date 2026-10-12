# G2 — worker B, round 10 (branch `par/cachefix-proofs`, from `fix/cache-rollback`)

A separate file on purpose: `docs/parallel/G2-legacy.md` on this branch stops
at round 3 (the fix branch does not carry §14–§28 of the main branch's copy),
so appending there would conflict at the merge. To be folded in as §29–§31 of
the main copy.

Nothing in this round was built (no Lean run from a worker).

## 29. The proofs for the patched `Rec.tryInlineUnfold`

The patch adds one action before the first `try` (`snapshotWireCaches`) and
one at the head of each `catch` (`restoreWireCaches saved`).

**RefLaws cells, re-checked from the definitions** (`Tools/ShippingChildInv.lean`):

| restored ref | covered by |
|---|---|
| the context's `exprCache` | `LocalRefType.exprCache` (line 97) → `Framed.localGetIO` / `localSetIO` |
| `sparkleLetWireCache` | `SideRef.letWire` |
| `sparkleLoopWireCache` | `SideRef.loopWire` |
| `sparkleWireCanon` | `SideRef.wireCanon` |
| `sparkleSingleOutInstanceCache` | `SideRef.singleOut` |
| `sparkleSubInstanceOutputs` | `SideRef.subInstOut` |
| `sparkleWireWidthCache` | `SideRef.wireWidth` |
| `sparkleFvarValueMap` | `SideRef.fvarValue` |
| `sparkleFvarZetaVisited` | `SideRef.fvarZetaVisited` (line 83) |

All eight globals have a `SideRef` constructor; **no shared-definition change
is needed**. None of the three tracked cells (`sparkleChildCache`,
`sparkleChildSynth`, `sparkleSynthDepth`) is read or written by the patch.

**Edited** (allowed this round):

* `Tools/ShippingChildLegacy.lean` — `snapshotWireCaches_keepsC`,
  `restoreWireCaches_keepsC` (both `@[keeps]`, by `vc`), and the script of
  `tryInlineUnfold_tripleC` with three more `TripleC.bind` steps. The
  statement is unchanged, so `vc`'s use of it is unchanged.
* `Tools/ShippingLegacySemInline.lean` — now imports
  `Tools.ShippingLegacySemTrace` (for `Ensures.lift_frame`); new
  `Ensures.read_frame`, `Ensures.bindFrame`, the tactic `frame_walk`,
  `snapshotWireCaches_frame`, `restoreWireCaches_frame`; the walk of
  `tryInlineUnfold_ensures` with the three new steps. Statements of
  `tryInlineUnfold_ensures` / `_returns` unchanged.
* `Tools/ShippingLegacySemUnfold.lean` — the walk of
  `tryInlineUnfold_none_frame`, same three steps.

**Import check (done by reading)**: `ShippingLegacySemTrace` imports only
`ShippingLegacySemCalc`, so the new import in `…Inline` is not a cycle.

**Spots that may not elaborate**

1. the two `vc` lemmas: `vc` has to see through `snapshotWireCaches`'s
   `match c.exprCache with` and `restoreWireCaches`'s two-discriminant match.
   If it stops there: `unfold` first, then `vc`.
2. `frame_walk` was written against the EXPECTED shape of the two actions.
   `restoreWireCaches`'s match is followed by more code, so it is probably a
   join point (`have __do_jp := …; match …`); `try dsimp only` is there to
   inline it. If `split` picks the wrong `match`, the fallback is one
   `Ensures.bindFrame` per line, by hand.
3. in `tryInlineUnfold_tripleC`, the name of the keeps lemmas' explicit
   arguments (`L D`) — taken from the neighbouring lemmas' use.

## 30. `Tests/Compiler/LegacyCacheFixCostTest.lean`

Logs only, never throws. Per declaration (17: `uRoot` … `uDeep`,
`nodeFilterTop`, `oddParityTop`, `useCtr1`, `useCtr1Twice`, `useMid1`,
`hftByte`, `plainSig`):

* `DIGEST` — the shipping entry's result: hash of the pretty-printed top
  module, statement / wire counts, number of modules, hash of all modules.
  Byte-comparable between the main branch and the fix branch.
* `PROBE default front end` / `PROBE legacy front end` — the compile through
  the real step with a probe around every recursive call: number of inline
  attempts (= snapshots on the fix branch) and the sum / maximum of the sizes
  of the context's expression cache and of the eight global maps at that
  moment.

Limits, stated in the file: the probe recognises an attempt as "this call's
expression is `unfoldDefinition?` of the enclosing call's expression"; the
retry's unfolding under default transparency is the same test, the reducible
first unfolding is NOT separately recognised (it is counted only when it
coincides with the default one — an undercount is possible). The
declarations are small; the quadratic risk is in large FSMs, not measured
(the corpus stays stopped). A missing name is reported as `MISSING`.

## 31. The entry-level statement (`Tools/ShippingLegacySemEntry.lean`)

The certified entry's proof (`synthesizeMixedCertified_term_sound_at`) uses
the quoted fragment at exactly two places: the leaf's `Contract` and the
leaf's `ActionOrder`. Everything else (`emitLeaves_from_ports`,
`emitLeaves_postReady_at`, the binder walk, the finish) is about an
arbitrary leaf. The file states the connection on that basis.

| Hypothesis | Meaning | Status |
|---|---|---|
| `HarnessSound` | the certified harness on ANY leaf with a `Contract` and an `ActionOrder` gives `RawValueAt` | provable-now (the existing proof with two hypotheses in place of two lemma uses); not proved in this file |
| `LegacyEntryReduces` | a successful legacy-arm run of `synthesizeFromConst` is a harness run on `leafOf ids`, finished the same way | needs-walk + oracle premises (`lambdaTelescope`, `getDecl`, `isSignalBinderType`, `inferHWTypeFromSignal`, `splitReturnLeaves`; the memo read of `sparkleSubModuleCache`) |
| the leaf's `LegacyDom` | the leaf is in the combined domain at `v` | per declaration; for `useDbl`: `dbl_call_step_closed`'s premises (`PlainHead`, `HasMappedFVar` — kernel-opaque —, `NoSubModule`, the unfolding's membership) |
| the leaf's `ActionOrder` | the leaf's translation keeps `OrderInv` | needs-proof: exists for the quoted fragment only; a legacy analogue of `legacy_translate_contract` for the order invariant is not written |
| `0 < v.kind.width` | — | provable-now per declaration |

Proved (two short compositions): `legacy_leaf_output`, `legacy_entry_output`.

Two things this statement does NOT hide:

* `LegacyEntryReduces` has the legal-name fact in its conclusion; it is the
  entry's own check on the certified side and has to be found (or added as a
  premise) on the legacy side.
* A legacy entry with record inputs, several return leaves, parameters or a
  sequential body is outside this statement (`bs`, one leaf `out`, no
  clock/reset) — a statement for those needs definitions that do not exist
  (needs-definition): the source meaning of a record input and of several
  outputs at the entry.
