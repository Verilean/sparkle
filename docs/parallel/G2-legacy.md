# G2 — semantic preservation of the legacy (fallback) route: worker B note

Branch `par/g2-legacy`, based on `9a9f812f`. Files added:
`Tools/ShippingLegacySemCalc.lean`, `Tools/ShippingLegacySemInline.lean`,
`Tools/ShippingLegacySemContract.lean`, this note.

**Verification status (integrator, 2026-10-12):** the three modules were built
through the protected queue at snapshot `ffad8424` + these files, first try, no
change: `Tools.ShippingLegacySemCalc`, `…Inline`, `…Contract`.
`returns_tryCatch`, `tryInlineUnfold_returns`, `translateFallback_legacy`,
`legacy_translate_contract` depend on `propext`, `Classical.choice`,
`Quot.sound` only. What that does NOT give: `ReachesInline` is an undischarged
premise (false as stated for cacheable calls while the expression cache is
unvalidated, §2), so no real fallback declaration is covered end to end. The
suspected defect of §2 is NOT reproduced yet (no run).

## 1. Where the fallback is, exactly

Two different fallbacks exist, at two levels.

**(E) Entry level** — `synthesizeFromConst` (`Sparkle/Compiler/Elab.lean`).
Order: `certifiedShape?` → `mixedCertifiedShape?` → `machineShape?` +
`synthesizeMachineCertified` → otherwise the legacy arm (`match constInfo
with | .defnInfo …`): memo read of `sparkleSubModuleCache`,
`openRecordInputs`, `stripMemoizeWrappers`, `lambdaTelescope`,
`splitReturnLeaves`, a fresh `IO.Ref` expression cache, then
`bindInputsLegacy … (emitLeaves translate …)` and `finishSynth`. The entry
reaches it when (i) no gate reads the constant (also after `entryConst`'s
unfolding), or (ii) `machineShape?` reads it but `closeLets` /
`closeInsts(G)M` returns `none`.

Real declarations that succeed there (from the tests; code path by reading the
source, not by a run):

| Declaration | Test | Why not the machine route |
|---|---|---|
| `useCtr1`, `useCtr1Twice`, `mid1`, `useMid1` | `ShippingCloseInstsCheckTest` | shape read, `closeInstsM` returns `none` (`kidsCombB` false: one-output SEQUENTIAL child) — case (ii) |
| `callerK` | `ShippingCallsCloseTest` | `machineShape?` is `none` (zero-argument call) — case (i) |
| data shape `let0 := x + x; let1 := let0` | `ShippingReflectCtxTest` | `closeLets` refuses — case (ii) |
| `uShadow`, `uDeep` | `ShippingInlineSoundnessTest` (`checkLeftAlone`) | no gate accepts (a helper the front end may not unfold / the unfolding exceeds the node budget) — case (i) |

**(T) Translator level** — `translateStep = translateStepWith
translateFallback`. `translateCore` first; else `translateFallback`, which
dispatches on `fallbackKind`: fourteen certified arms, and for `.other`
`translateInstanceOrFallback`: a tagged call takes the instance arms, anything
else goes to `Rec.translateExprToWireCached` (the caching shim) and from there
to `Rec.translateExprToWireImpl` (the legacy body: its own inline arms, then
`Rec.translateExprToWireApp`'s chain `handleCircuitMonad`,
`handleTupleProjections`, `handleApplicative`, `handleBitVecOps`,
`handleRegister`, `handleMux`, `handleMemory`, `handleLoop`,
`handleDefinitionUnfold`). (T) is taken on BOTH entry routes: a machine-route
transition whose field is not a certified shape goes through it as well.

`uDeep` (`dbl (dbl (… a))`, `dbl x := x + x` untagged) is the smallest real
success that is legacy at both levels: leaf `dbl X` → core declines →
`fallbackKind = .other` → not tagged → shim (a miss: the leaf call is
`named`) → body → handler chain → `handleDefinitionUnfold` →
`Rec.tryInlineUnfold` → `unfoldDefinition?` gives `X + X` → the certified
binary arm, whose two operands are `X` again: the first goes back through the
legacy inline arm, the second is a HIT of the shim's `IO.Ref` cache ("the
legacy translator shares the operand through its cache", the test's comment).

## 2. The contract

Template: `Contract rec ctx inputs we mems initial e v`
(`Tools/ShippingUnifiedRecursion.lean`) — for every hint and flag, every
successful run (`Returns`) of `rec e …` from `s` to `t` returning `w`:
`Frame s t`; and from `Inv … s prior` with `ScalarWidthsAgree we t`,
`Outcome … prior s t w v` (an environment at `t` satisfying `Inv`, `w ↦ v`,
earlier wires unchanged).

A legacy arm has to prove THAT statement for `translateStepWith
translateFallback rec` on its expressions, from `Contract rec` on the
sub-expressions it translates. Then it is a case of the same induction as the
certified arms. In Lean (`Tools/ShippingLegacySemContract.lean`):

* `RecSound Dom rec …` / `fuel_of_step` / `translate_of_step` — the fuel
  induction for any domain closed under one step;
* `LegacySem Dom …` — the statement for the whole body
  `Rec.translateExprToWireImpl`, relative to `rec` (the semantic analogue of
  `LegacyRel`). Stated, not proved;
* `LegacyArm rec … e v` — one constructor per handler; `translateFallback_legacy`
  is the ONE theorem about `translateFallback` with one case per constructor;
* `LegacyDom ctx inputs e v` and `legacy_fuel_contract` /
  `legacy_translate_contract` — input binders, every certified operator
  (`cert`, over arbitrary leaves, through `fuel_contract_leaves`) and legacy
  arms nested in any order, one induction on the derivation, conclusion
  `Contract (translateExprToWire …) … e v`.

### What the template cannot express (finding)

`Returns` quantifies the Meta context and the WORLD existentially. A handler
whose result is a wire NAME read from an `IO.Ref` therefore has no provable
`Returns`-contract: some world holds anything in the ref. The certified arms
avoid this by validating a hit against the pure builder state
(`cacheLookupValidated` compares `translateRecord[w]` with the requested
expression). The legacy route does not:

| Cache (IO.Ref) | Read by | Validated against the builder state? |
|---|---|---|
| `ctx.exprCache` | `Rec.translateExprToWireCached` (every `.other` expression that is cacheable) | NO |
| `sparkleLetWireCache` | the `.letE` arm (emits `alias := w`) | NO |
| `sparkleLoopWireCache` | `handleLoop` (returns `w`) | NO |
| `sparkleSingleOutInstanceCache` | `handleDefinitionUnfold` (returns `w`) | NO |
| `sparkleSubInstanceOutputs` | `handleDefinitionUnfold` (projection, multi-output) | partly (`alreadyDeclared` on one path) |

So the legacy contract needs one of: (a) every such hit validated against the
pure state, like the certified one — then the existing `Records` invariant and
`cached_action` apply and nothing new is trusted; (b) a world invariant per
cache ("every entry names a wire that is in use and carries the entry's
value") with value laws for those refs in the style of `RefLaws` — new trusted
laws, and a contract restated over `RunsTo` instead of `Returns`.

### Suspected defect behind the finding (NOT reproduced — no Lean run)

`try … catch` in `CompilerM` restores the builder state (`StateT`:
`returns_tryCatch` proves the handler runs from the state the `try` started
in) but not the `IO.Ref`s. `Rec.tryInlineUnfold`'s first attempt translates
the unfolded body; every sub-translation that succeeded has inserted
`expr ↦ wire` into `ctx.exprCache` (and `sparkleLetWireCache`, …). If the
attempt then throws, the wires are gone from the module and their names are
free again (`usedNames` and `counter` are rolled back), but the heap entries
stay. The retry, or the sub-module synthesis that follows a failed attempt and
translates the call's arguments, can then HIT such an entry and get a name
that is undeclared in the module or — because the counter was rolled back —
has since been allocated to a different wire. The source comments say the
inline path "fails-then-recovers thousands of times" on wide FSMs, so the
path is not exotic. A regression test to write: `f (g x)` with `g` an untagged
helper (legacy kind), `f` a helper whose inlining fails after its argument was
translated and whose sub-module synthesis succeeds; check that the instance's
connection for `g x` names a wire declared and driven by `g x`. If the hit is
real this is a miscompile of the legacy route, independent of G2's proof.

## 3. What is proved (to be built)

`Tools/ShippingLegacySemCalc.lean`
* `returns_tryCatch : Returns (tryCatch x h) ctx s a t → Returns x ctx s a t ∨ ∃ ex, Returns (h ex) ctx s a t`
  — the missing inversion for `catch`; SAME start state `s` on both sides.
* `Ensures c ctx s Q` and its rules (`pure`, `bindRun`, `bindLift`, `ite`,
  `tryCatch`): a goal-directed way to walk a handler.

`Tools/ShippingLegacySemInline.lean`
* `tryInlineUnfold_returns` — for every successful run of the real
  `Rec.tryInlineUnfold tr e hint named` from `s` to `t` returning `(some w, _)`:
  `∃ e', InlineUnfolds e e' ∧ Returns (tr e' hint false named) ctx s w t`.
  `InlineUnfolds e e'` = the attempt's own test `(e' != e) = true` and `e'` is
  a result (`MReturns`) of `unfoldOnce e` or `unfoldOnceReducible e`, the
  attempt's two oracles.

`Tools/ShippingLegacySemContract.lean`
* `step_eq_fallback`, `translateFallback_legacy`, `legacy_step_contract`,
  `fuel_of_step`, `translate_of_step`, `legacy_fuel_contract`,
  `legacy_translate_contract` (§2).

## 4. Premises that remain

1. `ReachesInline rec ctx e` — the dispatch from `translateFallback` to the
   inline attempt returns the attempt's wire, same start and end state. Open;
   and with `ctx.exprCache = some _` (always, at the entry) FALSE-AS-STATED
   for a cacheable call unless the shim's hit is validated (§2). It is
   provable in principle for `named = true` / `top = true` calls and for
   `exprCache = none`, by a walk of `translateInstanceOrFallback`, the shim,
   the body's prefix and the handler chain (every earlier handler returning
   `none` on the shape). That walk is not written: it is long, and its
   handlers before `handleDefinitionUnfold` have to be shown to decline.
2. `NotCore e` — two syntactic facts, `rfl` per shape.
3. For every `e'` with `InlineUnfolds e e'`: `LegacyDom … e' v`, i.e. the
   unfolding has the SAME value `v`. On the source side this is Lean's δ/β
   unfolding in the run's environment: reflection (audit §3.1 kind), a
   premise by design; it is quantified over every unfolding ANY run may
   return (`MReturns` hides the environment), which is stronger than one
   run needs.
4. `Meaning` of a certified node's leaves (asked by `cert`): the certified
   arms record what they lower and read records back through `Meaning`,
   which has no unfolding constructor. A legacy expression UNDER a certified
   node therefore needs a `Meaning` (today only `Meaning.inst` through
   `ChildSem` can give one to a call).
5. `Inv` at the start, `ScalarWidthsAgree` at the end — the contract's own.

## 5. Requested changes (not made: only new files were allowed)

* **lakefile**: three `lean_lib` entries (`Tools.ShippingLegacySemCalc`,
  `…Inline`, `…Contract`), like the other `Tools.Shipping*` modules.
* **Compiler, the shim** (`Rec.translateExprToWireCached`, and the same for
  the let / loop / single-output-instance caches): honour a hit only when the
  pure state records the wire for this expression — i.e. use
  `cacheLookupValidated` + `recordTranslation` (`translateControlCachedWith`)
  instead of the raw `IO.Ref` read. Accepts exactly the same sources (a
  refused hit is a miss and re-lowers); the text may differ where a stale or
  overwritten entry was honoured before. Detail to settle: the body can
  return an EXISTING wire (wrappers, `fvar` zeta), and `Frame`'s
  `RecordFresh` forbids re-recording a used wire, so record only a fresh
  result (cf. `cached_action` asks `FreshAction`).
* **`Meaning`** (`Tools/ShippingUnifiedMeaning.lean`): either a constructor
  for the unfolding step, or `Records` / `Inv` / `Contract` parametrised by
  the meaning relation (they use only its determinism). Removes premise 4.
* **Contract over contexts**: `Contract` fixes `ctx` and `inputs`. Handlers
  that bind (`withVarMapping` under `Signal.map` lambdas, `.letE`) call `rec`
  under an extended context and valuation; their arms need `RecSound`
  quantified over `ctx` and `inputs`.

## 6. Build order and spots that may not elaborate

Order: `Tools.ShippingLegacySemCalc` → `Tools.ShippingLegacySemInline` →
`Tools.ShippingLegacySemContract` (each imports the previous; the first
imports `Tools.ShippingUnifiedRecursion`).

* Calc, `RetPost.tryCatch`: copied step for step from `Triple.tryCatchQ`
  (`Tools/ShippingChildVC.lean`) with the error clause `True`; the two
  `change`s are the fragile lines.
* Calc, `returns_tryCatch`: the ascription `T` relies on the same definitional
  unfolding of `tryCatch` through `ReaderT` / `StateT` as `KeepsC.tryCatch`.
* Inline, `tryInlineUnfold_ensures`: `Or.inl hU1` / `Or.inr hU2` need the
  oracle blocks inside `Rec.tryInlineUnfold` to be definitionally
  `unfoldOnce e` / `unfoldOnceReducible e` (same source text, re-elaborated
  here). If that fails, restate `unfoldOnce*` or take the blocks from the
  goal.
* Contract, `step_eq_fallback`: `simp [translateStepWith, shape, core] <;> rfl`
  generalises `instance_step`'s two lines from one expression to any.
* Contract, the three `induction` / `cases` alternatives' field names.

## 7. Next steps, in order

1. Build; fix §6.
2. Decide the cache question (§2, §5) — it gates everything else: without it
   no `Returns`-contract exists for any `.other` expression that is cacheable.
   Write the regression test of §2 first; it decides whether this is a proof
   obstacle only or a bug.
3. With validated hits: walk the dispatch to discharge `ReachesInline`
   (shim: `cached_action`; body prefix: oracles only; chain: each handler
   `none` on a plain call of an untagged definition).
4. Further arms as further `LegacyArm` constructors, smallest first: the
   wrappers (`Signal.mk` / `OfNat.mk` payload), `fvar` zeta, the applicative
   `normSpine` re-entry, then `handleMux` (`uShadow`).
5. Entry level (E): the legacy arm of `synthesizeFromConst` has no
   counterpart of `ships_design_*` at all; `lambdaTelescope` /
   `splitReturnLeaves` / `bindInputsLegacy` have to produce `Inv` at the
   start and read the outputs off `emitLeaves`.

## 8. The reproduction test

`Tests/Compiler/LegacyCacheRollbackTest.lean`. It never throws; it logs.

**A guard I had missed in §2.** `instLinkCheck` (`Elab.lean`, before every
`emitInstance` of the legacy handler) refuses an instance one of whose
connections is not a declared wire or input of the parent with the port's
width. So in the SUB-MODULE recovery path a stale argument wire that is
undeclared in the rolled-back module is not emitted: the compile is REJECTED
("a connected wire's width differs from the port's width"). That path
miscompiles only if the stale name has been re-allocated, at the same width,
before the instance is emitted. The RETRY path has no such guard: the
unfolding is lowered by the certified binary arm, which reads its operand
wires without looking at their declarations.

**Method.** The real entry (`synthesizeCombinationalCoreWith`, legacy front
end) with the real step `translateStepWith translateFallback`, tied by
`translateFuelFix` like `translateExprToWire`, every recursive call through
`inject`: a one-shot fault at the inline attempt's own translation call,
raised `before` it (clean failure), `after` it (the attempt's
sub-translations are in the cache), or not at all. The fault is INJECTED; it
stands for any exception late in an inline attempt. I did not find, by
reading, a source whose attempt fails late by itself AND recovers (a failure
in the unfolded body also fails the sub-module synthesis of the same body;
the retry translates the same unfolding). The plausible natural trigger is a
helper that only compiles as a module because the entry preprocesses a module
body (`stripMemoizeWrappers`, `openRecordInputs`) and not an inlined one — the
"circular zeta-reduction" failure of FSM bodies; the test's second block
measures two natural candidates (`natDeep`, `natCtr`) and reports whether any
recursive translation failed and was recovered from.

**Scenarios and what my reading of the allocator predicts** (names from
`freshTemporary`: `_tmp_{hint}_{counter}`, counter rolled back by the catch):

| Scenario | Source | Predicted `after` run |
|---|---|---|
| retry, argument twice | `helperFR (helperG x)`, `helperFR y := y + y` reducible | `_gen_out := _tmp_op_a_0 + _tmp_op_a_0`, `_tmp_op_a_0` neither declared nor driven: malformed module, emitted |
| retry, later operand | `helperFK (helperG x) + (x + x)`, `helperFK y := 3 + y` reducible | the stale name `_tmp_op_b_2` (was `helperG x`) is re-allocated to `x + x`: module well formed, computes `(3 + 2x) + 2x` instead of `(3 + (x + 1)) + 2x` — a SILENT miscompile, caught only by the evaluation |
| sub-module after a failed inline | `helperF (helperG x)`, `helperF` not reducible | rejected by `instLinkCheck` |

The checks: declared / driven / driven-once over statements and instance
connections (an instance drives what is connected to its module's output
ports), and the port `out` evaluated with `Sparkle.IR.Semantics.evalAssigns`
(iterated to a fixpoint) against the source function at x = 0, 1, 5, 200.
Verdict lines: `STALE HIT REPRODUCED: …`, `STALE HIT REPRODUCED, CAUGHT AS A
REJECTION: …`, `no stale hit: …`, `FAULT NOT REACHED` (my reading of the
dispatch is wrong), `INCONCLUSIVE` (a control is not clean).

Only `ctx.exprCache` is exercised. `sparkleLetWireCache` /
`sparkleLoopWireCache` / `sparkleSingleOutInstanceCache` have the same shape
(a name read from an `IO.Ref`, state rolled back by the catch) and are not
tested here.

## 9. Proposal: validate the legacy hits (NOT applied)

### 9.1 The shim (`Elab.lean` 7854–7889, `Rec.translateExprToWireCached`)

Move `cacheLookupValidated` (7910–7921) and `recordTranslation` (7925–7931)
above `section TranslatorBlock` (5569); they use only `CompilerM` and
`ExprDecEq`. Replace the body of the shim by

```lean
def translateExprToWireCached (e : Lean.Expr) (hint : String := "wire")
    (isTopLevel : Bool := false) (isNamed : Bool := false) : CompilerM String := do
  let cacheable := !isNamed && !e.isFVar && !isTopLevel
  if cacheable then
    if let some w ← cacheLookupValidated e then
      CompilerM.liftMetaM (sparkleCacheHits.modify (· + 1))
      return w
  let s0 ← get
  let r ← translateExprToWireImpl (fun e h t n => translateExprToWire e h t n) e hint isTopLevel isNamed
  -- record (and cache) only a wire this call made: a result that is an
  -- existing wire (a bound variable's, a wrapper's payload) keeps its record
  if !s0.usedNames.contains r then recordTranslation e r cacheable
  return r
```

Changes against today: the hit is honoured only if the pure state records
the wire for THIS expression (`translateRecord[w] = e`, decided by
`ExprDecEq`); the second lookup under `e.consumeMData` is dropped; the
insert goes through `recordTranslation` (pure record always, `IO.Ref` when
cacheable). `emitLeaves`' own insert (2174) needs no change: the leaf's wire
was recorded by the shim when it was fresh.

**Accepted sources.** A validated hit returns what today's hit returns. Where
today hits and the new code misses, the new code runs the body — the same
call today's code makes on a miss. Three kinds of new miss: (a) a stale entry
after a rollback (today's defect); (b) an `mdata`-stripped key; (c) an
expression whose first lowering returned an existing wire (not recorded). In
(b) and (c) the expression was lowered successfully once in an earlier state
of the same module, and is lowered again. That the second lowering succeeds
is NOT a theorem (the translation-call limit is the one state-dependent
failure I know of); it has to be confirmed by the corpus diff. If exactly
today's hit set minus (a) is wanted, make the record multi-valued instead
(`translateRecord : HashMap String (List Expr)`, a hit valid when the list
contains `e`): then (c) hits as today, at the price of restating `Records` /
`RecordFresh` over lists. The emitted text can differ in (b)/(c) (duplicated
hardware); for the legacy route that is a new difference and needs
`compare_outputs.py`.

**Lemmas that then apply, unchanged:** `cacheLookupValidated_returns`,
`recordTranslation_returns`, `validated_hit` / `hit_outcome` (the hit's
`Outcome` from `Inv.records`), `Records.insert` / `record_preserves`,
`Frame.record_new` (the result is fresh), `cached_widths_outcome`. One new
inversion lemma replaces `legacyShim_returns`: a run of the new shim is a
validated hit, or the body's run followed by `recordTranslation` on a fresh
wire, or the body's run alone. With it `ShimAt` holds for EVERY call
(`Tools/ShippingLegacySemDispatch.lean`), so `ReachesAt` and
`inline_step_contract_at` need no cacheability premise. `legacyRel`'s proof
of the shim is by `vc` and should go through (`cacheLookupValidated` and
`recordTranslation` are already walked for the certified arms).

### 9.2 The three name caches

`sparkleLetWireCache` (read 7745, written 7774), `sparkleLoopWireCache`
(read 6064, written 6087; also 1276), `sparkleSingleOutInstanceCache` (read
6549, written 6554; `instArmCacheGet/Put` 8359/8363) are keyed by a
canonical hash, not by the expression, so `translateRecord` cannot validate
them. Proposal: make them fields of `CircuitState`
(`Sparkle/IR/Builder.lean`) instead of global `IO.Ref`s. They are per-module
already (the entry clears them on every nested synthesis, 5471–5487), so the
lifetime is the same; a `catch` then rolls them back together with the wires
they name, and they become visible to `Returns`. `sparkleSubInstanceOutputs`
deliberately persists across nested syntheses and re-declares its wires in
the new parent (`alreadyDeclared`), so it stays an `IO.Ref`; its remaining
unvalidated read is the projection shortcut (6364), which should get the
same `alreadyDeclared` test.

## 10. The dispatch, in stages

`Tools/ShippingLegacySemDispatch.lean`: `ReachesAt rec ctx e hint top named`
(per call: the inline attempt's wire, or a validated hit `t = s ∧
translateRecord[w] = e`), `inline_at_action`, `inline_step_contract_at`
(the contract from `ReachesAt`, hit included, with `Meaning e v` for the
hit), and the stages: `fallback_eq_arm`, `arm_to_shim` (proved),
`ShimAt` and `BodyReachesInline` (premises), `reachesAt_of_stages`.

`Tools/ShippingLegacySemShim.lean`: `legacyShim_returns` (today's shim is
the body's run or an unvalidated hit), hence `shimAt_of_uncacheable`,
`shimAt_of_noCache`, `reachesAt_uncacheable`, `reachesAt_noCache`.

NOT done: `BodyReachesInline`. Its walk needs, for a plain call, (i) the
body's prefix (`trace[…]`, the call counter, the limit, the profile tick —
oracles), (ii) every inline arm of `Rec.translateExprToWireImpl` before the
`match e with | .app ..` declining on the head's name, (iii) the
`hasMappedFvar` / `whnf` step (an oracle that may REPLACE `e`: the statement
needs "the expression has a mapped `fvar`", or a premise on the oracle),
(iv) `handleErrorPatterns` and the eight handlers before
`handleDefinitionUnfold` returning `none`, (v) `handleDefinitionUnfold`'s
own prefix. Each handler's "returns `none` on this head" is a name test in
its first lines, but they are nine separate programs; I did not write them
blind.

Spots that may not elaborate: `arm_to_shim`'s last step (the two-discriminant
`match` after the projection test is rewritten to `none`; three alternatives
are tried); all of `legacyShim_returns` (see the file's header); in the test,
nothing proof-like, but the `circuit do` candidate `ctrU` and the
`evalAssigns` call are the API uses I could not check.


## 11. Integrator's run of the reproduction test (2026-10-12)

`Tests/Compiler/LegacyCacheRollbackTest.lean` was run through the protected
queue (base `ffad8424` + the test). Verdicts, with the fault INJECTED at the
inline attempt's translation call (no source that fails late by itself was
found: `natural candidates: []`):

* retry, argument used twice (`parentRetry`): the emitted module reads
  `_tmp_op_a_0`, neither declared nor driven; `out = 0` for every input
  (source: `2 * (x + 1)`).
* retry, then a later operand (`parentRealloc`): the module is WELL FORMED
  and computes another function (`x = 5`: `out = 23`, source `19`): the
  stale name `_tmp_op_b_2` was re-allocated to `x + x`.
* sub-module after a failed inline (`parentSub`): rejected by
  `instLinkCheck`.

So the stale hit is real given a late failure of an inline attempt. Whether
any real source fails late is NOT established.
`Tools.ShippingLegacySemDispatch` failed its first build (returned to the
worker); `Tools.ShippingLegacySemShim` was not reached.
