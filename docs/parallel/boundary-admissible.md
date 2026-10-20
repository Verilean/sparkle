# Admissible-context boundary for `RefLaws` (round par/bnd2, base aa35e8a6; revised par/bnd3, base 204e857f)

Status: DESIGN + Lean file `Tools/ShippingChildInvA.lean`: ba2 version BUILT (exit 0, ax4 standard);
revision par/bnd3 (quiet start-world premises, section (f)) BUILT (ba3 exit 0, ax7 standard).
No existing file changed (except `lakefile.lean` registration). No production
change, no new trusted law, no new field in `RefLaws`/`RefLawsCore`/`ChildLaws`.

Motivation (integrator finding, probe `Tests/Compiler/CanUnfoldProbe.lean`, run
cu2 exit 0): `RefLaws.frame`/`excOk`/... quantify over EVERY `Meta.Context`.
`Meta.Context.canUnfold?` is a caller-supplied `CoreM` callback that `whnf`
runs; at runtime a callback changed `sparkleSynthDepth` 0 -> 41 inside
`Framed.whnf` (case W), and an arbitrary lazy exception propagated out of
`whnf` (case E). Status:
* logical inconsistency of the old laws: NOT PROVEN (no proof either way);
* runtime counterexample REPRODUCED for `frame` over every context (probe case W);
* case E: propagation of an arbitrary lazy exception only (NOT a counterexample
  to `excOk`);
* case G (run cu3): the escaped message has an `ofGoal` node, hence is not in
  `OkMsg` by the kernel lemma `Tools.ShippingOkMsgGoal.not_okMsg_of_hasGoal`;
  this is NOT an unconditional `excOk` counterexample, since `excOk` asks
  `quiet w` of the start world and quietness was not checked in the probe.

## (a) Audit: context fields that are code or inject effects

Toolchain `~/.elan/toolchains/leanprover--lean4---v4.32.1/src/lean`.

| field | where | kind | effect on the three refs / exceptions |
|---|---|---|---|
| `Meta.Context.canUnfold? : Option (Config → ConstantInfo → CoreM Bool)` | `Lean/Meta/Basic.lean:504` (structure at 464) | **arbitrary CoreM code** | run by `canUnfold` (`Lean/Meta/GetUnfoldableConst.lean:30-35`) inside `whnf`, `unfoldDefinition?`, `whnfUntil`, `reduce`, `inferType` (via whnf), `isClass?`, `mkAppM`(defeq). Can do any IO: write the three refs, throw any exception. Set by `withCanUnfoldPred` (`Basic.lean:1172`). **The only code-valued field.** |
| `Core.Context.cancelTk? : Option IO.CancelToken` | `Lean/CoreM.lean:238` | a ref (read only by `checkInterrupted`) | cannot write the three refs; can make Core ops throw the interrupt exception (`Exception.internal`). Whether that is `OkExc` is NOT checked here (open item O-cancel). |
| `Core.Context.options` / `maxHeartbeats` / `maxRecDepth` / `diag` / `inheritedTraceOptions` | `CoreM.lean:222,224,229,236,245` | data | change WHICH errors are thrown (heartbeat / max-rec-depth errors, built from text) and whether traces are collected; traces go into `Core.State.traceState`, not stdout, so no printing during the run. No ref writes. Exception class: text messages; assumed in `OkMsg` by the existing `excOk` story (unchanged by this round). |
| `Core.Context.fileName/fileMap/ref/currNamespace/openDecls/quotContext/currMacroScope/initHeartbeats/currRecDepth/suppressElabErrors` | `CoreM.lean:219-243` | data | none |
| `Meta.Context.keyedConfig/trackZetaDelta/zetaDeltaSet/lctx/localInstances/defEqCtx?/synthPendingDepth/univApprox/inTypeClassResolution/cacheInferType` | `Basic.lean:465-520` | data | none (`localInstances` steer instance search, which runs only environment code — covered by the existing `OkEnv` assumption, unchanged) |

Conclusion: the context-borne injection point is `canUnfold?` (plus the
cancel token, which only affects the exception class).

## (b) Admissible contexts

```
InertUnfold quiet f :=   -- predicate on the callback, NOT assumed
  ∀ cfg info cctx cref w, quiet w →
    let r := f cfg info cctx cref w
    cv/sv/dv (end r) = cv/sv/dv w ∧ quiet (end r) ∧ (r = .error e _ → OkExc e)
AdmCtx quiet mctx cctx := ∀ f, mctx.canUnfold? = some f → InertUnfold quiet f
```
`admCtx_none : mctx.canUnfold? = none → AdmCtx quiet mctx cctx` (proved).
`cctx` is a parameter only (nothing required of it now; see O-cancel).

Context transformations the compile performs (grep of `Sparkle/`):
* `Sparkle/Compiler/Elab.lean`: `withLocalDecl` 14, `withLocalDeclD` 1,
  `withLetDecl` 3, `forallTelescopeReducing` 7, `lambdaTelescope` 3,
  `withTransparency` 13 (e.g. 548, 700, 5936, 6254, 6300, 6314, 6365, 6856,
  6861, 7386, 7686, 7715, 7729), `withReader` 2 (127, 133 — these are on the
  `CompilerM` reader `dimVarMap`/`varMap`, NOT the Meta context).
* `Sparkle/Core/SignalLeavesDerive.lean` `forallTelescopeReducing` 2,
  `Sparkle/Verification/Equivalence.lean` 1.
* NO `withCanUnfoldPred`, `withConfig`, `withLCtx`, `withNewMCtxDepth` in
  `Sparkle/` (grep).

Each of these changes `lctx`, `localInstances`, `keyedConfig` (transparency)
or (via `withIncRecDepth`) `Core.Context.currRecDepth`, and never
`canUnfold?`. So AdmCtx is preserved; in Lean this is `rfl` on the
`canUnfold?` projection: proved lemmas `admCtx_lctx`, `admCtx_localInsts`,
`admCtx_lctx_insts`, `admCtx_config`, `admCtx_cctx` (any `cctx'`). The
library combinators' internal context updates (telescope internals) are NOT
proved here: that they use only such record updates is a reading of the
library (`withNewLocalInstances`, `withReader (fun ctx => {ctx with lctx…})`),
recorded as a fact to be carried by the restricted `telescope`-family laws
below (their continuations are asked only in admissible contexts with the
SAME `canUnfold?`).

## (c) Provenance of local refs

Currently `Framed.localMk/localGet/localSet/localModify/…IO`
(`ShippingChildInv.lean:235-255`) and `exprCacheGet/exprCacheGetIO/exprCacheModify`
(233-237, 256) accept ANY `r : IO.Ref (ExprStructMap String)`. Non-aliasing
with the three tracked refs is argued by type only (`LocalRefType`,
line 98: only `ExprStructMap String`, different from the three refs' types).
Type distinctness is a runtime fact that does not survive `unsafeCast`; a
caller-supplied ref of that type could also be shared with another component.

Design: `FramedA Fresh p` — a copy of `Framed` whose ref-taking local/exprCache
constructors require `Fresh σ r`, a provenance predicate on the ref (intended
meaning: `r` was returned by an `IO.mkRef` executed inside this run, i.e. by
`Framed.localMk`/`mkExprCache`). All other constructors are copied verbatim.
`FramedA.toFramed : FramedA Fresh p → Framed p` (proved, by cases), so every
law about `Framed` restricts to `FramedA`.

Threading a proof of `Fresh`: the call sites that create local refs are the
entry's translation cache (`mkExprCache`, used by the harness/walk:
`Tools/ShippingChildHarness.lean`, `ShippingWalkStill.lean` (4 hits of
`exprCache`), `ShippingHarnessStill.lean`, `ShippingChildLegacy.lean`,
`ShippingLegacySem{Shim,Inline,Contract}.lean`, `ShippingCacheSoundness.lean`).
The `vc` proof step at the bind `let r ← IO.mkRef v; k r` would introduce
`Fresh _ r` as a hypothesis for the continuation (a world-indexed version:
`FreshIn w r` := `r` not reachable in `w`'s tracked cells — needs a heap
model statement; OPEN). Only `localSet` is used outside `ShippingChildInv`
(`ShippingChildLegacy.lean:125`, in a comment).

## (d) Consumers of the context-universal fields

Per-file counts (grep, Tools/*.lean):
* `L.frame` / `L.frameQ`: `ShippingChildInv.lean:739,745` (`RefLaws.same*`),
  `ShippingChildKeeps.lean:182-183`, `ShippingChildBalance.lean:132-133`,
  `ShippingChildBndCore.lean:251,254`. Needs: AdmCtx at the point + `FramedA`.
* `L.excOk`: `ShippingChildKeeps.lean:205,225,246`,
  `ShippingChildBalance.lean:152,164,178`, `ShippingChildBndCore.lean:250`.
  Needs AdmCtx.
* `L.telescope/lamTelescope/localDecl/letDecl`: `ShippingChildVC.lean:130,138,197,205`,
  `ShippingChildBndCore.lean:257-260`. Needs AdmCtx of the outer context; in
  return the continuation is asked only for admissible `mctx'` (implied by the same
  `canUnfold?` as an admissible outer one) — a strictly WEAKER obligation on the consumer.
* `L.same` (derived from frame): CacheCoherent{Cert 3, Close 2, Run 2, Via 5, Outer 3},
  CallsRunFinal 1, CallsRunG 1, ChildInv 2, ChildRun 4, ChildKeeps 2, CallsSame 1,
  HarnessStill 1, MemClosesRun 1, WalkStill 1, WalkGrow 1.
  `L.sameQ`: CacheCoherentOuter 2, ChildInv 1, ChildRun 2, ChildKeeps 1, CacheCoherentVia 2.
  `L.sameD`: CacheCoherentVia 2, CacheCoherentOuter 1, ChildInv 1, ChildRun 1,
  HarnessStill 2, GateParentRun 1. Each needs AdmCtx at the point (threaded
  from the entry's start context) and `FramedA` instead of `Framed`.
* `Framed.` constructor uses: CacheCoherentOuter 3, CacheCoherentVia 3,
  ChildBalance 6, ChildRun 3, ChildKeeps 15, ChildLegacy 1, GateParentRuns 5,
  HarnessStill 6, ChildBndCore 4, HeapModel 2, ChildHarness 7, LegacySemMemo 1,
  WalkStill 5, WalkStillMore 2: rename to `FramedA.` (+ `Fresh` proof for
  local/exprCache constructors).
* `RefLaws` mentioned in ~90 Tools files (types of hypotheses `L : RefLaws …`);
  these change only by carrying `AdmCtx` in `Keeps`/`KeepsC`/`ChildKeeps`
  (the `∀ mctx cctx` inside `KeepsC`, `ShippingChildInv.lean:601`, and in
  `ChildKeeps:609` become `∀ mctx cctx, AdmCtx … →`).

Conditions NOT derivable now:
1. AdmCtx of the entry's START context: the command elaborator's
   `Meta.Context` has `canUnfold? = none` by default (`Basic.lean:504`
   default `none`), but connecting the shipping entry to the command's
   initial context is not formalised (premise at the top).
2. `Fresh` for exprCache refs (heap-model provenance; OPEN).
3. That `forallTelescopeReducing`/`lambdaTelescope`/`withLocalDeclD`/
   `withLetDecl` run their continuation in a context with the same
   `canUnfold?` — a library-reading fact folded into the restricted laws
   (the laws remain laws; this round does not prove them).
4. O-cancel: the interrupt exception's class under `OkExc`.

## (e) Coverage change

Theorems under `RefLawsA` cover runs from admissible contexts AND quiet start
worlds only. Runs from a context with a non-inert `canUnfold?` callback are NOT
covered — the old `frame` was false of such a run (probe cu2, case W); for
`excOk` see the case-E status above. This corrects
an over-broad assumption; it is not a production guard, adds no trusted law,
refuses nothing.

Relation old/new (`RefLawsCore.toA`): the restricted non-continuation fields
(`diag frameT excOk frameQ cacheSetQ depthSetQ frame cacheSet depthSet`) follow
from the old ones by dropping the AdmCtx and `quiet w` hypotheses and
`FramedA.toFramed` (`toAOps`, proved).
The continuation fields (`telescope` …) in `RefLawsA` ask LESS of the
continuation (only admissible `mctx'`), so they
are NOT implied by the old fields; `toA` therefore takes them as separate
arguments (`RefLawsATele`) and the doc does not claim old ⇒ new for them:
the continuation laws are a different assumption, not derived.

## Lean (`Tools/ShippingChildInvA.lean`; ba2 BUILT, par/bnd3 revision BUILT ba3)

`InertUnfold`, `AdmCtx`, `admCtx_none`, `admCtx_lctx/localInsts/lctx_insts/config/cctx`,
`FramedA` (+ `FramedA.toFramed`), `RefLawsAOps` (non-continuation fields),
`RefLawsATele` (continuation fields), `RefLawsA := ⟨ops, tele⟩`,
`RefLawsCore.toAOps` (old ⇒ new, proved), `RefLawsCore.toA` (needs a
`RefLawsATele`), `RefLawsATele.telescope_old` (new continuation law ⇒ old at
admissible contexts), consumers re-derived: `RefLawsAOps.cacheModify'`,
`RefLawsAOps.depthModify'`. `excOk` keeps `Op` (its `framed` case on old
`Framed`): local-ref ops do not throw, provenance is irrelevant there.

## (f) Revision par/bnd3: the start world must be quiet (reviewer finding P1)

Finding: `InertUnfold quiet f` only asks the callback to be safe FROM quiet
worlds and `AdmCtx` is only that, but the ba2 `frame`/`frameT`/`cacheSet`/
`depthSet` and the telescope family's `Keeps` held at ALL worlds. At
`quiet := fun _ => False` every callback is `InertUnfold`
(`admCtx_quietFalse`, also at the context carrying the case-W writer,
`admCtx_quietFalse_writer`), so the ba2 `frame` again claimed the frame of
`whnf` under the writing callback (`OldFrameA`, `oldFrame_covers_writer`).
Adding `AdmCtx` alone was not a repair.

Revision (quiet is NOT fixed to True/False; it stays a field):
* `frame`, `frameT`, `cacheSet`, `depthSet` now take `quiet w →` (start
  world); `diag`, `excOk`, `frameQ`, `cacheSetQ`, `depthSetQ` already did.
  `frameT`'s conclusion is now `frame ∧ quiet (endW …)` (was `quiet w → …`).
  Reason: the callback is only known safe from quiet worlds.
* telescope family: an extra premise `(∀ w, I w → quiet w)`; `Keeps` starts
  from an `I` world, hence a quiet one. Continuations asked only in
  admissible contexts (unchanged).
* audit (BUILT ba3): `RefLawsAOps.quietFalse` (the whole operations
  bundle at `quiet = False` is inhabited by `False.elim`), `RefLawsATele.quietFalse`,
  `frame_quietFalse_vacuous` — at `quiet = False` the laws have no
  consequences; the vacuity now sits in the start condition `quiet w`.
* consumers: `RefLawsAOps.cacheModify'`/`depthModify'` take `hq : O.quiet w`
  (the intermediate world's quietness from `frameQ`); `OutQ quiet w :=
  quiet w ∧ sv w = some synthesizeChild ∧ dv w = 0`, `outQ_end`, `keeps_outQ`
  (`Keeps (OutQ O.quiet) p` for `FramedA Fresh p` in an admissible context):
  the quiet premise is supplied by the invariant. Two-step bind: not done
  (`Keeps.bind` is in `ShippingChildVC`, not imported).
* `toAOps` (old ⇒ new) still holds, with the added premises unused.

## Vertical migration (1 path) (round par/vert, base 777630e9; WRITTEN, NOT BUILT at writing time)

Files: `Tools/ShippingChildFresh.lean`, `Tools/ShippingChildVCA.lean`,
`Tools/ShippingChildVertA.lean`, audit `Tests/Compiler/ChildVertAuditTest.lean`
(not in AllTests).

**Law witness**: `O : RefLawsAOps MkRefd mref cref` and `hA : AdmCtx O.quiet mctx cctx`
only. No `RefLaws`, no `RefLawsCore`, no `RefLawsCore.toAOps`/`toA`, no
`RefLawsATele` (the path has no telescope). The audit test walks the
transitive constant closure of each audited theorem and throws if one of
these appears (positive control: the closure of `toAOps` does contain
`RefLawsCore`).

**`Fresh` has meaning**: `MkRefd σ r` := `r` was returned by a run of
`IO.mkRef v` (MetaM, or lifted from IO) in some contexts from some world. It
is not `fun _ _ => True`. Proved law-free: `runsTo_mkRef_bind` /
`runsTo_mkRefIO_bind` (the continuation of `x ← IO.mkRef v; k x` runs on a
ref with `MkRefd`). Under the laws: `tripleA_mkExprCache` /
`keepsA_mkExprCache_bind` (the allocation is `FramedA.mkExprCache`; the
continuation need keep the invariant only for `MkRefd` refs),
`keepsA_exprCacheGet` (a read of such a ref: `O.frame` at
`FramedA.exprCacheGet r hr`, `hr` discharged by the threading). That an
`MkRefd` ref is not one of the three tracked refs is NOT proved: it is what
`O.frame` states at `FramedA MkRefd (.localSet …/.exprCacheModify …)`, a
law of the new boundary. No law field was added.

**Migrated (theorems, modulo the premises below)**:

* `core_tripleA`: the core entry `synthesizeCombinationalCore declName [] false`
  from `OutQ O.quiet` ends in `OutQ O.quiet` on every outcome, exceptions
  in the class. Steps: profile read (`FramedA.ioEnv`), profile log
  (`O.diag`), depth read (value = depth, `runsTo_get_readOf`), depth guard
  (`O.frameT`, `O.excOk`), saved maps, 4 resets, cache clear (`O.cacheSet`,
  `O.cacheSetQ`), 7 resets, bump to 1 (`O.depthSet`, `O.depthSetQ`),
  `getConstInfo`/`getEnv`, the body, the `finally` (`finA`:
  `RefLawsAOps.depthModify'` + `O.frameQ`/`O.depthSetQ`, back to 0). The
  invariant is `JQ q D` = quiet ∧ synthesis ref = `some synthesizeChild` ∧
  depth = `D` (no cache half; the old `J L D` carries `CacheInv`, which is
  stated over `RefLaws`).
* `certified_keepsA`: the `IO.mkRef` sub-path `synthesizeCertified`
  (reached from `synthesizeFromConst`'s certified branch) keeps any
  `StableA` invariant through the fresh fvars, the distinctness branch and
  the cache allocation, handing the rest a ref with `MkRefd`.

**Stays a hypothesis (unproven)**:

* `hbody` of `core_tripleA`: the body `synthesizeFromConst …` keeps `JQ O.quiet 1`
  (the old route proves its analogue from `bodyRel`/`childKeeps` under
  `RefLaws`; nothing of the body is migrated);
* `hrest` of `certified_keepsA`: the translation run and `finishSynth` keep the
  invariant for `MkRefd` refs; the link `synthesizeFromConst → synthesizeCertified`
  (so that `certified_keepsA` discharges part of `hbody`) is not made;
* the start condition of the entry: `OutQ O.quiet w` (in particular
  `O.quiet w`) and `AdmCtx O.quiet mctx cctx` of the entry's contexts — the
  callback of the command's Meta context is not shown inert;
* the runtime fit of `RefLawsAOps MkRefd` itself (joint satisfiability,
  and the non-alias content of `frame` at `MkRefd` refs): not shown; every
  result may be vacuous for a model without such a witness (cf. the
  `quiet = False` audit above, which makes the conclusions vacuous, not
  false).

**Next steps to widen**: (1) migrate the body: `synthesizeFromConst`'s
dispatch, connecting the certified branch to `certified_keepsA` and the
legacy branch's `IO.mkRef` (Elab.lean:5377) the same way; (2) the child
entry (`synthesizeChild`, memoised) under `JQ` plus a cache half not stated
over `RefLaws`; (3) the telescope sites via `RefLawsATele` (lambda/forall
telescopes in the legacy body); (4) `CompilerM` lifts of the local-ref ops
inside the translation run (`exprCache*` from `CompilerM`), so that `hrest`
becomes a theorem; (5) discharge `AdmCtx` at the command's context
(`canUnfold? = none` for `#synthesizeVerilog`'s `MetaM` run, `admCtx_none`).
