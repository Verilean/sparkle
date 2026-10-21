# EnvSnapshot: design of a minimal read-only `Core.State` model (unit SR2h)

Status words: PROVED / PREMISE / OPEN. File: `Tools/ShippingEnvSnapshot.lean` (built, s2 exit 0).

## 1. Which operations lie between w1 and w2 (and to w4)

| span | operations | env-relevant? |
|---|---|---|
| w1 → w2 | `Lean.getConstInfo n` = `getEnv >>= (find? ; throwUnknownConstant \| pure)` | one `ST.Ref.get` of the Core state; no write |
| w2 → w3 | `Lean.getEnv` | one `ST.Ref.get` |
| w3 → w4 (reference) | the whole `synthesizeFromConst … translate` body: Lean API calls (`whnf`, `inferType`, `mkAppM`, `unfoldDefinition?`, instance synthesis), callbacks, the SR refs | NOT modelled; see §3 |

Preservation form: `EnvFrame x := ∀ w a w', RunsTo x … w a w' → envAt cref w' = envAt cref w`.

## 2. What is PROVED

* `EnvFrame.pure`, `EnvFrame.bind` (law-free, on the real `RunsTo`).
* `envFrame_getConstInfo`: `GetEnvFrame → EnvFrame (getConstInfo n)`.
* `envSnapshot_of_getConstInfo`, `ci_in_envR_of_frame`: `EnvSnapshot cref w1 w2` follows from the `getConstInfo` run
  w1→w2 and `GetEnvFrame`. `EnvSnapshot` is no longer a hypothesis; it is replaced by the **single-primitive**
  premise `GetEnvFrame := EnvFrame getEnv` (PREMISE). This is not a wrapper: different statement, one operation,
  and the derivation (bind/pure/throw case) is proved.
* Pure model (`Model.St E`, `getEnvM`, `getRestM`, `modifyRestM`, `getConstM`): all preserve `env`
  (`getEnvM_frame`, `getRestM_frame`, `modifyRestM_frame`, `getConstM_frame`), closed under bind;
  `snapshot_model`; the writer `setEnvM` is not a frame (`setEnvM_not_frame`).

## 3. What is NOT shown (stated explicitly)

* **No correspondence with the real `ST.Ref` exists.** `ST.Ref.get` is `@[extern] opaque` and the world is the
  opaque `Void IO.RealWorld`: the kernel cannot see that `get r w` returns `w` (and `ST.Ref.get` could a priori
  return any world). Hence `GetEnvFrame` itself is NOT PROVED from the definitions here (no route found; not shown unprovable); the model `Model.*` is a
  different type and proves only the model analogue. To transfer it one needs a heap model of the runtime
  (`Void IO.RealWorld → St Environment` such that real `ST.Ref.get cref` is the model read), the same OPEN fit as
  `Tools/ShippingHeapModel.lean`, or the named law `GetEnvFrame` as a trust boundary.
* Nothing is shown about the body w3→w4 or the finalisation.

## 4. Real call paths that can change the environment (reviewable list)

No `addDecl`/`setEnv`/`modifyEnv`/`withEnv` in `Sparkle/Compiler` source (SR2g grep). Paths via Lean itself:

| path | can it change `Core.State.env`? | options |
|---|---|---|
| `whnf`, `whnfR/whnfD`, `inferType`, `isDefEq` | no env write FOUND in Lean's code (unverified; a candidate to confirm), but they use caches in `Meta.State`/`Core.State` fields other than `env`; `unfoldDefinition?` reads only | proof needs a model of Lean's Meta (not attempted; a large undertaking — not shown infeasible); or trust law "MetaM read-only API leaves `env`" (named, per call); or implementation change: wrap body in `withoutModifyingEnv`-style restore (changes the compiler; then the end-of-body env is restored, but snapshot over w1,w2 is unaffected) |
| `mkAppM`, `mkAppOptM` | no env write FOUND (unverified; a candidate to confirm); may instantiate mvars (Meta.State) | same trust law |
| instance synthesis (`synthInstance?`) | tabled resolution, cache in `Meta.State`; that no auxiliary decls are added is a CANDIDATE, unverified | same trust law |
| `unfoldDefinition?`, `Meta.reduceMatcher` | CANDIDATE, unverified: `reduceMatcher` follows `mkMatcherAuxDefinition`-free paths and matcher *creation* (`addDecl`) happens only at elaboration, not in these reductions | trust law; check by a bounded grep of called Lean entry points |
| `Lean.Elab` / `Term.elab*` if any callback elaborates | CAN `addDecl` (auxiliary lemmas, `_private` defs, `instance` caches) | implementation change (`withoutModifyingEnv` around callbacks) or exclude from the covered body |
| sparkle callbacks (`translate`, `childSynthEntry`, user `userInliner`) | `RefLawsAOps` does NOT imply that they write only the SR refs, nor that `Core.env` is preserved (it says nothing about `Core.State`); env-preservation not stated by any law | one option (a candidate, not established as the only one): a new named law `CoreEnvFrame` over `Core.State` (a trust boundary change, needs a ruling), not added here |
| `addDecl` (none present) | yes | would break the snapshot; absent in source |

For the demonstrated span w1→w2 only `getEnv` occurs, so the sole premise is `GetEnvFrame`. For w1→w4 the
list above is OPEN: each row is either a proof (needs a model of Lean's Meta API, not available), an
implementation change, or a named law; none is taken here.
