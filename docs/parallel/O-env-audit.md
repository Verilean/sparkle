# Environment writes on the synthesis path (reviewer 2026-10-19, item 2)

Integrator, 2026-10-19, poc af07d484. SOURCE REVIEW (grep + reading), not a proof.

## Direct writes in `Sparkle/`

`grep modifyEnv|addDecl|setEnv|withEnvironment|withoutModifyingEnv|addAndCompile|restoreState|saveState Sparkle/`:
ONE hit, `Sparkle/Verification/Equivalence.lean:347 setEnv savedEnv` — a verification command, not on the
synthesis path. No `evalExpr`/`evalConst` on the path (`Elab.lean:725` mentions `evalExpr` in a comment only;
`inferResetKindFromSignal` uses `whnf`). `Elab.lean:9285 evalStringArrayImpl` (`Meta.evalExpr`, which adds and
compiles an auxiliary definition under `withoutModifyingEnv`) belongs to a simulation command, not to
`synthesizeCombinationalCoreWith`. No `getEqnsFor?` / `getUnfoldEqnFor?` / `realizeConst` / `mkAuxDefinition`.

## Library calls on the path

`whnf` / `whnfR` / `whnfD`, `inferType`, `isDefEq`, `instantiateMVars`, `forallTelescope(Reducing)`,
`lambdaTelescope` (97 call sites in Elab.lean), `getConstInfo`, `getEnv`, `withLocalDecl`, `try … catch`
(MetaM `tryCatch`: no state restore). By source review of Lean v4.32.1 these read the environment and write
only `Meta.State` caches / the metavariable context — but this is NOT established here (no lemma about them).

Recursive child synthesis (`synthesizeChild` → the whole entry again for the callee, Elab ~8929), the child
cache (`sparkleChildCache`, ~1031), the depth ref, `closeLets` / `closeInstsGM` (pure), harness translation:
none writes the environment in Sparkle source.

## Can the existing laws entail preservation? No.

`RefLaws` (Tools/ShippingChildInv.lean 333) speaks of three tracked refs (`val`, `sval`, `dval`), quietness,
exceptions, and continuation combinators. No field mentions `Core.State.env`, and `getEnv` /
`ST.Ref.get` are opaque primitives with no equation. Counterexample: take any model of `RefLaws` and change
it so that every `Framed` operation also replaces the environment held in `cref` (e.g. by one with a different
`userStructure?` at some name); every field of `RefLaws` still holds (none reads the environment), yet a
`getEnv` before and after such an operation returns different environments. So `EnvAt`-style agreement between
the parent's read and a later child read is NOT derivable from the current laws.

## Minimal missing primitive (specification only; NOT added to RefLaws, NOT approved)

1. `envGet`: a `getEnv` run from world `w` returns `envOf w` (as `cacheGet` does for the cache);
2. `envFrame`: every operation on the path between the parent reader's `getEnv` and a child's `getConstInfo`
   leaves `envOf` unchanged — the `Framed` operations, the cache/depth ref writes, the continuation combinators
   (telescopes, `withLocalDecl`), and recursively the child synthesis (by the same induction as `ChildKeeps`).

Call sites it would serve: the parent's `getEnv` in `synthesizeCombinationalCoreWith` (the `structEnv` the
reader uses), the child's `getConstInfo` / `getEnv` in its entry run (`entryConst`, `MachineDefines`), and every
operation of `synthesizeMachineCertified` / `closeInstsGM` before the child's run. With (1)+(2), `getConstInfo_find`
gives the run-local DR/FA facts. Without them, the run-local variants (worker O-ENVL) carry the needed
equalities as premises about the WITNESSED reads only.
