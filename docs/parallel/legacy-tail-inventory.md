# Inventory: the legacy tail of `synthesizeFromConst` (Sparkle/Compiler/Elab.lean:5288–5399)

Unit B3. Status words: PROVED / PREMISE / OPEN. Entry: `synthesizeFromConst translate (profLogIO b)
declName [] false false ci isInst` (`parameters = []`, `symbolicMode = false`, `certifiedFrontEnd = false`).

Key observation (recorded before the proof): with `certifiedFrontEnd = false` the certified gate, the
mixed gate AND the machine route (`machine? := if certifiedFrontEnd && … then … else pure none`) are all
skipped by `ite` on a literal `false`. So the tail needs no gate hypothesis (it holds for every constant),
and the machine-route functions (`machineShape?`, `synthesizeMachineCertified`, `closeInstsM`) are NOT run in it;
they belong to the `certifiedFrontEnd = true` entry (FrontCP `fromConst_machine_keepsAP`, already proved).
The tail's only recursion is `translate`; there is no `synthesizeChild` call, hence no `ChildSynthA` hypothesis.

| step | primitive | covering lemma | status |
|---|---|---|---|
| gates, machine route | `ite` on literal `false`; `pure none` binds | `simp only` + `keeps_pure_bind_of` | PROVED |
| memo read | `sparkleSubModuleCache.get` | `FramedA.sideGet .subModule` via `keepsA_framed` (vca) | PROVED |
| memo hit | `logProf`, `pure cached` | `Diag.profLog` (`keepsA_diag`) | PROVED |
| `getConstInfo done` log, `defnInfo` log, `monoMsNow` | `Diag.profLog`, `FramedA.monoMs` | vca | PROVED |
| non-definition arm | `throwError "Cannot synthesize …"` | `keepsA_throwError` (`OkMsg`) | PROVED |
| `openRecordInputs` | `inferType`, `forallTelescopeReducing` (**T-usage**: `T.telescope`), `whnf`, `getConstInfoInduct/Ctor` (try/catch), `instantiateForall`, `Array.allM` over fields (`whnf`/`inferType`), `mkLambdaFVars`, pure `replaceFVarId`, the structural-fuel `walk` | `openRecordInputs_walk_keeps` (induction on fuel), `openRecordInputs_keeps`, `keepsA_getConstInfoInduct/Ctor` (ProjFieldA), `Keeps.allMA` (new, law-free) | PROVED given T |
| `stripMemoizeWrappers` | pure (`partial def`, no monad) | none needed: it is not in `MetaM` (a value) | PROVED (nothing to prove) |
| `lambdaTelescope` | `T.lamTelescope` (**T-usage**) | `keepsA_lambdaTelescope` (WalkA) | PROVED given T |
| `symbolicMode` block | `ite` on literal `false` (`foundNatBinder` loop, `whnf`) | `simp only` | PROVED (dead branch) |
| `splitReturnLeaves` | `fuelFixM2` over `splitReturnLeavesStep`: `inferType`, `whnf`, `mkAppM`, `getConstInfoInduct/Ctor`, `forallTelescopeReducing` (**T-usage**), `getUserName`, `lambdaTelescope` (**T-usage**) + `mkLambdaFVars`, `Array.mapM`, `try/catch` | `splitReturnLeavesStep_keeps`, `splitReturnLeaves_keeps` (`fuelFixM2_keepsA`), `keepsA_getUserName`, `Keeps.arrayMapMA` (new, law-free) | PROVED given T |
| `IO.mkRef ∅` | `IO.mkRef` for the expression cache, `MkRefd` handed on | `tripleA_mkExprCache` (`Triple.bindQ`) | PROVED |
| `bindInputsLegacy` | `getDecl` (local-context read / `throwUnknownFVar`), `isSignalBinderType`, `inferHWTypeFromSignal` (try/catch), `addParameter` (dead: `parameters = []`), `withDimVarMapping`, `bindInputPort` | `bindInputsLegacy_keepsCP` (induction on `xs.size − i`; vca), `inferHWTypeFromSignal_keepsCP` (HelpersA), `bindInputPortAP` | PROVED |
| `emitLeaves` | clock/counters/logger, translator call, cache update, port-name throw, `addOutput`, `emitAssign` | `emitLeavesAP` (TranslatePathA) with `htr : RecA O I translate` | PROVED given `translate` keeps |
| run on `entryCompilerState false cacheRef` | `CtxOk` of the entry context | `ctxOk_entry false hr` | PROVED |
| `finishSynth` | `ite`, `throw` | `finishSynthA` (PathA) | PROVED |
| memo write | `sparkleSubModuleCache.modify` | `FramedA.sideModify _ .subModule` | PROVED |

Premises of the result (no per-primitive premise is left):
* `T : RefLawsATele O.quiet mref cref` (ADDED, unproved boundary; logical inconsistency NOT PROVEN) — fields
  `telescope` (openRecordInputs, splitReturnLeaves) and `lamTelescope` (the tail's `lambdaTelescope`, splitReturnLeaves).
* `htr : RecA O I translate` — the translator (an argument, per the review correction); at `JQ O.quiet D` it is
  built from `hC : ChildKeepsA O D` in `legacyTailA_of_step`.
* NOT run in this entry and so not a premise here: `machineShape?`, `synthesizeMachineCertified`, `closeInstsM/GM`.

Runtime caveats (structural only): `splitReturnLeaves`, `openRecordInputs` and `stripMemoizeWrappers` are real
code over `Lean.Expr` primitives (`instantiate`, `abstract`, `replaceFVarId` are `extern`); the model treats them
through `Keeps` frame laws only (`mkLambdaFVars`/`whnf`/… are `FramedA`), never their results. `panic` in
`getConstInfoCtor`'s `isCtor?` is covered in the MODEL only. Not claimed: that the tail returns the right module.
