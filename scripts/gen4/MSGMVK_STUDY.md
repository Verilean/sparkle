# MSGMVK_STUDY: can `MsgMvK` be dropped for successful compiles?

Base: kjob/rt180 7c836d8a. Issue: sparkle-gen4-parametric-supply. Reviewer ruling 2026-11-05: MemoFamily rev3 (15 statements) stays; `MsgMvK` is NOT added as a law.
Words: "read" = I read the code, Lean did not check it. No Lean was edited or built for this study.

## Result

**Not removable by a path argument.** The error branch of the catch at `Sparkle/Compiler/Elab.lean:6599` is on the path of a successful compile. `MsgMvK` stays a named unsolved hypothesis. No new theorem (`topEntry_K_of_family3'`) is written, since it would need a premise that is not provable from the code.

## 1. The catches on the call paths (Elab.lean)

The site: `handleDefinitionUnfold`, 6599-6610. `catch _` after `synthesizeCombinational name`; renders `lastFail` with `ex.toMessageData.toString` (6605); ends in `throwError` (6609-6610). On this path the site itself always throws. The question is whether an enclosing catch resumes.

| Line | What it wraps | Can it catch the 6610 error and continue? |
|---|---|---|
| **6358 (`catch ex1`) and 6374 (`catch ex2`)** in `tryInlineUnfold` (6345-6383) | `translateExprToWire eReduced …` (6360), and the retry `translateExprToWire eReduced2` (6372) | **YES.** This is the resume point. See the path below. |
| 6587 `catch _` | `synthesizeCombinational name` of an `@[hardware_module]` callee (opted-in branch) | Catches child-synthesis errors (which may contain a nested 6610 throw), but its handler is a `throwError`; it does not continue. |
| 6599 `catch _` | `synthesizeCombinational name` (the fallback branch) | It is the site. It catches errors of the nested child synthesis, then throws. No continue. |
| 6408 | `getConstInfo name` (the `isValidDef` check) | No: wraps no translation. |
| 7157, 7162 | `extractBitVecLiteral constValue` / `extractBitVecLiteral reduced` | No: they wrap the literal extractor only. The `translateExprToWire` at 7165 is in the HANDLER of the inner catch, so its errors propagate. |
| 7829 (`.letE`) | `inferHWTypeFromSignal type` | No: no translation inside. |
| 7335 | `extractBitVecLiteral e` | No: no translation inside. |
| 754 | `whnf`/`resetKind` reduction | No: no translation inside. |
| 1957 | `mkAppM projName #[e]` | No: no translation inside. |
| 2143 | `inferHWTypeFromSignal binderType` | No: no translation inside. |
| 1928, 2022, 6473, 8500 | `getConstInfoInduct …` | No: no translation inside. |
| 7020-7025 | `reduce` / `inferType` / `ppExpr` (diagnostic text only) | No: no translation inside. |
| 9389 | `IO.FS.createDirAll`/`writeFile` of sim output | No: no translation inside. |
| 5562-5580 `try … finally` | `doSynth` | `finally` does not swallow; the error propagates. |
| other files in `Sparkle/Compiler/` | only `SimChecked.lean:93` (file write) | No. |

Only the catches at 6358/6374 both wrap `translateExprToWire` and resume.

### Path of a successful run through the error branch (read)

1. `translateExprToWire` reaches `handleDefinitionUnfold` for definition `f`; `f` has a body that is inlined by `tryInlineUnfold` (6594): `unfoldDefinition? e` gives `eReduced ≠ e`, so the `try` at 6357 runs `translateExprToWire eReduced`.
2. Inside that body, a call to a definition `g` is neither inlinable nor `@[hardware_module]`. Its `handleDefinitionUnfold` runs `tryInlineUnfold` (returns `(none, some ex)`), then `synthesizeCombinational g` fails, so the catch at 6599 runs: **`ex.toMessageData.toString` (6605), then `throwError` (6609)**.
3. That error reaches the enclosing `catch ex1` (6358) of `f`'s `tryInlineUnfold`. It calls `restoreWireCaches saved`, retries under reducible transparency, and either gets `eReduced2 == e` → `(none, some ex1)` or catches again at 6374 → `(none, some ex2)`.
4. `f`'s `handleDefinitionUnfold` takes the `(none, lastFail)` arm (6596) and runs `synthesizeCombinational f` (6598). If that succeeds, `f` becomes a sub-module instance and the compile **continues and succeeds**. The failed inline expansion is discarded; only builder state (restored) and the IO-ref caches the code does not restore remain.

So the world `w1` after the rendering at 6605 is the world the successful continuation starts from. The comment at Elab.lean:6346-6350 says the same ("on wide FSMs the inline path fails-then-recovers thousands of times").

## 2. How `MsgMvK` is consumed

- `Keeps … I m := ∀ w, I w → I (endW … m w) ∧ ErrOk … m w` (`Tools/ShippingChildInv.lean:315`): the invariant `I` must hold at the END world of `m` on **every outcome, including `error`**. This is exactly because `catch` hands the end world of the failed attempt to its handler (`KeepsCP.tryCatch`; `tryInlineUnfold_tripleCPK` in H7, used from `Tools/ShippingGen4KWalkLegacyH8.lean:55`).
- `I` is a `StableK` invariant (`KW O P`, `Tools/ShippingGen4KWalkPrims.lean:29`): it transfers across a step only when `cv/sv/dv/mv` are unchanged (`kw_transfer`). `mv` is the child-module memo table `sparkleSubModuleCache` (`Tools/Assume/MemoFamily.lean:27`).
- `keepsK_msgToStringR` (`Tools/ShippingGen4KWalkLegacyH8a.lean:148`) is the only consumer of `MsgMvK`: it needs `mv (end of m.toString) = mv w` to keep `I` on the world that the catch at 6358 then resumes from.

So the K-walk DOES require the invariant on the error outcome of the 6599 catch. Restating the triple with the error postcondition unconstrained for this throw is **not sound** for the walk: the resumed continuation (the `synthesizeCombinational f` at step 4) reads the memo and needs `I` on `w1`. Dropping it would also leave `lastFail` as an arbitrary exception whose world is untracked, and the final theorem's statement on successful runs would then have to carry an extra premise about that continuation. No restatement in the current framework avoids this.

## 3. What would be needed to remove it

One of:

(a) A 16th family statement (memo version of `Diag.msgToString`, the missing memo twin of `OkMsg`/`excOk`): `∀ m, OkMsgMv m → quiet w → mv (endW … (liftM m.toString) w) = mv w`, plus a memo version of `excOk` saying that every exception the walk can throw satisfies `OkMsgMv`. This is `MsgMvK` plus its supply. The reviewer ruled out adding it.

(b) A proof, from the tracked exception class, that rendering a message does not write `sparkleSubModuleCache`. The obstacle (MEMO_FAMILY_FREEZE §R2.6): `OkMsg`'s `withContext c` only constrains `c.env` (`OkEnv c.env`, the three refs); `c` is the environment captured at THROW time, not the current world. `MessageData` can also hold lazy closures (`ofLazy`) which are arbitrary code. Neither is controlled by the existing 15 statements.

(c) Changing the compiler so that the rendered text is computed without a Meta action (e.g. render at throw time into a `String` stored in the exception, or build the text from the exception without `MessageData.toString`), which would let the step be an explicit `pure`. The brief forbids compiler edits.

## 4. Result for the issue

- Item 1 answered: yes, an enclosing catch (Elab.lean 6358/6374) resumes after the 6610 throw; every other catch listed does not wrap a translation.
- Item 2 answered: the consumer needs `I` on the error outcome; no restatement without a new premise.
- Item 3: not removable, so this document is the deliverable. `MsgMvK` stays hypothesis `def` at `Tools/ShippingGen4KWalkDiag.lean:195`; `topEntry_K_of_family3` is unchanged. Ledger FG ±0, T1 ±0.
