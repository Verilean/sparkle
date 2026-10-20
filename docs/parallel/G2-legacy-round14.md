# G2 — worker B2, round 14 (branch `par/g2-legacy-14`, base `fix/cache-rollback` = `8bc938f5`)

Nothing here was built (no Lean run from a worker). To be folded into
`docs/parallel/G2-legacy.md` as §46–§51.

Task of the round: remove `htele` (`TelescopeSpec … (EntryFacts …)`) from
`useDbl_output`.

## 46. The `RunsIn` calculus (`Tools/ShippingLegacySemRunInCalc.lean`, new)

`RunsIn.bind`, `RunsIn.pure`, `RunsIn.liftMetaM` (the inner action's run in
the SAME context, builder state untouched), `MRunsIn.run`,
`MRunsIn.ite_pos / ite_neg`, `RunsIn.ite`, `RunsIn.dite_pos / dite_neg`,
`runsIn_tryCatch` (body's run or a handler's, same builder state, same
context), `getDecl_runsIn_find` (a successful `getDecl` of a variable the
context declares returned that declaration; the variable is given by an
equation so the caller does not rewrite).

Every proof is the built proof of the `Returns` / `MReturns` lemma of the
same name with `mctx` kept (`Returns.bind`, `Returns.pure`,
`returns_liftMetaM`, `returns_tryCatch`, `MReturns.run`, `getDecl_runsIn`).

## 47. The entry walked in the telescope's context (`Tools/ShippingLegacySemEntryIn.lean`, new)

`TelescopeIn body P` (`P : Meta.Context → Array Expr → Expr → Prop`): a run
of `lambdaTelescope body k` is a run of `k xs inner` IN `mctx` with
`P mctx xs inner`. `legacy_entry_walk_in`: `legacy_entry_walk` with
`TelescopeIn` and the binder walk's run as `RunsIn … mctx …`. Generated from
`legacy_entry_walk`'s text: identical up to the telescope, then the same
steps with `MRunsIn.*`. `legacy_entry_walk` is untouched.

Why a second walk and not a corollary: `TelescopeSpec`'s conclusion is
`MReturns (k xs inner) r` (some context); the context of the continuation
cannot be recovered from it.

## 48. The binder walk (`Tools/ShippingLegacySemBinder.lean`, new)

`bindInputsLegacy_one`: in a context whose local context declares `id` as
`d0`, a successful run of `bindInputsLegacy [] false #[.fvar id] 0 k` is

* a run of `bindMixedCertifiedInputs k [((d0.userName, .bits n), id)]`, or
* a run of `k` alone (the binder SKIPPED).

Premises: `SignalTestFrame d0.type` (provable — §50), `InfersBits d0.type n`
(oracle). The context is read ONCE (`getDecl`); after that step the proof
goes back to `Returns` and uses the existing calculus (`returns_tryCatch`).

**The third outcome is a disjunct, not excluded.** `Returns` / `RunsIn`
describe successful runs; "the type oracle did not throw inside the `try`" is
not a statement about a successful run of the walk, and "it never throws" is
false of some worlds. What would remove the disjunct: a failure predicate
(`Throws x mctx ctx s`), a `tryCatch` inversion that reports which case ran
WITH the body's failing run, and a premise about THIS run's world (so the
entry walk in `RunsTo` form, as §43 already needs for `MemoHit`). Or, on the
other side: a proof that `emitLeaves` on `dbl x` with `x` unmapped does not
return (the leaf walk with `HasMappedFVar` false) — not attempted.

## 49. The leaves (`Tools/ShippingLegacySemLeaves.lean`, new)

`splitReturnLeaves_scalar`: `e.isLambda = false`, `SignalTyped e` ⟹ every
successful `splitReturnLeaves e` returns `leaves` with
`leaves.toList = [("out", e)]`. `SignalTyped e`: every successful
`inferType e` then `whnf` gives `tyN` with
`tyN.getAppFn = .const ``Signal us`. From it, proved: `needsReduce` is false
(the result is NOT reduced — the leaf is `e` itself) and the Signal test is
true. Imports only `Tools.ShippingEntrySoundness`.

## 50. Composition and the test

* `Tools/ShippingLegacySemEntryOne.lean` (new): `LamTelescopeOne` (the
  Meta-library fact, stated with exactly what `lambdaTelescopeImp.process`
  computes: `T.instantiateRevRange 0 0 #[]`, `b.instantiateRevRange 0 1
  #[.fvar id]`), `OneBinderScope`, `telescopeIn_of_lam`, `InputSkipped`,
  `one_binder_entry_output`.
* `Tools/ShippingLegacySemSignalFrame.lean` (new, OPTIONAL, imported by
  nothing): `isSignalBinderType_frame : ∀ T, SignalTestFrame T`.
* `Tests/Compiler/LegacySemInstanceTest.lean`: the round-13 theorem renamed
  `useDbl_output_r13` (statement and proof unchanged); new `useDbl_output`.

**What the new `useDbl_output` claims differently from round 13**

* weaker conclusion: a third disjunct `InputSkipped logProf ``useDbl callE m`;
* `htele` is gone; in its place `htel`, `hbody`, `hsig`, `hinf`, `hres`;
* `hbody` makes explicit a premise that `htele` contained silently: the
  body the telescope runs on (after `openRecordInputs` and the `partial`
  `stripMemoizeWrappers`) is `fun (x : T) => b` with the two
  `instantiateRevRange` results. `Expr.instantiateRevRange` is an `opaque`
  extern: `b.instantiateRevRange 0 1 #[.fvar id] = dbl (fvar id)` is not
  provable in the kernel for any `b`.

## 51. Premises of `useDbl_output`, classified

| Premise | Class |
|---|---|
| `htel : LamTelescopeOne` | Meta-library fact (`lambdaTelescopeImp` is `private partial`) |
| `hbody` | reflection of the environment (the constant's value) through the oracle `openRecordInputs`, the `partial` `stripMemoizeWrappers`, and the kernel-opaque `Expr.instantiateRevRange` |
| `hsig : SignalTestFrame xTy` | provable; premise only until `…SignalFrame.lean` is built |
| `hinf : InfersBits xTy 8` | binder-type oracle: reflection through `inferHWTypeFromSignal` (a statement about every successful run, like `hunfE`) |
| `hres : ∀ id, SignalTyped (callE id)` | result-type oracle: reflection through `inferType` / `whnf` |
| `hmap` | kernel-opaque (`Expr.find?`) |
| `hplain` | reflection of the environment |
| `hnosub` | fact about the run |
| `hunfE` | reflection through `unfoldDefinition?` |
| `hr` | the run |

Outcomes not excluded: `MemoHit` (heap fact of the caller), `InputSkipped`.

## 52. Spots most likely not to elaborate, in order of risk

1. `Tools/ShippingLegacySemBinder.lean`, S2: `Returns.bind b0` needs the
   unifier to reduce `match (([] : List _).find? p).map (·.2) with …` to its
   `none` arm (fallback: `simp only [List.find?, Option.map] at b0`). And S4:
   the assumed shape `tryCatch (infer >>= fun _ => pure true) (fun _ => pure
   false) >>= fun isHWArg => …`.
2. `Tools/ShippingLegacySemLeaves.lean`, L2: the join point of
   `let e ← if needsReduce then whnf e else pure e` (three shapes tried) and
   the definitional match between `needsReduceOf tyN` and the program's own
   `needsReduce` text (two auxiliary matchers that must unfold to the same
   `Expr.casesOn`).
3. `Tools/ShippingLegacySemLeaves.lean`: the three closed name tests
   (`name_test`: `decide` / `decide +kernel` / `rfl` on `Name` literals) and
   `exact needsReduce_closed …` up to matcher iota.
4. `Tools/ShippingLegacySemBinder.lean`: `unfold bindInputsLegacy` (a
   well-founded definition) — at the hypothesis and in
   `bindInputsLegacy_done`; `bindMixed_one_bits` by `rfl`; the wrapper's
   `(#[.fvar id][0]).fvarId! = id` by `rfl`.
5. `Tools/ShippingLegacySemEntryIn.lean`: the tail after the telescope is the
   built tail with `MRunsIn.*`; the risk is only which `first` alternative
   the original took.
6. `Tools/ShippingLegacySemEntryOne.lean`: `have run' : HarnessRun … := bound`
   (unfolds `HarnessRun` and `List.zip`); `rcases` through `OneBinderScope`.
7. `Tools/ShippingLegacySemSignalFrame.lean` (optional): the split of the
   `match` on `Lean.Expr`.

## 53. Next

1. Build `…SignalFrame.lean`, then drop `hsig` (pass
   `isSignalBinderType_frame _`).
2. Compiled evidence for `hbody` / `hinf` / `hres` on `useDbl` in the test's
   `run_cmd` (as `hunfE EVIDENCE`): the body after `openRecordInputs` /
   `stripMemoizeWrappers` is a one-binder lambda named `x`; inside
   `lambdaTelescope` the instantiated body equals `callE id`;
   `inferHWTypeFromSignal` on the declaration's type returns `.bitVector 8`;
   the `whnf` of the inferred type of the leaf is headed by `Signal`. Not
   written this round (it cannot be checked without a build, and a mistake
   there would fail the test file).
3. `InputSkipped` and `MemoHit`: both need the run in `RunsTo` form (§43,
   §48).
4. Several binders: `LamTelescopeOne` for `n` binders (the instantiated
   types depend on the earlier variables) and `bindInputsLegacy` by
   induction on `xs.size - i`; `.bool` and `.domain` binders (a skipped
   binder is then the EXPECTED outcome for `.domain`).
