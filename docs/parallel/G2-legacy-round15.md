# G2 — worker B2, round 15 (branch `par/g2-legacy-15`, base `fix/cache-rollback` = `ed09bd33`)

Nothing here was built (no Lean run from a worker). To be folded into
`docs/parallel/G2-legacy.md` as §54–§58.

## 54. Item 1 — `hsig` dropped

`Tests/Compiler/LegacySemInstanceTest.lean` imports
`Tools.ShippingLegacySemSignalFrame`; `useDbl_output` passes
`isSignalBinderType_frame xTy` to `one_binder_entry_output`. The hypothesis
`hsig` is gone; nothing else in the statement changed.
(`one_binder_entry_output` keeps its `SignalTestFrame T` argument: the file
that proves it was built after it and is not imported by it.)

## 55. Item 2 — `InputSkipped` is NOT refutable from `Returns`; it stays

Read: the variable arm of `Rec.translateExprToWireImpl`
(`Sparkle/Compiler/Elab.lean`, "0. Handle free variables first", lines
6903–6955). On `.fvar id` it does, in order:

1. `CompilerM.lookupVar id`: the context's `varMap`, then the builder
   state's `sourceBindings` — a hit returns the wire;
2. on a miss, a read of the `Meta` local context: if the variable has a
   value (a `let` variable) the arm translates the VALUE, recursively;
3. otherwise `try Lean.Meta.reduce e catch _ => pure e`; if the result
   differs from the variable the arm translates THAT, recursively;
4. only then `throwError "Unbound variable …"`.

So "a successful translation of a variable implies the variable is mapped"
is false as a statement about `Returns`. What holds is proved:

`Tools/ShippingLegacySemFVarArm.lean` (new), `impl_fvar`: a successful run of
the body on `.fvar id` is a `lookupVar` hit with the state unchanged
(`visible ctx s.sourceBindings id = some w ∧ t = s`), or a successful run of
the recursive translator on some `val`, or on some `reduced` with
`(reduced != .fvar id) = true` — same hint, flags, states and wire.

Three independent reasons why the skipped outcome cannot be excluded for
`useDbl` without more than `Returns`:

* **the arm reads the local context and an oracle.** Excluding cases 2 and 3
  needs the run in its `Meta` context down to this arm (`RunsIn` through the
  whole translator, including its `withLocalDecl`s) and a Meta-library
  premise (`reduce` on a `cdecl` variable returns it);
* **the leaf is `dbl x`, not a variable.** With no port bound the body's
  test `hasMappedFvar` is false at run time and the body REPLACES the
  expression by `whnf e` (an oracle's result; `pre_plain`'s premise
  `HasMappedFVar` is what keeps the proved walk out of that branch) and goes
  on with that. Nothing relates the result to `dbl x`: the run need not reach
  the variable arm at all (a `whnf` to `Signal.mk …` / a lambda takes other
  arms);
* **that test is kernel-opaque in both directions.** `hasMappedFvar` is
  `Expr.find?` (`findImpl?`, `opaque`): it is not provably `false` even for
  the empty `varMap`.

Whether the real compiler returns in that situation is an empirical
question; the test now RUNS it (§56, `SKIPPED-INPUT EVIDENCE`). If the log
says `THREW`, the behaviour is "does not happen in practice" but remains
unprovable here; if it says `RETURNED`, `InputSkipped` is a real behaviour.

Stated consequence: `useDbl_output` keeps the disjunct. Removing it needs
either the failure-reporting `tryCatch` inversion in `RunsTo` form (§48), or
a change in the COMPILER (shared change, not made, see §58).

## 56. Item 3 — compiled evidence (test, second `run_cmd`, logs only)

On the real `useDbl`, in the test's environment:

* `hbody EVIDENCE`: the shape of `stripMemoizeWrappers (← openRecordInputs
  value)` (a lambda? binder name? is its body a lambda?); inside
  `lambdaTelescope`: one variable and the body `== callE x`; the premise's
  two `instantiateRevRange` results equal the declared type and `callE x`;
  the declared user name is `x`;
* `hinf EVIDENCE`: `inferHWTypeFromSignal` on the declared binder type, run
  from `entryCompilerState false cache` and a fresh builder state — expected
  `bitVector 8`;
* `hres EVIDENCE`: the head of `whnf (← inferType leaf)` is the constant
  `Signal`;
* `SKIPPED-INPUT EVIDENCE`: `emitLeaves … [("out", dbl x)] none 0` run with
  NO port bound — `RETURNED` or `THREW (message)`.

These are observations of one run. The premises quantify over every
successful run (every environment a run may see), so the logs support them
and do not prove them. The whole block is inside `try … catch` and only
logs. It was written without a build: an elaboration error there fails the
test file (the block can be deleted without touching any theorem).

## 57. Item 4 — `MemoHit`: what can be said without `MemoLaws` — nothing

Read (`synthesizeFromConst`, `synthesizeCombinationalCoreWith`):

* **Writers.** `sparkleSubModuleCache.modify (·.insert declName result)` at
  four places, all inside `synthesizeFromConst`, each after a successful
  synthesis: the certified arm, the mixed certified arm, the machine arm, the
  legacy arm. `sparkleSubModuleCache.set {}` once, in
  `synthesizeCombinationalCoreWith` at depth 0. No other writer in
  `Sparkle/Compiler/` (the snapshot / restore of the inline attempt does not
  include it: line 5577).
* **Key.** `declName` only — for ANY declaration, not only
  `@[hardware_module]` ones. Not keyed by `parameters`, `certifiedFrontEnd`,
  the `ConstantInfo` handed over, or the translator.
* **Reader.** Only the legacy arm (after the three gates declined), under
  `!symbolicMode`.

Consequences:

1. A hit on `useDbl` means: since the last reset, SOME run of
   `synthesizeFromConst` on the NAME `useDbl` succeeded and stored its result
   — through any of the four arms and with any front-end flag / constant
   (with the front end on, `entryConst` hands over the UNFOLDED constant and a
   certified gate takes it). So even informally the hit is not "what an
   earlier run of this theorem's kind returned"; it is "what an earlier run
   of one of four arms returned for this name".
2. To turn that into the output statement one needs an invariant of the
   memo's CONTENT ("every entry `(n ↦ (m, d))` satisfies the output statement
   of `n`") preserved by every writer — an induction over the heap's history.
   `MReturns` / `Returns` quantify the world existentially per run: two
   facts about the same `IO.Ref` in two runs cannot be related, so neither
   "the entry was written by a sound run" nor "the read misses after the
   reset" (round 13, `memo_miss_after_reset`, needs get-after-set) is
   derivable. `MemoHit` itself is stated with `MReturns` (SOME run of the
   read): it cannot even be refuted by a heap law until the walk is in
   `RunsTo` form.
3. Without a law the only removals are by changing the statement's scope:
   (a) keep the disjunct (today); (b) state the theorem for the entry one
   level up AND assume the laws; there is no (c).

**Answer: negative.** `MemoHit` cannot be excluded or characterised for
`useDbl` without a value law for `sparkleSubModuleCache` (get-after-set and
a frame, i.e. `MemoLaws` or an extension of `RefLaws`) and the `RunsTo` form
of the two walks. The minimal law set for the OUTERMOST entry is the one of
§43: `memoGet`, `memoSet`, and the frame of the memo's value over the eight
other `set`s, `sparkleSynthDepth.set`, `getConstInfo`, `getEnv`.

## 58. Requested shared changes (NOT made)

1. `lakefile.lean`: a `lean_lib` entry for `Tools.ShippingLegacySemFVarArm`.
2. For discussion, compiler (`Sparkle/Compiler/Elab.lean`,
   `bindInputsLegacy`): the `try … catch _ => pure false` around
   `inferHWTypeFromSignal` is what creates `InputSkipped`. If a binder whose
   type passes `isSignalBinderType` and then fails the type oracle were an
   ERROR (as it already is in symbolic mode: "Do not catch failures here"),
   a Signal binder could no longer be skipped silently; the walk's third
   outcome would then be confined to non-Signal binders, where skipping is
   the intended behaviour. This changes behaviour only for inputs that today
   compile with a silently missing port.

## 59. Hypotheses and conclusion of `useDbl_output` after this round

Hypotheses: `htel` (Meta-library), `hbody` (reflection + oracle + two
bodiless functions), `hinf` (binder-type oracle), `hres` (result-type
oracle), `hmap` (kernel-opaque), `hplain` (environment), `hnosub` (the run),
`hunfE` (unfolding oracle), `hr` (the run). Conclusion:
`MemoHit ∨ (∃ id cache, … RawValueAt 8 … (x + x)) ∨ InputSkipped`. Verbatim
in the test file.
