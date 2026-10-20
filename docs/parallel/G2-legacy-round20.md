# G2 — worker B2, round 20 (branch `par/g2-legacy-20`, base `fix/cache-rollback` = `e81a5ea5`)

Nothing here was built (no Lean run from a worker). To be folded into
`docs/parallel/G2-legacy.md` as §81–§85.

**Status in one line**: the census now RUNS the real entry on every
legacy-route candidate and tabulates the ones that return (items 1–2,
written). Item 3 — naming the largest class of RETURNED declarations — needs
the log of that run; what this note gives instead is the gap statement of
`list_entry_output` for EACH class the tables can show, so the log line
selects one row (§83).

## 81. The round-19 counts (integrator's build, recorded)

400 of 531 Signal-valued definitions examined. Routes: mixed 212, legacy
128, machine 59, certified 1. Legacy top leaf by `fallbackKind`: other 127,
boolControl 1. By head: `<lambda>` 45, `Signal.fst` 39, `Signal.register`
22, `<let>` 7, `Signal.mux` 4, user definitions and others 11 (one
`Signal.map`, body `BitVec.signExtend`). So a mapped unary primitive is not
the commonest leaf; the `Signal.map` arm is not walked.

Caveat (integrator): the population is every Signal-valued definition, not
the declarations the entry returns for.

## 82. Items 1–2 — pass 2 of `Tests/Compiler/LegacyArmCensusTest.lean`

Each legacy-route candidate of pass 1 is handed to the shipping entry
(`synthesizeCombinationalCore n [] false`: certified front end on, no
parameters, not symbolic).

* Isolation: `Meta.saveState` … `restore` around each run; the entry resets
  its `IO.Ref` caches at depth 0 itself; `sparkleSynthDepth` is set to 0
  before and after each run.
* Bounds: `runHeartbeats = 200000` per declaration (`withTheReader
  Core.Context` + `withCurrHeartbeats`); runtime exceptions caught with
  `tryCatchRuntimeEx`; a wall-clock budget `runBudgetMs = 240000` for the
  whole pass, after which the remaining declarations are `NOT RUN`.
* Log lines, all starting `LEGACY ENTRY RUNS`: OUTCOMES (RETURNED / THREW /
  TIMEOUT / RUNTIME / NOT RUN, with the pass's milliseconds); THREW by first
  line of the message, and by the leaf's head; RETURNED by head, by
  `fallbackKind`, by binders (`k binders = a scalar Signal + b structured
  Signal + c domain + d other`), by result payload, the `<lambda>` heads by
  their head after `headBeta`, and by class
  `head | binders | result payload`.

Not covered by pass 2: declarations the gates route to `machine` whose
machine synthesis then declines (they also end in the legacy arm);
structure- / product-valued declarations.

## 83. Item 3 — the gap of `list_entry_output`, per class

`list_entry_output` (round 17) needs: (B) every binder a `bits n` (n ≠ 1) or
`bool` Signal with `InfersHW` / `InfersNoCatch`; (R) a non-lambda result
whose type's `whnf` is Signal-headed, ONE leaf `out`, value of positive
width, flat `RawValueAt`; (L) the leaf in `LeafDom … "out" true` — today:
inputs, the certified term fragment, a plain inline call, or a proved
`HandlerCase`.

The class line `LEGACY ENTRY RUNS, RETURNED by class` selects a row:

| If the largest RETURNED class has … | What is missing | Size |
|---|---|---|
| binders with `d > 0` (other: parameters, instances) or `c > 0` (domain) | (B): a SKIP step of the binder walk. For a non-Signal binder the walk's `try` must yield `false`: the oracle has NO returning run on the binder's type (`∀ ctx s h t, ¬ Returns (inferHWTypeFromSignal T) ctx s h t`) — the opposite premise to `InfersNoCatch`. With it `returns_tryCatch` gives the skip, and `bindInputsLegacy_prepare` gets a third binder kind whose `prepare` step is the identity (the certified `.domain` case). | small: one step lemma, one case of the induction; the pieces exist (`returns_tryCatch`, `bindInputsLegacy_done_returns`' pattern). For a NAT parameter used by the body the leaf then contains a free variable that is not an input: (L) additionally. |
| binders with `b > 0` (structured Signal: a product / structure payload) | (B) and the VALUE MODEL: the walk binds one `.bitVector (sum)` port, which matches a `.bits n` binder at the port; but `Value` has only `bool` / `bits`, and the source meaning of a packed product input (and of `Signal.fst` on it) is not defined. A statement needs definitions that do not exist (the packed encoding as the source value). | large (definitions first) |
| head `Signal.fst` / `Signal.snd` / `<proj …>` | (L): `handleTupleProjections` (5647–5761) ACCEPTS; there is only its decline walk. Plus the value model above (the argument is a product-valued Signal). | large |
| head `Signal.register` | outside the statement altogether: sequential. `RawValueAt` is the flat combinational conclusion; the legacy `handleRegister` emits a register; the certified statements for registers are on the machine route. (R) and (L). The binders table says why the machine gate declined. | not a G2-entry gap; a routing question |
| head `<lambda>` (a beta-redex) | (L): the body takes its `whnf` branch (`isBetaRedex`), i.e. replaces the leaf by an oracle's result. A walk needs a premise on that result (as `hunfE` for `unfoldDefinition?`): "every `whnf` of the leaf is `e'`", then the domain of `e'`. The line "by the head after headBeta" shows what `e'` is likely to be. | medium: one more oracle premise and the body's `whnf`-branch walk (the else-branch is `pre_plain`) |
| head `<let>` | (L): the body's `let` handler (`withLocalDecl` / `withLetDecl`, value translated, variable bound) — no walk; needs `RunsIn` through the handler (the variable arm reads the local context). | large |
| head `Signal.mux` (not canonical) | (L): `handleMux` accepting walk. | medium–large |
| head a user definition, scalar binders, scalar result | nothing new: `plainCallee_leaf` + per-declaration name block and unfolding (rounds 12–18). | per declaration |
| result payload not `BitVec` / `Bool` | (R): several leaves or a packed result; `splitReturnLeaves_scalar` covers one Signal leaf only, and the value model above. | large |

No walk was written this round: which row is the largest is not known until
the log exists, and the only "small" row (the skip step) is useful only if
the binder table shows `c + d > 0` on a class that otherwise fits.

## 84. Queue

1. `Tests/Compiler/LegacyArmCensusTest.lean` (rebuilt; nothing else
   changed). Please return the nine `LEGACY ENTRY RUNS` lines (and the wall
   time).

## 85. Risk (unverified) — the census code only

1. `runEntry`: `tryCatchRuntimeEx` in `MetaM` with two `do` blocks;
   `withTheReader Core.Context … <| withCurrHeartbeats <| …`; `Meta.saveState`
   / `saved.restore`; the `if … else if … else` with a `let … ←` in the last
   branch.
2. A declaration whose synthesis loops WITHOUT reaching a heartbeat check
   stalls the test: the bound is only the heartbeat one; the wall-clock
   budget is checked between declarations, not inside one. If the build
   stalls, lower `cap` or `runBudgetMs`, or skip the stalling declaration.
3. Restoring the `Meta` state does not undo `IO.Ref` writes of a run that
   was cut off; the entry's own depth-0 reset covers its caches, and
   `sparkleSynthDepth` is reset explicitly. The translator's call counter
   (`sparkleCallCounter`, `Elab.lean` 948) is never reset by the entry and
   its limit is per process: `runEntry` sets it to 0 before each run. Other
   profile counters accumulate (harmless).
4. The five-component tuple from `lambdaTelescope`; the `Info` structure
   literal; `prefixOf`.
