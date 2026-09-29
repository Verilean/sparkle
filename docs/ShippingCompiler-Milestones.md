# Shipping compiler proof — milestones

Updated 2026-09-28; S2 completed in `075e9f4`; S3 comparisons, Bool logic/equality and BitVec mux trees connected.
This is the current milestone plan for the existing compiler. The dated entries
in [the proof record](ShippingCompiler-Soundness.md), and the earlier
certificate/typed-frontend milestones, are evidence and history, not this plan's
completion checklist. The actionable checklist is at the top of
[CertifiedRoundtrip-TODO.md](CertifiedRoundtrip-TODO.md#current-shipping-compiler-todo).

## Target and reporting rule

The target remains: every successful compilation in the existing Signal DSL
compiler agrees with its emitted RTL, for the stated admissible inputs and
execution model. A replacement typed compiler, a smaller syntax gate, or a
per-circuit replay certificate alone does not discharge this target.

Track each source domain against three obligations: concrete syntax/binding,
source-to-selected-IR values, and emitted-RTL execution. Expanding the domain
requires connecting all three for that extension; it does not invalidate an
already proved smaller domain. A milestone closes when its general endpoint is
proved and audited, not when a certain number of lemmas or commits have landed.

## Status and exit criteria

| ID | Milestone | Status | Completion criterion |
| --- | --- | --- | --- |
| S0 | Original positive-width BitVec combinational fragment | Done | Actual shipping text has concrete syntax and unique bound declarations; emitted AST has the unique bounded solution and finite delta settling to the source value. `compiledFragment_execution` supplies the endpoint. |
| S1 | Current mixed Bool/BitVec fragment: source IR and syntax | Done, `2ad67ae` | Actual entry, cleanup/checked merge and both checked optimizer selections connect source IR values to the exact printed AST, concrete grammar, legal names and all reference/target bindings. `syntax_source_of_env` supplies the endpoint. |
| S2 | Current mixed fragment: RTL semantics and settling | Done | One general shipping-source endpoint combines S1 with AST semantic preservation, unique bounded solution, and existence/convergence of every permitted delta trace to the source output. No caller-supplied expression-check, acyclicity, child-correctness or compiler-replay certificate. |
| S3 | Remaining successful combinational paths | Active — comparisons, Bool logic, BitVec mux trees, mixed widths and setWidth casts connected | Inventory the existing successful paths, then connect remaining Bool surface forms, BitVec-result mux, other comparisons/shifts, width-changing/mixed-width operations and successful interface forms through syntax and RTL semantics. Completion requires the inventory's combinational entries to be covered, not one more chosen example. |
| S4 | State and reset | Active — one register over the unified domain connected at the raw core entry | Derive a general state/trace correspondence from the actual stateful compilation path, including initialization, clock/update observation, enable/hold and supported reset behavior; preserve it through actual postprocessing, optimization and emitted RTL. Separate typed single-register results do not close this milestone. |
| S5 | Memory | Pending | Model and prove the actual successful memory paths: initialization assumptions, read latency, writes/masks, read/write ordering and collisions where applicable. Connect arbitrary admissible traces through actual compilation and emitted RTL. |
| S6 | Hierarchy | Pending | Give instances compositional execution semantics; prove port/parameter/width linkage and state/memory composition for actual successful hierarchical entry points. Name validation alone does not close this milestone. |
| S7 | Successful-domain coverage and final composition | Pending | Reconcile all successful dispatcher/entry/pass branches with proved cases, compose the end-to-end theorem, and instantiate that theorem on representative real circuits. No silently omitted success branch or caller-provided replay proof. State the remaining trust assumptions explicitly. |

S0 covers inputs/constants, six basic arithmetic/bitwise operations and
same-width logical shifts. The S1/S2 baseline covers the `BExpr` source
fragment: Bool inputs/literals, unsigned `ult`/`ule`, nested Bool-result mux and
positive common-width BitVec arithmetic operands. Input arguments may be
interleaved and unused arguments may have other positive widths. This does not
establish general mixed-width arithmetic or BitVec-result mux. S3 now extends
the same general endpoint to `Signal.slt`, `Signal.sle` and standard BitVec
`Signal.beq`, standard Bool equality and canonical Bool `&&&`/`|||`/`^^^`/`~~~`,
recursively combined with Bool-result mux, over the same common positive-width
arithmetic operands. The new `VExpr` endpoint additionally covers BitVec-result
mux trees with `BExpr` conditions and `FExpr` leaves. It does not allow a vector
mux below an arithmetic/comparison node, or mixed result/operand widths.

The chosen proof order is S2, then extension work S3–S6, then S7. State/memory/
hierarchy do not logically depend on completing every combinational extension;
their exact ordering may follow the successful-path inventory. Keep their model
design and coverage notes without claiming their proofs have begun or completed.

## S2 — completed work unit

Owner/status: complete. `execution_source_of_env` in
[ShippingMixedExecutionSoundness.lean](../Tools/ShippingMixedExecutionSoundness.lean)
combines the exact shipping syntax with SV evaluation, unique bounded solutions
and finite parallel settling. Initial environments must satisfy the emitted
declaration bounds; undriven values remain fixed throughout delta execution.

Completed obligations:

1. Derive expression/assignment forward-semantic conditions from the emitted
   AST's declaration widths, including the one-bit `out` exception to the
   internal width environment. Reuse `typedExpr_printed` and
   `typedBody_assignsCheck` where their hypotheses match; carry the result across
   both optimizer selections.
2. Extend dependency-order reasoning to mixed recursive translation. Track
   pending parent names allocated before their children, cache hits, Bool and
   BitVec live bindings, and the final output assignment. Derive absence of
   cycles/repeated drivers from successful synthesis, rather than asking the
   theorem's caller to supply it.
3. Preserve the order and semantic facts through actual cleanup, checked
   duplicate merging and checked optimization. Reuse existing order/validator
   lemmas only after deriving their hypotheses for the mixed domain.
4. Compose `module_settled` and the delta execution results with the same AST and
   text returned by S1. Bind outputs to the source's library Signal observations
   at every source time, keeping `EnvDefines` explicit.
5. Instantiate the general endpoint on real nested and reordered-input sources;
   cover optimizer acceptance and retention, shared/cache-used expressions and
   unused inputs. Run `lake build Tests.AllTests` and audit endpoint dependencies
   for only `propext`, `Classical.choice`, `Quot.sound`.

Starting points:

- [Mixed syntax endpoint](../Tools/ShippingMixedBindingSoundness.lean)
- [Typed expressions](../Tools/ShippingTypedExprSoundness.lean) and
  [mixed postprocessing](../Tools/ShippingTypedPostSoundness.lean)
- [Recursive contracts](../Tools/ShippingMixedRecursion.lean)
- [Existing order invariant](../Tools/ShippingTranslationOrder.lean) and
  [pending-name protection](../Tools/ShippingPendingSoundness.lean)
- [Settled equations](../Tools/ShippingSettledSoundness.lean),
  [delta semantics](../Tools/ShippingDeltaSemantics.lean) and
  [original fragment execution endpoint](../Tools/ShippingExecutionSoundness.lean)

The mixed order invariant is now derived by `bool_fuel_orders`, using the
BitVec recursion order proof and protected pending names. Both actual
postprocessing choices preserve it. Real nested and reordered-input declarations
instantiate the endpoint at arbitrary source observation times.

## Active work unit: S3

The [coverage inventory](ShippingCompiler-Coverage.md) records dispatcher families
and the exact current boundary. It is an initial structural inventory, not a
proof that every successful legacy branch has been enumerated. Next: establish
regressions for uncovered combinational routes, then extend the general source
language and recursive invariants through the same execution endpoint.
State, memory and hierarchy remain separate substantial milestones.

Completed S3 extension: signed comparisons. `SignalCompareKind` gives the
existing comparison recursion all four `ult`/`ule`/`slt`/`sle` cases. The shipping
entry gate and total lowering now include the exact signed library forms.
`execution_source_of_env` proves the extended domain through the same syntax,
unique bounded solution and finite settling endpoint. Signed operand widths
are derived from recursive wire declarations; arbitrary compound signed IR
operands are not assumed to have the source width.

The concrete syntax proof includes the existing sign-bit-bias output, plus the
printer's zero-width literal and unknown-width `$signed` forms. Those last two
printing cases are syntax results, not an extension of the source theorem to
zero-width or unknown-width sources. Five real sources were confirmed to
compile before the extension. `ShippingSignedComparisonTest` instantiates the
general theorem on a nested source and checks 2,250 source/legacy/SV/delta cases
at widths 1, 8 and 65. Legacy comparison runs use the old cached handler chain
at every recursive step. Endpoint axiom audits admit only the standard three.

Completed S3 extension: standard BitVec equality. `compareE` accounts for the
actual type/instance telescope of `Signal.beq`; `execution_source_of_env` now
covers it through the same endpoint, including nested ordered/equality tests.
The direct path accepts equality derived from DecidableEq on BitVec, preserving
the existing fallback for custom BEq. Regression work also fixed a legacy
applicative shortcut that had erased custom instance semantics. That repair is
regression-tested; the source theorem still covers the quoted standard instance,
not all user-defined instances or general applicative syntax.
`ShippingEqualityTest` checks 2,250 source/legacy/SV/delta cases and 32 custom
instance cases. Applicative regressions cover 14 actual compilations with
exhaustive small-width inputs, including delayed literals and arithmetic shifts.

Completed S3 extension: canonical Bool logic and standard Bool equality. The
recursive source relation, cache separation, gate/entry proof and allocation
order now cover all five operators through the same execution endpoint.
Negation lowers to one-bit equality with a generated false wire; its actual
output grammar and execution use the existing comparison proofs. Real nested
source theorems and legacy-path comparisons are in `ShippingBoolEqualityTest`
and `ShippingBoolLogicTest`. This does not cover arbitrary user instances or
all mapped/unfolded spellings.

Completed S3 extension: positive common-width BitVec mux trees. The general
`ShippingVectorMuxSoundness.execution_source_of_env` endpoint connects actual
recursive translation and source input positions to arbitrary-width output,
concrete syntax/binding, unique bounded equations and finite RTL settling.
`ShippingVectorMuxRecursion` proves both value and dependency-order contracts;
`ShippingContractEntrySoundness` derives output facts from those contracts.
The original Bool endpoint remains a one-bit specialization of the backend.
`ShippingVectorMuxTest` instantiates nested and computed-condition sources
(including a source without Bool inputs) and checks 2,772
source/legacy/SV/delta cases at widths 1/8/65, including shared arithmetic leaves.

Completed S3 extension: vector mux cache reuse. `translateFallback` now sends
literal-width vector muxes through the shared validated cache wrapper, so
repeated mux subtrees reuse one wire. Soundness of hits comes from the unified
deterministic `Meaning` record invariant; the old `VExpr` vector endpoint keeps
its statement and is derived from the unified endpoint via the `ofV` embedding.

Mutual source/cache foundation now implemented: `ShippingUnifiedSource` embeds
all three previous source languages and agrees with library Signal observations.
The deterministic `ShippingUnifiedMeaning.Meaning` relation covers arithmetic
containing muxes and comparisons over those expressions. The actual validated
cache wrapper and record updates preserve `ShippingUnifiedInvariant.Inv`, once
its uncached child satisfies that stronger invariant. A reserved-name assignment
lemma is available; protection of that name through recursive children is not
assumed completed. `ShippingUnifiedSourceTest` proves a real nested source's
meaning and checks 2,322 legacy/SV/delta cases, auditing standard axioms.

Completed S3 extension: mutual mux composition. `ShippingUnifiedRecursion`
closes the actual fuel recursion for the whole mutual `Term` domain with one
induction, deriving the reserved-parent safety hypotheses of
`Inv.emit_reserved` from child frames and `Frame.record_reserved`.
`ShippingUnifiedProtection` proves pending-parent protection and dependency
order across every node kind, including validated cache hits, so arithmetic
that reserves its result before mux/comparison children stays acyclic.
`ShippingUnifiedEntrySoundness` ports the width-polymorphic output contracts,
and `ShippingUnifiedExecutionSoundness` connects the new `unifiedGateRoot`
acceptance (a third, purely additive disjunct in `mixedCertifiedShape?`) to the
same execution backend: `execution_source_of_env` now covers either result sort
of the mutual domain. `ShippingUnifiedSourceTest` instantiates the endpoint on
nested, comparison-root and width-65 arithmetic-root declarations and keeps
2,322 source/legacy/SV/delta cases, now through the certified gate.

Completed S3 extension: per-operation mixed widths. The unified source is
width-indexed (`SType.bits w`); different subtrees may use different positive
widths while each canonical operation keeps a common operand width, matching
what the recognizers always accepted syntactically. The fuel contract,
protection and order inductions quantify over a per-input width assignment,
so one theorem instance covers e.g. an 8-bit comparison controlling a 65-bit
mux (`mixedWidth` in `ShippingUnifiedSourceTest`: gated, 54 SV execution
cases, endpoint instantiated). The old uniform-width embeddings (`ofF`/`ofB`/
`ofV`) instantiate the width assignment constantly.

Completed S3 extension: width-changing setWidth casts. The canonical
`Signal.map (BitVec.setWidth w)`/`zeroExtend` form (literal positive widths)
no longer reaches the legacy handler: `translateFallback` recognizes it
(`canonicalSetWidth?`) and lowers it totally behind the validated cache
wrapper — a `{k'd0, x}` concat when widening, the size-cast `w'(x)` slice
encode when narrowing, a plain alias at equal widths. Both IR shapes were
threaded through the whole RTL chain (`simpleRhs`, `TypedExpr.zext/trunc`,
`PrintShape`, renderer byte equality, concrete grammar, name binding,
zero-width and merge passes), and `checkedOptimize` provably keeps cast
bodies unchanged (`checkedOptimize_cast`). `Term.setw` extends the unified
source; the same `execution_source_of_env` endpoint covers widening (8→16),
narrowing (65→8), equal width and a widened operand under an arithmetic
parent (72 SV execution cases in `ShippingUnifiedSourceTest`).

Still open in S3: sign extension (the legacy lowering's narrowing behavior
is not certified and stays on the fallback), general slice/concatenation
surface operations, symbolic widths, and the remaining successful interface
forms from the inventory.

Started S4: one register over the unified combinational domain. The
canonical polymorphic-domain `Signal.register initLit input` root takes a
total lowering (`translateRegisterUncachedWith`; input cone first, then one
register statement on the shared `clk`/`rst` with the asynchronous kind the
legacy handler falls back to over a polymorphic domain — concrete domains
keep the legacy handler and its inferred kind), and a gate disjunct
(`unifiedRegisterRoot`). `Tools/ShippingRegisterSoundness.lean` proves from
`synthesizeCombinationalCore` (the raw module; the actual
`SPARKLE_NO_REGDEDUP=1` shipping configuration precedes cleanup): per cycle,
under admissible inputs and reset low, `out` observes the register's current
value and `regNexts` steps it by the unified source cone's value
(`register_step_of_env`); `trace_of_cycles` iterates over `runModule`, so
the observable trace from the declared initial value is exactly
`Signal.register`'s stream. Non-interference needed no extra premises: every
wire name is allocated (`_gen_*`/`_tmp_*`), so `rst`/`out` are never wires,
and typed assigns have positive declared widths. The zero-width cleanup is
now proved to be the identity on this register shape (body and width
environment preserved, so the theorems cover the cleaned
`SPARKLE_NO_REGDEDUP=1` module of `synthesizeCombinational`). The enabled register
(`Signal.registerWithEnable initLit en input`, polymorphic domain) is also
certified: the total lowering mirrors the legacy order (hold mux reading the
register output back), and `registerEnable_step_of_env` proves the
capture/hold cycle recurrence — the fixed source semantics — at the raw core
module, with `trace_of_cycles` generalized to state-reading updates for the
`runModule` trace. The feedback register
(`Signal.loop (fun s => Signal.register initLit cone)`) is proved to the
cycle recurrence at the current state (`loopRegister_step_of_env`; the loop
binder is one more unified-source input bound to the pre-allocated register
wire, so the combinational contract machinery is reused verbatim and no
reserved-parent protection is needed), and zero-width cleanup is proved
preserved on all three register shapes. All three shapes also carry
packaged full-run endpoints: `register_run_of_env`,
`registerEnable_run_of_env` (width bound carried by `trace_of_cycles_inv`)
and `loopRegister_run_of_env` state that the compiled `runModule` trace
observes the source register stream itself, identified against the library
`.val` streams via `loop_register_val` and the definitional
`registerWithEnable_val` (`regAcc_run`/`regHold_run`/`accLoop_run`).
Multiple registers have their first certified shape: the two-stage shift
chain (`Signal.register i1 (Signal.register i2 cone)`) is gate-accepted
and proved end to end — the monolith decomposes both fuel-fixpoint levels,
the per-cycle theorem shifts the inner register's value into the outer one
while the inner steps by the cone, and
`trace_of_cycles2`/`register2_run_of_env` package the full two-state
`runModule` trace against the nested source register streams.
The single-slot `circuit do` is reified onto the loop form: the macro
destructures its handle tuple with `Prod` projections (matcher-free),
`canonicalCircuitDo?` recognizes the shape purely and `cdoConeToLoop`
rewrites coerced register reads into the loop binder, so the certified
feedback lowering emits the byte-identical module, and
`map_fst_loop_register`/`cdoAcc_val` identify the source streams. The
endpoint chain is stated on the circuit-do quote form itself: `cdoE`
transcribes the elaborated call exactly, `cdoConeToLoop_quote`
distributes the normalizer over the unified quote, and the
`CdoPreserves` monolith feeds `cdo_step_of_env`/`cdo_run_of_env`,
instantiated on the real declaration with standard axioms only.
Open in S4: the sequential `mergeDuplicates` (the unvalidated raw merge;
the test exercises the merged default configuration numerically),
`circuit do` beyond the proved shapes (the two-slot cross-coupled form
now carries its full proof chain for the returned-slot-0 shape — the
Cdo2Preserves monolith with doubled self machinery and chained cone
contracts, the state-reading two-register trace lemma, and real-entry
per-cycle/full-trace endpoints instantiated on the real declaration;
open: slot-1 return, differing widths, more slots, Reg-operator reads,
mutual-stream `.val` identification), deeper register
chains and register networks beyond depth two, user reset muxes, and
sequential emitted-SV text (sequential modules pass through
`optimizeModule`, unproved). S5–S7 remain unfinished.

## Trust, validation and work cadence

- `EnvDefines` remains the explicit link between the runtime Lean environment
  and the intended source declaration. Investigate how to discharge or account
  for it at S7; do not report an unconditional theorem if it is still a premise.
- The present RTL execution model is two-state, zero-delay parallel delta
  rounds with fixed inputs; delta rounds are not source clock cycles. External
  simulator equivalence, arbitrary event scheduling, X/Z and physical delays
  are not proved. Stateful extensions must state their clock/trace models.
- The S0–S2 endpoints and S3 comparison/Bool-logic/vector-mux-tree extensions have no `sorry` dependency.
  Other files in the repository can contain placeholders or executable-oracle
  proofs; do not use a repository-wide placeholder count as the endpoint audit.
- Latest validation: `lake build Tests.AllTests`, 626 jobs. New Bool equality
  and logic tests check 1,890 and 1,962 source/legacy/SV/delta cases, respectively,
  with standard-axiom audits of the general and real-source endpoints. Existing
  coverage includes 2,250 signed and 2,250 BitVec equality cases, 32 custom-BEq cases,
  14 exhaustive applicative compilations and standard-axiom audits. Mixed execution
  regression checks 2,700 source/SV/parallel-delta cases on 18 paths, with
  6 optimizer acceptances and 12 retentions, including shared expressions.
  This is a test-module build, not a claim that the `lake test` binary ran.
- Make coherent, tested commits as recovery/review checkpoints. A commit or a
  new lemma is not a reason to stop work and ask the user to say “continue”.
  Work toward the active milestone until it is complete, the user redirects,
  or a concrete blocker needs a decision. Report blockers with the exact open
  connection and continue independent work where possible.
- Bundle bookkeeping-only edits with the next relevant work checkpoint unless
  a standalone documentation change is requested. Update checkboxes, proof
  references, validation and remaining assumptions when a milestone changes.
