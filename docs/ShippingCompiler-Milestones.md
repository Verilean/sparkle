# Shipping compiler proof — milestones

Updated 2026-09-27; S2 completed in `075e9f4`; S3 signed comparisons and standard BitVec equality connected.
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
| S3 | Remaining successful combinational paths | Active — ordered comparisons and BitVec equality connected | Inventory the existing successful paths, then connect uncovered Bool operations, BitVec-result mux, other comparisons/shifts, width-changing/mixed-width operations and successful interface forms through syntax and RTL semantics. Completion requires the inventory's combinational entries to be covered, not one more chosen example. |
| S4 | State and reset | Pending | Derive a general state/trace correspondence from the actual stateful compilation path, including initialization, clock/update observation, enable/hold and supported reset behavior; preserve it through actual postprocessing, optimization and emitted RTL. Separate typed single-register results do not close this milestone. |
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
`Signal.beq`, recursively under
Bool-result mux, over the same common positive-width arithmetic operands.

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

Next: Bool operators/Bool equality and BitVec-result mux, followed by varying widths
and the remaining successful interfaces. S3 remains open until the inventory
is reconciled; these comparison extensions do not close it.

## Trust, validation and work cadence

- `EnvDefines` remains the explicit link between the runtime Lean environment
  and the intended source declaration. Investigate how to discharge or account
  for it at S7; do not report an unconditional theorem if it is still a premise.
- The present RTL execution model is two-state, zero-delay parallel delta
  rounds with fixed inputs; delta rounds are not source clock cycles. External
  simulator equivalence, arbitrary event scheduling, X/Z and physical delays
  are not proved. Stateful extensions must state their clock/trace models.
- The S0–S2 endpoints and S3 signed-comparison/equality extensions have no `sorry` dependency.
  Other files in the repository can contain placeholders or executable-oracle
  proofs; do not use a repository-wide placeholder count as the endpoint audit.
- Latest validation: `lake build Tests.AllTests`, 624 jobs, including 2,250
  signed and 2,250 equality source/legacy/SV/delta cases, 32 custom-BEq cases,
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
