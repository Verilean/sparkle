# Claude Code handoff — Signal DSL → RTL proof

Updated: 2026-09-28 (4th revision). Target branch: `poc/roundtrip-proof`.
The S3 "mutually recursive mux composition" work unit is complete. The unified
`Term` domain's real fuel recursion, reserved-parent protection, dependency
order, entry, and output-RTL execution general theorem
(`Tools/ShippingUnifiedExecutionSoundness.lean: execution_source_of_env`) are
connected. `mixedCertifiedShape?` gained the purely additive `unifiedGateRoot`
disjunct, so the covered sources take the certified route.
Read the boundary table and work-unit sections below as reflecting the
completed items.
Vector-mux cache reuse is also restored (through the validated wrapper; the
old VExpr endpoint is derived via the `ofV` embedding).
Per-operation mixed widths are complete: `Term` is width-indexed
(`SType.bits w`) and the endpoint takes a per-input width assignment `vw`.
Width-changing operations (setWidth) are complete: the canonical
`Signal.map (BitVec.setWidth w)`/`zeroExtend` at literal positive widths takes
a total lowering in `translateFallback` (`translateSetWidthUncachedWith`,
sharing the validated cache) and connects to the same endpoint as `Term.setw`.
Widening emits `{k'd0,x}`, narrowing the `w'(x)` encode, equal widths an
alias. The RTL-side chain (simpleRhs/TypedExpr/PrintShape/renderer/grammar/
binding/zero-width/merge) accepts both IR shapes, and `checkedOptimize_cast`
proves cast-carrying bodies pass through the checked optimizer unchanged.
S4 is under way: the single `Signal.register` over the unified domain
(polymorphic domain, literal init) is certified via a total lowering + gate,
with cycle/trace theorems (`Tools/ShippingRegisterSoundness.lean`) connected
at the real core entry.
Next candidates: the rest of S4 (sequential duplicate merge, feedback,
multiple registers, enable, sequential SV text), sign extension (excluded —
the legacy narrowing behavior is unproved), general slice/concat surface
operations, symbolic widths, remaining combinational forms, S5–S7.

## Read this first

The goal is: **for every path on which the existing Signal DSL compiler
succeeds, the actual emitted RTL is equivalent to the source.** Replacing the
compiler with a smaller one, shrinking the success domain, or per-circuit
replay proofs do not count as completion.

Do not treat defining a source language or adding cache lemmas by themselves
as domain expansion; a unit is complete only when the general theorem reaches
the real entry and the emitted RTL.

The user values work that finishes in complete units over fine-grained
commits or short sessions. Committing is pre-approved. Do not stop after each
intermediate commit to ask "continue?"; work to a complete unit boundary.
Never hide unproven scope or hypotheses. Keep the TODO and milestone
documents in line with the implementation.

Canonical planning documents:

- [TODO](CertifiedRoundtrip-TODO.md#current-shipping-compiler-todo)
- [Milestones and completion criteria](ShippingCompiler-Milestones.md)
- [Coverage of successful paths](ShippingCompiler-Coverage.md)
- [Proof record](ShippingCompiler-Soundness.md) (long history; most recent
  changes at the end)

## Boundary between proved and open

| Scope | Status |
| --- | --- |
| Positive common-width BitVec inputs, constants, add/sub/mul, and/or/xor, same-width logical shifts | Connected through output syntax, declarations/references, the RTL's unique bounded solution and finite delta settling |
| Bool inputs/constants/Bool mux/standard Bool logic and equality; ult/ule/slt/sle and standard equality over the BitVec expressions above | Likewise connected to the general source → RTL theorem |
| BitVec-result mux trees | Connected for `VExpr` (conditions in the old `BExpr`, leaves in the old `FExpr`) |
| Mutual recursion placing muxes under arithmetic/comparison parents | Complete. `ShippingUnifiedRecursion` (fuel contract) + `ShippingUnifiedProtection` (protection/order) + `ShippingUnifiedEntrySoundness` + `ShippingUnifiedExecutionSoundness.execution_source_of_env` (both sorts) |
| Per-operation mixed widths (different positive widths across subtrees) | Complete. Width-indexed `Term` and per-input width assignment `vw`, same endpoint |
| Width-changing operations (canonical setWidth/zeroExtend map at literal positive widths) | Complete. `canonicalSetWidth?` recognition + total lowering + `Term.setw` on the same endpoint. Verified by 72 SV execution cases: widening 8→16, narrowing 65→8, equal width, and a widened operand under an arithmetic parent |
| Sign extension, general slice/concat surface operations, symbolic widths, remaining combinational forms/interfaces | Open. Still on the legacy path (no general theorem). Exhaustive reconciliation with the successful branches is also needed |
| Single register (`Signal.register initLit` over the unified domain, polymorphic domain) | S4 started; first unit complete. Total lowering + gate + `ShippingRegisterSoundness`: at the real core entry's raw module, the cycle theorem `register_step_of_env` (out = current value, next state = the source recurrence, rst = 0) and `trace_of_cycles` (the `runModule` trace from the initial value). Standard three axioms only |
| `dropZeroWidthModule` proved body/weOf-preserving on the certified register shape (covers the `SPARKLE_NO_REGDEDUP=1` configuration). Remaining S4: the sequential duplicate merge (`mergeDuplicatesRaw` is unvalidated; needs register bisimulation — the test checks the default configuration numerically for 12 cycles), feedback (`Signal.loop`/`circuit do`), multiple registers, enabled-register zero-width preservation (the enable cycle theorem itself is proved at the raw core module: `registerEnable_step_of_env`, capture/hold recurrence matching the fixed source semantics), reset muxes, sequential SV text (goes through `optimizeModule`, unproved) | Open |
| Memories, hierarchy, final composition over the whole success domain | S5–S7, open |

Main existing endpoints:

- `Tools/ShippingExecutionSoundness.lean`: `compiledFragment_execution`
- `Tools/ShippingMixedExecutionSoundness.lean`: `execution_source_of_env`
- `Tools/ShippingVectorMuxSoundness.lean`: `execution_source_of_env`

These connect the actual synthesis, zero-width cleanup and checked duplicate
merging, checked optimization, syntax/name guarantees for the same string as
the emitted AST, and the two-valued zero-delay RTL meaning with finite
parallel delta settling. Premises such as input agreement and bounded initial
environments remain. Undriven values are held fixed during delta execution.
X/Z, physical delays, and the external simulator's own correctness are out of
scope. `EnvDefines` (the runtime Lean environment holds the target
declaration) remains an explicit trust boundary.

"Open" primarily means the general theorem/connection for that path does not
exist yet. The unified-foundation files carry no `sorry`/new `axiom`, and the
tests audit the key theorems' axiom dependencies. This is not a claim that
every file in the repository is `sorry`-free.

## Map of the recent implementation

### The unified foundation — `52ab4c3`

| File | Role / reusable definitions |
| --- | --- |
| `Tools/ShippingUnifiedSource.lean` | `SType` and the typed `Term`; Bool and common-width BitVec recurse into each other freely. `WF`, `eval`, `denote`, `quote`, `denote_val`. Embeddings of the old `FExpr/BExpr/VExpr` with meaning/quotation/WF preservation, `instFVars_quote` |
| `Tools/ShippingUnifiedMeaning.lean` | `Value`, `Kind`, the pure syntactic recognizer `view`, `Meaning`. `Meaning.deterministic` is the uniqueness of one Lean expression's value and sort. `meaning_quote`/`meaning_quote_mixed` connect quoted expressions to meanings. Bool and BitVec 1 are distinguished |
| `Tools/ShippingUnifiedCache.lean` | `Records`; preservation through the actual `cacheLookupValidated` and `recordTranslation`. `validated_hit`, `record_preserves`, `cached_action` (the latter assumes the uncached lowering's correctness) |
| `Tools/ShippingUnifiedInvariant.lean` | `Inputs`, `Inv`, `Outcome`: execution, inputs, cache records, typed body, and preservation of live wire values. `cached_outcome`, `Inv.allocate`, `Inv.emit_reserved`, `Inputs.of_mixed` |
| `Tests/Compiler/ShippingUnifiedSourceTest.lean` | Meaning proofs on real sources, compile success plus 2,322 source/legacy/SV/delta cases, axiom audits. Not a substitute for the general mutual-recursion theorem |

`Inv.emit_reserved`'s input-collision/record-collision hypotheses for the
final assignment to a reserved parent wire were subsequently derived from the
child recursion and the fuel induction closed (see the boundary table).

### Existing local translation, recursion and entry

- `Tools/ShippingMixedBinarySoundness.lean`
  - `Frame`: structural preservation of declaration growth, used names,
    bindings, records, simple statements; reusable under the new meaning.
  - `Frame.record_reserved`: transports a record of an initially-used wire
    from post-translation back to the start.
  - `binary_returns`: decomposes the real arithmetic lowering into
    "reserve parent → child a → child b → parent assignment".
  - `translateCanonicalSignalBinary_mixed`, `binary_frame`,
    `core_binary_recorded` are the model proofs under the old invariant.
  - The old `Child`/`Lookup` depend on the old Bool/BitVec valuations; the
    unified `Inv` uses its own contracts.
- `Tools/ShippingMixedRecursion.lean`
  - `Contract`, `ActionSpec`, `FreshAction`, contracts for inputs, constants,
    comparisons, Bool operations, Bool mux.
  - `bool_fuel_contract` is the old closed recursion proof and the model for
    the unified construction.
  - `emit_bool_frame`, `translateBoolBinary_returns`, `typed_bool_bin`,
    `bool_bin_rhs` and the `*_step` rewrites are reused.
- `Tools/ShippingVectorMuxRecursion.lean`
  - `vector_step`, `emit_vector_frame` (the old fuel contract/orders were
    subsumed by the unified induction).
- `Tools/ShippingPendingSoundness.lean` and
  `Tools/ShippingTranslationOrder.lean`
  - `Protected`, `Protects`, `Orders`: the reserved parent is neither read
    nor driven by children; single assignment and dependency order.
  - Value preservation alone is not assumed to imply the RTL stability
    conditions; order is connected separately in the unified version.
- `Tools/ShippingContractEntrySoundness.lean`
  - `emitLeaves_correct`, `emitLeaves_from_ports`, `emitLeaves_postReady_at`.
- `Tools/ShippingVectorMuxSoundness.lean`
  - The model for connecting a real declaration, input preparation,
    quotation/substitution, outputs, post-processing, and RTL.
- `Tools/ShippingMixedEntrySoundness.lean`: `PrintBaseAt`, `RawValueAt`.
  `Tools/ShippingTypedPostSoundness.lean`: `OutputTypedAt`.
  `Tools/ShippingMixedExecutionSoundness.lean`: `execution_of_entry`.
  These backends already handle arbitrary output widths; prefer reuse.

### Notes on the real compiler

The target is `Sparkle/Compiler/Elab.lean`.
`mixedCertifiedShape?` now dispatches through `mixedGateBoolBody`,
`mixedGateVectorRoot`, `unifiedGateRoot`, and `unifiedRegisterRoot` — all
purely additive. **Missing the gate is not the same as the whole compiler
failing**: sources outside the gate still succeed on the fallback.

The literal-width BitVec mux fallback goes through
`translateControlCachedWith (translateVectorMuxUncachedWith rec n)` (a hit is
validated against the recorded expression, a miss lowers and records); the
same wrapper hosts the setWidth cast lowering
(`translateSetWidthUncachedWith`), the register lowering
(`translateRegisterUncachedWith`), and the enabled-register lowering
(`translateRegisterEnableUncachedWith`). Hit justification uses the unified
`Meaning`/`Records` invariants. The old `VExpr` endpoint keeps its statement
and is derived through the `ofV` embedding.

## Next work units and completion criteria

1. **The rest of S4.** Sequential duplicate merging (the sequential
   `mergeDuplicates` is the unvalidated `mergeDuplicatesRaw`; either validate
   it in the compiler with a register-bisimulation check or prove it),
   feedback (`Signal.loop`/`circuit do`, register cones reading register
   outputs), multiple registers, enable/hold, user reset muxes, and the
   sequential printed SV (sequential modules currently go through
   `optimizeModule`, unproved).
2. **Remaining combinational forms.** Sign extension (the legacy lowering's
   narrowing behavior is unproved — do not certify it as-is), general
   slice/concatenation surface operations, symbolic widths, and the
   inventory's interface forms.
3. **S5–S7.** Memories, hierarchy, and the final composition across the
   success domain.

A finished unit connects recognition, total lowering, the invariant
inductions, the entry, and the RTL semantics, with regression and axiom
audits; do not present a smaller step as a finished unit.

## Verification and environment

- `lean-toolchain`: `leanprover/lean4:v4.32.1`. Use the existing project
  environment.
- Latest full verification: `lake build Tests.AllTests`, **641 jobs green**.
- Typical iterative targets:

  ```sh
  lake build Tools.ShippingUnifiedRecursion
  lake build Tools.ShippingRegisterSoundness
  lake build Tests.Compiler.ShippingUnifiedSourceTest
  lake build Tests.AllTests
  ```

- Never run more than one `lake build` at a time. Run the full build per
  coherent change set. `lake test` previously hit an unrelated macOS linker
  issue; acceptance verification is the `Tests.AllTests` build.
- Model axiom audits on the `collectAxioms` blocks at the end of the tests.
  The only permitted dependencies are `propext`, `Classical.choice`,
  `Quot.sound`. Audit both the new endpoints and their applications to real
  declarations; never substitute `sorryAx` or a native oracle.
- `Tests/AllTests.lean` imports the shipping tests; register any new module
  as a `lean_lib` root in `lakefile.lean`.

Known Lean implementation notes:

- Keep `SType.Type` an `abbrev`; making it a `def` broke type-class
  inference in existing code.
- Dependent mux induction patterns sometimes need the explicit sort:
  `| s, .mux ...`.
- `bitVecEqualityWidth?` returns `Option Expr`; go through
  `canonicalNatLitValue?` for the width Nat.
- Replacing `view_binary`'s `simp only` with a plain `cases op <;> rfl` made
  elaboration extremely slow.
- Extract HashMap name equality with `beq_iff_eq`; `simp [eq_comm]` hit
  recursion-depth problems.

## Working tree and commits

Check `git status --short` when taking over. The user has uncommitted work
unrelated to this proof effort (e.g. `docs/design/`, firmware, scratch
files). `.env`/`.mcp.json` are untracked; never open or commit them.
No `git add .`, no bulk clean/reset, no reverting unrelated changes; stage
only the task's files explicitly. Do not add commit trailers.

Recent proof-effort history:

| Commit | Content |
| --- | --- |
| `52ab4c3` | Unified source meaning/cache/invariant foundation |
| `e0a3e91` | Mutually recursive mux composition through shipping RTL execution |
| `4809a71` | Vector mux cache reuse through the validated wrapper |
| `7569b81` | Per-operation mixed widths through the unified endpoint |
| `ab47e13` | Width-changing setWidth casts through the unified endpoint |
| `12fa945` | Register cycle theorem through the real shipping entry (S4 start) |
| `406f0b9` | Cherry-pick of main's registerWithEnable semantics fix |
| `01a7d42` | Sequential zero-width cleanup preserved on the register shape |

## Starting instructions for Claude Code

```text
Read docs/ShippingCompiler-ClaudeCode-Handoff.md and take over the
CompCert-ification of the existing Signal DSL compiler.
Continue with the remaining S4 state/reset scope (sequential duplicate
merging, feedback, multiple registers, enable) and then S5–S7.
Never shrink the existing success domain or replace the compiler with a
smaller one. Preserve the user's uncommitted changes, and keep the TODO and
milestone documents in line with reality. Do not stop at intermediate
commits; work to complete unit boundaries. Distinguish finished from open
work, and verify with Tests.AllTests plus the endpoints' axiom audits.
```
