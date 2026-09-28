# Shipping compiler coverage inventory

Updated 2026-09-28, including comparisons, Bool logic/equality and BitVec mux trees. This is an initial structural inventory of the
existing compiler, not an exhaustive success-domain theorem or a new acceptance
policy. A registered operator/handler is a possible route, not evidence that
every source spelling succeeds. S3 must attach successful source witnesses and
reconcile the internal branches before marking this inventory complete.

## Entry and recursive dispatch

The implementation is [Sparkle/Compiler/Elab.lean](../Sparkle/Compiler/Elab.lean).
Use declaration names as anchors; source line numbers move during extensions.

| Actual route | Current shipping theorem coverage | Remaining obligation |
| --- | --- | --- |
| `synthesizeFromConst` → `certifiedShape?` → `synthesizeCertified` | S0: quoted positive-width BitVec fragment, `compiledFragment_execution` | Extend source/interface forms outside this gate without treating refusal by this gate as compiler failure. |
| `synthesizeFromConst` → `mixedCertifiedShape?` → `synthesizeMixedCertified` | S1/S2: Bool inputs/literals, canonical `&&&`/`|||`/`^^^`/`~~~`, `ult`/`ule`/`slt`/`sle`, standard BitVec/Bool `beq`, Bool-result mux over common-width BitVec operands; BitVec mux trees via `ShippingVectorMuxSoundness.execution_source_of_env` | Extend operations/results and recursive width invariants. |
| Both shape gates miss → existing synthesis/cache path | No general source-to-shipping-RTL theorem | Reconcile source opening, normalization, output leaf splitting, cached submodules and all successful legacy handlers. |
| `translateStepWith` → `translateCore` | Existing fragment's literals, inputs and eight binary operations; mixed order proof reuses protected pending names | Other supported surface forms must be related to the quoted source, not assumed equal. |
| `translateFallback` → Bool control/cache path | Current quoted Bool domain, including validated cache hit/miss behavior | Other Bool surface forms/custom instances and additional comparison forms. |
| `translateFallback` → cached literal-width BitVec mux / width-changing map | Unified `Term`: mutual composition of muxes below/above arithmetic and comparison parents at either result sort, via `ShippingUnifiedExecutionSoundness.execution_source_of_env`, including validated cache hit/miss and record preservation; per-operation mixed widths and canonical width-changing maps (`Signal.map (BitVec.setWidth w)`/`zeroExtend` at literal positive widths — zero-extension, truncation and equal-width casts) are covered through the same endpoint. | Sign extension, general slice/concat surface operations and symbolic widths stay on the legacy path without a general theorem. |
| `translateFallback` → canonical polymorphic-domain register | One `Signal.register initLit` root over the unified combinational domain: cycle observation and register update proved at the raw `synthesizeCombinationalCore` module (`register_step_of_env`, `trace_of_cycles`), reset held low, initialization from the declared value; `dropZeroWidthModule` proved body/width-preserving on this shape (the `SPARKLE_NO_REGDEDUP=1` configuration). | Sequential duplicate merge (unvalidated `mergeDuplicatesRaw`), feedback/`circuit do`, multiple registers, enable/hold, reset muxes and sequential printed SV stay open; concrete-domain registers keep the legacy handler. |
| `translateFallback` → `Rec.translateExprToWireCached` / `translateExprToWireImpl` | No blanket fallback theorem | Unfolding/type queries, application normalization, primitive and structural routes below. |
| `synthesizeCombinationalWithParameters`, symbolic dimensions | Not covered by S0–S2 endpoint | Parameter interpretation, width positivity/zero-width behavior, emitted parameter syntax and instantiated execution. |
| `synthesizeHierarchical*` / `validateDesignNames` | Name validation is implemented; no general hierarchy semantic theorem | S6 instance/port/parameter semantics and composition. |

## Operation and interface families

| Family / implementation anchor | Coverage boundary and next connection |
| --- | --- |
| `primitiveRegistry`, `handleBitVecOps`: arithmetic and bitwise binary operations | Eight canonical common-width operations are covered in the quoted fragment. Registry membership alone does not cover direct, overloaded, unfolded or mapped spellings. |
| `Signal.slt` / `Signal.sle` | General quoted-source endpoint now covers these at a positive common width, recursively under Bool mux. Five real success witnesses and 2,250 execution cases; direct/unfolded/constant variants still need source-coverage reconciliation. |
| Standard BitVec `Signal.beq` | The general quoted-source endpoint now includes equality at a common positive width, recursively with all ordered comparisons and Bool-result mux. The direct route checks that BEq comes from decidable equality; arbitrary user BEq is not reinterpreted as RTL `==`. |
| Canonical Bool `&&&` / `|||` / `^^^` / `~~~`, standard Bool `Signal.beq` | Recursive quoted-source endpoint connected, including mixed nested comparisons/muxes. Mapped/unfolded spellings and custom instances are not generally proved. |
| BitVec unary negation/complement | Outside the current shipping source endpoint; require their own source/recursive/backend connection. |
| `handleMux` | Bool-result and positive common-width BitVec muxes are connected through the unified mutual endpoint, including muxes under arithmetic/comparison parents and computed conditions containing muxes. Other successful mux forms (non-canonical types, varying widths) remain unproved. |
| `handleBitVecOps`, `translateShiftAmount` | Same-width logical shifts covered in the quoted domain. Nat amounts, other amount widths, arithmetic right shifts and extraction/unwrapping paths require their own connection. |
| `handleBitVecOps`, primitive application handling inside `translateExprToWireImpl` | Slices, concatenation, zero extension/truncation and sign-extension handling require varying-width source semantics and matching AST/RTL rules. The application handler has additional paths; enumerating only `handleBitVecOps` is insufficient. |
| `handleApplicative`, `handleTupleProjections`, `splitReturnLeaves`, `openRecordInputs` | General map/ap/tuple/record interfaces, flattened outputs and inputs are outside the scalar quoted endpoint. Track source-to-port mapping and multiple output observations. |
| Unit/PUnit application branches and zero-width cleanup | Successful terminator/zero-width paths are outside the positive-width theorem. Prove erasure semantics and interface behavior. |
| `handleDefinitionUnfold`, applicative normalization, canonical instance checks | Definition expansion and hardware-module recognition need explicit source correspondence; successful fallback is not ruled out by a gate miss. |
| `handleRegister`, `handleLoop`, `handleCircuitMonad` | S4: actual state/feedback path, enable/hold, initialization and supported reset behavior, then arbitrary source traces and emitted sequential execution. Circuit-monad handlers also contain structural cases; classify those individually. |
| `handleMemory` | S5: actual initialization, latency, write masks and read/write interactions, then trace preservation. |
| Hardware-module instantiation / design cache | S6: submodule correctness, interface/parameter linkage and compositional state/memory execution. |

## Signed comparison witnesses

[ShippingSignedComparisonTest](../Tests/Compiler/ShippingSignedComparisonTest.lean)
contains `signedLt`, `signedLe`, `signedOne`, `signedWide` and `nested`. All five
compiled through the shipping compiler before this extension. They now reach
the mixed source gate; the regression also compiles them with that gate disabled
and the original cached handler chain used for every recursive translation.
The source theorem is instantiated on `nested` for arbitrary source Signals and
observation times, including arithmetic overflow before signed comparison.

The new source coverage is exactly library `Signal.slt`/`Signal.sle` over the
current quoted arithmetic domain. General `Signal.lt`/`le`, `sltC`,
alternative mapped/applicative expressions and zero/symbolic operand widths
remain outside this claim even if they compile successfully.

## Equality and applicative dispatch

[ShippingEqualityTest](../Tests/Compiler/ShippingEqualityTest.lean) adds five
standard equality sources, including width-one, width-65, aliased operands and
a nested mixed-comparison source. These compiled before the extension; they
now reach the mixed gate. The nested source instantiates the general execution
theorem at arbitrary Signal observations. Arbitrary user BEq,
alternative mapped forms and zero/symbolic widths are not covered by this
source theorem.

A regression exposed an existing miscompilation: a custom BEq returning `true`
was emitted as ordinary equality. The old `Seq.seq` shortcut read only the
outer primitive name. Signal applicative notation now reaches the existing
body-preserving `Signal.ap` handler; noncanonical BEq projection lowering
extracts and applies the instance's actual method. This preserves both constant
and reordered-argument custom implementations in regressions. It is a compiler
fix with regression evidence, not a general proof of all legacy unfolding.
`ApplicativeSemanticsTest` also checks reversed subtraction, nested arithmetic,
arithmetic right shift and constants on either side of surface applicative
notation. The body-preserving route beta-reduces Seq's delayed argument before
literal recognition and preserves BitVec shift amounts before unfolding toNat.

Do not infer success merely from a library/registry name: for example the
attempted `Signal.lt` on BitVec 8 failed at `Decidable.rec` during this work.
The retained fallback success witness in `ShippingMixedEntryTest` is now a
BitVec-result mux, which remains outside the two quoted entry gates.

## Bool logic and equality

The canonical library forms `a &&& b`, `a ||| b`, `a ^^^ b`, `~~~a` and
`Signal.beq a b` on Bool were confirmed to compile before extending the source
gate. `BExpr` now includes all five forms recursively, and the same
`execution_source_of_env` covers their values, emitted syntax and finite RTL
settling. The Bool/BitVec source relations explicitly separate equality's source
type and Boolean operators' instance widths, preserving cache determinacy and
record separation.

Binary logic emits one-bit bitwise operations. Canonical Bool negation lowers
to equality with a generated false wire, using the existing comparison pipeline;
it adds that constant wire rather than emitting the legacy unary-not AST.
This avoids extending the backend grammar for this source family. The resulting
actual text/AST is covered by the same endpoint, including constant allocation,
cache reuse, dependency order and postprocessing.

[ShippingBoolEqualityTest](../Tests/Compiler/ShippingBoolEqualityTest.lean) and
[ShippingBoolLogicTest](../Tests/Compiler/ShippingBoolLogicTest.lean) instantiate
the general theorem on real nested sources, with arbitrary Signals/times. They
compare the direct path, the fully recursive legacy handler path, SV evaluation
and parallel settling; cover aliases, repeated subexpressions, constants and
all Boolean inputs; and exercise mixed 8-bit boundary values. A custom asymmetric
Bool BEq is separately regression-tested. Arbitrary custom BEq and other user
overloads remain outside the source theorem; recognition does not silently
reinterpret them as canonical operations. `Signal.map Bool.not` and other
alternative spellings still require coverage reconciliation. The full 626-job
`Tests.AllTests` build passes; the two new execution regressions cover 1,890 and
1,962 cases, respectively, and both real-source endpoint audits admit only the
standard three axioms.

## Pass and theorem obligations

S0–S2 connect their domains through actual zero-width cleanup, checked duplicate
merging and both selections of checked optimization. This is not a universal
pass theorem for arbitrary stateful/memory/instance IR. Every extension must
establish the relevant pass hypotheses from successful compilation, and keep
syntax, binding and RTL execution on the same emitted AST and string.

The present RTL model is bounded two-state, zero-delay parallel rounds with
fixed undriven values. `EnvDefines` remains the source-environment trust boundary.
S4–S6 need richer trace/composition models; X/Z, physical delays and equivalence
to an external simulator have not been proved.

## Next concrete work

1. Add successful actual-source witnesses for uncovered combinational families,
   recording which gate/legacy branch each reaches. Include distinct surface
   forms and interface/parameter modes rather than testing registry names alone.
2. Continue with BitVec-result mux and varying-width expressions, and carry it through the whole
   shipping endpoint. Do not close S3 after the first extension.
3. Reconcile the remaining successful branches against this table before S7;
   maintain state, memory and hierarchy obligations under S4–S6.

## BitVec mux-tree extension

`VExpr` admits existing arithmetic leaves and nested BitVec mux branches with
existing Bool conditions at a common positive width. Output typing, printing,
binding and execution now carry that width instead of assuming one bit.
[ShippingVectorMuxTest](../Tests/Compiler/ShippingVectorMuxTest.lean) instantiates
a real source theorem and checks 2,772 execution cases (widths 1/8/65, both
conditions, overflow, aliasing, three initial seeds and three postprocessing
routes). `underArithmetic` is included only as a regression: it is a successful
source outside `VExpr`. The former mux fallback witness in `ShippingMixedEntryTest`
is now admitted by the expanded mixed gate.

The direct total mux route intentionally avoids lookup and recording at vector
mux nodes until the source/cache invariant includes their meanings. This can
increase duplicate intermediate work; arithmetic/Bool children retain validated
caching. The legacy recursive chain is compared in tests, not claimed proved.

## Mutual source/cache foundation (2026-09-28)

`ShippingUnifiedSource.Term` represents both source sorts with arbitrary mutual
nesting, at a common BitVec width. Its quotation, substitution and library-value
proofs preserve the old FExpr/BExpr/VExpr fragments. `ShippingUnifiedMeaning`
provides deterministic meanings on the actual Lean expressions; its syntax
view checks canonical instances and literal widths without a MetaM type query.
`ShippingUnifiedCache` connects those meanings to the real validated lookup and
record write. `ShippingUnifiedInvariant.cached_outcome` preserves input values,
execution, typed body and the live-wire frame, with an explicit uncached-handler
contract still to be discharged by recursion.

[ShippingUnifiedSourceTest](../Tests/Compiler/ShippingUnifiedSourceTest.lean)
adds `arithmetic1`, `arithmetic8`, `arithmetic65`, `comparison`, and `nested` as
existing successful paths outside the current certified gates. It identifies
the real nested declaration with the typed quotation and library meaning, and
checks 2,322 source/legacy/SV/delta cases. These are success witnesses and
regressions, not universal compiler correctness for that larger domain.
The remaining source-coverage boundary in the tables above is unchanged.
