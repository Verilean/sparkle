# Shipping compiler coverage inventory

Updated 2026-09-27, including the S3 signed-comparison extension. This is an initial structural inventory of the
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
| `synthesizeFromConst` → `mixedCertifiedShape?` → `synthesizeMixedCertified` | S1/S2: Bool inputs/literals, `ult`/`ule` and now `slt`/`sle`, Bool-result mux over common-width BitVec operands; `execution_source_of_env` | Extend operations/results and recursive width invariants. |
| Both shape gates miss → existing synthesis/cache path | No general source-to-shipping-RTL theorem | Reconcile source opening, normalization, output leaf splitting, cached submodules and all successful legacy handlers. |
| `translateStepWith` → `translateCore` | Existing fragment's literals, inputs and eight binary operations; mixed order proof reuses protected pending names | Other supported surface forms must be related to the quoted source, not assumed equal. |
| `translateFallback` → Bool control/cache path | Current quoted Bool domain, including validated cache hit/miss behavior | General Bool operations and additional comparison forms. |
| `translateFallback` → `Rec.translateExprToWireCached` / `translateExprToWireImpl` | No blanket fallback theorem | Unfolding/type queries, application normalization, primitive and structural routes below. |
| `synthesizeCombinationalWithParameters`, symbolic dimensions | Not covered by S0–S2 endpoint | Parameter interpretation, width positivity/zero-width behavior, emitted parameter syntax and instantiated execution. |
| `synthesizeHierarchical*` / `validateDesignNames` | Name validation is implemented; no general hierarchy semantic theorem | S6 instance/port/parameter semantics and composition. |

## Operation and interface families

| Family / implementation anchor | Coverage boundary and next connection |
| --- | --- |
| `primitiveRegistry`, `handleBitVecOps`: arithmetic and bitwise binary operations | Eight canonical common-width operations are covered in the quoted fragment. Registry membership alone does not cover direct, overloaded, unfolded or mapped spellings. |
| `Signal.slt` / `Signal.sle` | General quoted-source endpoint now covers these at a positive common width, recursively under Bool mux. Five real success witnesses and 2,250 execution cases; direct/unfolded/constant variants still need source-coverage reconciliation. |
| `primitiveRegistry`: `BEq.beq`, Bool `not`/`and`/`or`/`xor`, unary negation/complement | Outside the current shipping source endpoint. Add source constructors/recognition, recursive preservation, declaration typing, order and RTL execution. |
| `handleMux` | Bool-result quoted mux is covered by the specialized control path. BitVec-result and other successful mux forms remain outside that theorem. |
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
current quoted arithmetic domain. General `Signal.lt`/`le`, equality, `sltC`,
alternative mapped/applicative expressions and zero/symbolic operand widths
remain outside this claim even if they compile successfully.

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
2. Choose a coherent extension (Bool operators and additional comparisons, then
   BitVec-result mux/varying-width expressions), and carry it through the whole
   shipping endpoint. Do not close S3 after the first extension.
3. Reconcile the remaining successful branches against this table before S7;
   maintain state, memory and hierarchy obligations under S4–S6.
