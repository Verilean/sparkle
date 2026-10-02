# Shipping compiler coverage inventory

Updated 2026-10-01 (dispatch table reconciled through the register, memory and instance arms; the family sections below keep their original dates). The MEASURED coverage of the repository's own synthesis corpus is in the last section. This is a structural inventory of the
existing compiler, not an exhaustive success-domain theorem or a new acceptance
policy. A registered operator/handler is a possible route, not evidence that
every source spelling succeeds. S3 must attach successful source witnesses and
reconcile the internal branches before marking this inventory complete.

## Entry and recursive dispatch

The implementation is [Sparkle/Compiler/Elab.lean](../Sparkle/Compiler/Elab.lean).
Use declaration names as anchors; source line numbers move during extensions.

| Actual route | Current shipping theorem coverage | Remaining obligation |
| --- | --- | --- |
| `synthesizeCombinationalCoreWith` → `entryConst` (front-end normalisation) | The entry hands `synthesizeFromConst` the declaration as read when a gate accepts it, and the declaration with its untagged user definitions unfolded (`userInliner`: pure delta-beta of untagged user definitions, `<$>`/`<*>` at the library's Signal instances as `Signal.map`/`Signal.ap` with canonical binder names, and projection of a user structure's field out of the constructor its record head-normalises to — zeta of the lets in front, which is what the legacy projection handler's `unfoldDefinition?`/`whnf` loop does to `(ipHW a b).field` — against the run's environment, total, node-budgeted) when the original misses both gates and the unfolding passes one or is a state machine (`machineShape?`, with the structure projections of the run's environment — the third disjunct, since the machine route). Every family theorem then applies to that entry constant verbatim (`synthesizeCombinationalCore_entry_sound`, the whole bundle); real helper-structured declarations are certified end to end (`useSel_execution`, `accH_run`) under the boundary `EntryDefines`, and so are the FIRST TWO REAL IP MODULES: the DroneCAN node filter and the MIL-STD-1553 odd-parity generator, compiled through the field-projecting wrapper their test benches use (`nodeFilter_execution`, `oddParity_execution`: the module computes the IP definition's own output stream; `*_library` identify the IP definition with the quoted term by `rfl`). Byte-identical to the legacy route on 21 + 18 declarations (suite-gated), the latter including the AES S-box and round-constant tables of the IP library; `rcon_execution` proves the round-constant table end to end. | Reducible definitions, universe-polymorphic helpers and library projections (`Prod.fst`) are not unfolded; one refused node (`∀`, metadata, a primitive projection) abandons the whole normalisation; only the unified combinational and the feedback-register endpoints have `_of_entry` twins so far (the other families are reached through the bundle). |
| `synthesizeFromConst` → `certifiedShape?` → `synthesizeCertified` | S0: quoted positive-width BitVec fragment, `compiledFragment_execution` | Extend source/interface forms outside this gate without treating refusal by this gate as compiler failure. |
| `synthesizeFromConst` → `mixedCertifiedShape?` → `synthesizeMixedCertified` | S1/S2: Bool inputs/literals, canonical `&&&`/`|||`/`^^^`/`~~~`, `ult`/`ule`/`slt`/`sle`, standard BitVec/Bool `beq`, Bool-result mux over common-width BitVec operands; BitVec mux trees via `ShippingVectorMuxSoundness.execution_source_of_env` | Extend operations/results and recursive width invariants. |
| `synthesizeFromConst` → `machineShape?` → `synthesizeMachineCertified` (both shape gates miss) | The MACHINE ROUTE: a general `circuit do` — any number of Bool/BitVec slots, a result that is one Signal (directly or one field of a structure result) or a structure of Signals (one output port per field), hardware `let`s — compiled as its packed TRANSITION through `synthesizeMixedCertified` and closed into registers by `Sparkle.IR.Machine.closeMachine`. `MachinePreserves` (one cycle), `machine_trace` (any number of cycles), `synthesizeCombinationalCore_machine_sound` (real entry, boundaries `MachineDefines`, `MachineCloses`); end to end `mThree_execution`, `lin_execution`, `linHW_execution` (an IP declaration itself, two ports). Hardware `let`s are binders of the transition and fields of its packed value, tied by `closeLets` (`closeLets_eval`, `LetsHold`). The emitted text differs from the legacy lowering by decision; 55 real declarations take it. | Automatic per-declaration endpoints; the optimizer/print pipeline for machine modules; concrete domains other than `defaultDomain`; computed constants and sub-module calls inside the body; a generic source bridge. |
| All gates miss → existing synthesis/cache path | No general source-to-shipping-RTL theorem. MEASURED: 271 of the 389 real-corpus declarations take this route (see "Measured corpus coverage"). | Reconcile source opening, normalization, output leaf splitting, cached submodules and all successful legacy handlers, in the order the measurement gives. |
| `translateStepWith` → `translateCore` | Existing fragment's literals, inputs and eight binary operations; mixed order proof reuses protected pending names | Other supported surface forms must be related to the quoted source, not assumed equal. |
| `translateFallback` → Bool control/cache path | Current quoted Bool domain, including validated cache hit/miss behavior. APPLICATIVE-LIFTED Bool-result operators — `(BitVec.ule · ·) <$> a <*> b`, `ult`/`slt`/`sle`, `(· == ·)`, `(· && ·)`, `(· || ·)`, `(· ^^ ·)`, in the form the front end normalises them to, `Signal.ap (Signal.map f a) b` — take this arm (`appBoolOp?`, `translateAppCompare`/`translateAppBoolBinary`: operands under the legacy applicative hint `app_arg`, then the direct route's result assignment); they are `Term.appCompare`/`Term.appBool` of the unified domain, with the full contract, protection and order inductions, both gates, and both `circuit do` cone conversions; `kLut!` table muxes are certified through them. The TWO-LEVEL Bool bodies the IP library writes on control signals — `fun x y => x && !y`, `!x && y`, `!(x || y)` — are `AppBoolOp.two` / `Term.appBool2` in the same arm (`translateAppBool2`: both operands under `app_arg`, the inner application on a wire of its own under the legacy hint `arg1`/`arg2`, then the result); their inner or outer operator is the unary NOT, which is a right-hand side of the whole back half as of that unit (`simpleRhs`, `TypedExpr.not1`, `PrintShape.notRef`, the printed form `(w'(x ^ w'dM))` and its grammar production `maskNot`, `~(x)` when the width is unknown). Numeric literals (`Signal.pure 5` at `BitVec.instOfNat`) are `Term.bitsNum`. | Lifted functions whose body is neither one operator on the two variables nor one of the three two-level Bool bodies (`x.toInt > y.toInt`, a three-level body), unary lifts, BitVec-result lifts (`(· &&& ·) <$>`), and Bool surface forms/custom instances keep the legacy handlers. |
| `translateFallback` → cached literal-width BitVec mux / width-changing map | Unified `Term`: mutual composition of muxes below/above arithmetic and comparison parents at either result sort, via `ShippingUnifiedExecutionSoundness.execution_source_of_env`, including validated cache hit/miss and record preservation; per-operation mixed widths and canonical width-changing maps (`Signal.map (BitVec.setWidth w)`/`zeroExtend` at literal positive widths — zero-extension, truncation and equal-width casts) are covered through the same endpoint. SLICES — `Signal.map (fun x => BitVec.extractLsb' start len x) s` at literal widths with `0 < len` and `start + len ≤ ws`, the form `s.map (BitVec.extractLsb' start len ·)` elaborates to — are the arm `FallbackKind.slice` (`canonicalSlice?`, `translateSliceUncachedWith`: operand under the legacy hint `s`, result wire at `hwTypeFromWidth len`, right-hand side the part-select `s[start+len-1:start]`) and the constructor `Term.slice` of the unified domain, with contract, protection and order inductions, both gates and both `circuit do` cone conversions; the part-select is a right-hand side of the whole back half (`simpleRhs`, `TypedExpr.slice`, `PrintShape.sliceRef`, the renderer and both grammar productions, name binding). CONCATENATION — `a ++ b` of two Signals at the library instance, literal positive operand widths — is the arm `FallbackKind.concat` (`canonicalConcat?`, `translateConcatWith`: the result wire FIRST, then the operands under the legacy hints `concat_hi`/`concat_lo`, then `{hi, lo}`) and the constructor `Term.concat : Term (.bits m) → Term (.bits n) → Term (.bits (m + n))`, with contract, protection and order inductions (the allocator-before-children pattern of the binary operators), both gates (a concatenation root takes its width from its operands) and both cone conversions; `{a, b}` on two references is a right-hand side of the back half (`simpleRhs`, `TypedExpr.cat`, `PrintShape.catRef`, renderer, name binding). The elaborator writes the result width as the SUM `m + n` and every parent's type arguments carry it; the front end folds literal `Nat` sums (`inlFoldNat`, applied after the unfolding), so a declaration containing `++` is certified through its entry constant. A LITERAL operand — `v#k ++ b`, `a ++ v#k` at the library's mixed instances, the literal written `BitVec.ofNat k v` with `v < 2 ^ k` — is the arm `FallbackKind.concatLit` and the constructors `Term.concatLitHi`/`concatLitLo`: the same sequence with the literal on a fresh `concat_const` wire allocated in the operand's place, as the legacy mixed handler emits it. The concatenation lemmas are stated over operand ACTIONS (`translateConcatActs`), so the three forms share one contract, one protection and one order proof. Two MAP IDIOMS of the IP library: `a.map (fun v => BitVec.append (0#k) v)` — zero-extension by a literal prefix — is `Term.zextMap` and the arm `FallbackKind.zextMap`, whose lowering IS the zero-extending width cast's (`{k'd0, a}`, child hint `s`), so it reuses that node's contract, protection and order lemmas through `0#k ++ x = setWidth (k + n) x`; a slice written `f <$> a` is `Term.sliceF` and the arm `FallbackKind.sliceF`, the slice map's lowering under the legacy `Functor.map` handler's child hint `a` (the slice lemmas are stated for any child hint). The front end also folds literal `Nat` DIFFERENCES, so `extractLsb' (32 - 8) 8` is a canonical slice. The gates and the view read every six-argument shape beside the canonical operators through ONE function (`sixArgShape?` / `concatView?`). | Sign extension, a concatenation whose literal operand is a numeral (`(5 : BitVec 4) ++ a`), a literal prefix other than zero inside a map, an out-of-range or zero-length slice, and symbolic widths stay on the legacy path without a general theorem. |
| `translateFallback` → canonical polymorphic-domain register | One `Signal.register initLit` root over the unified combinational domain: cycle observation and register update proved at the raw `synthesizeCombinationalCore` module (`register_step_of_env`, `trace_of_cycles`), reset held low, initialization from the declared value; `dropZeroWidthModule` proved body/width-preserving on this shape (the `SPARKLE_NO_REGDEDUP=1` configuration); the enabled register (`registerWithEnable`, hold mux) proved to the capture/hold cycle recurrence at the raw core module (`registerEnable_step_of_env`). (zero-width cleanup preserved for the plain and enabled shapes); the feedback register `Signal.loop (fun s => Signal.register initLit cone)` proved to the state-reading cycle recurrence at the raw core module (`loopRegister_step_of_env`; zero-width cleanup preserved on all three register shapes; the packaged `register_run_of_env`/`registerEnable_run_of_env`/`loopRegister_run_of_env` give the whole `runModule` trace of each shape as the source register stream, instantiated against the library `.val` streams); the two-stage shift chain `Signal.register i1 (Signal.register i2 cone)` proved likewise (`register2_step_of_env`, two-state `trace_of_cycles2`, packaged `register2_run_of_env`, zero-width cleanup preserved); the single-slot `circuit do` is recognized (`canonicalCircuitDo?`) and lowered to the byte-identical loop-form module, with source streams identified (`cdoAcc_val` via `map_fst_loop_register`) AND the general endpoint chain stated on the cdo quote form itself (`cdo_step_of_env`/`cdo_run_of_env` through the `CdoPreserves` monolith). | Sequential duplicate merge and the sequential `optimizeModule` pass-through are now covered by the PROVED rename-equivalence checker (`seqOptCheck_step_sound`/`seqOptCheck_run_sound`: k-cycle trace equivalence for accepted pairs, acceptance runtime-gated on every certified shape, composed with every certified shape's trace endpoint via `seqOptCheck_transfer` (`regAcc`/`regHold`/`accLoop`/`regChain`/`cdoAcc`/`cdo2X` `_run_optimized`), carried to the emitted-SV semantics (`seq_run_to_sv`, `*_sv_optimized`: M4 `runModuleSV` trace = source stream on every shape's optimized module) and to the parsed-back printed bytes (`seq_run_to_parsed`, `*_parsed_optimized`; the byte→AST parser is the remaining trusted step)); `circuit do` beyond the certified single-slot shape (the two-slot cross-coupled form is PROVED end to end for the returned-slot-0 shape — per-cycle and full-trace endpoints at the real entry over the state-pair recurrence; the trace is identified with the actual `circuit do` output stream via `loopPair_val`; differing widths, more slots, slot-1 return and Reg-operator reads stay open), register chains deeper than two stages and general register networks, reset muxes and the sequential SV printer step stay open; concrete-domain registers keep the legacy handler. |
| `translateFallback` → canonical sync-read memory (`canonicalMemory?` → `translateMemoryUncachedWith`) | `Signal.memory` with bare-input operands AND with unified-cone operands: gate, total lowering, monoliths (`MemoryPreserves`/`MemoryConePreserves`), whole-trace endpoints at the real entry (`memory_run_of_env`, `memoryCone_run_of_env`), the emitted-SV layer with the read latch and write program (`mem_run_to_sv`), the parsed-back printed bytes (`mem_run_to_parsed`), the composed post-pipeline (`shipping_pipeline_transfer_mem`) and the real-circuit capstones at the core AND the full entry (`memAcc_shipping`, `memAcc_shipping_full`; the cleanup/merge identity is a lawful decidable gate). | Multi-port memories, `memoryWithInit` (an arbitrary Lean function argument), the non-synthesizable combinational-read form, and concrete-domain variants keep the legacy handler. |
| `translateFallback` → `translateInstanceOrFallback` (tagged head, single-output child → `translateInstanceUncachedWith`) | Every `@[hardware_module]` call with a single-output child takes this provable arm in ANY translation (byte-equal to the legacy handler — suite-gated incl. clk/rst plumbing and repeated-call dedupe). Certified as a ROOT: the canonical combinational parent at EVERY arity (`InstanceNPreserves` over the list-quoted call `instEN`, `parentUse3_instance_entry`; the two-input instance `InstancePreserves`/`parentUse_instance_entry` additionally has its source composition observed through the linked semantics by `parentUse_entry_observes`) and the one-input sequential-child parent (`Instance1Preserves`, `parentSeq_instance_entry`; the linked per-cycle run `runH` observes the source register stream, `parentSeq_runH_observes`). Every instance statement the arm emits is width-linked (checked before emission, concluded as `Linked` in the contract; a width-generic child at a foreign width is refused instead of miscompiled). Run boundaries: `HardwareTagged`, `SubSynthDefines`, plus the parent's scalar result type (single-out cache hits are validated against the builder's own record, so no cache boundary). | Field projections of multi-output children take the sibling provable arm `translateProjInstanceUncachedWith` and are certified as a ROOT by `ProjInstancePreserves` (`parentHi_instance_entry`, source field observed by `parentHi_entry_observes`; boundaries `ProjEnvDefines`/`ProjFieldDefines`/`OutCacheEmpty`); record-RETURNING parents and a second projection of an already-emitted call fall through to the legacy handler; instance calls INSIDE cones with binder arguments on single-output combinational children are certified as cone leaves (`inst_leaf_contract`, `HierConePreserves`, `parentMix_entry_observes`: the linked evaluation observes the source); pipelines (a call whose operands are calls) are certified the same way (`hierInstRoot`, `parentNested_entry_observes`); a wrapper written at a CONCRETE clock domain (`childHW (dom := defaultDomain) a b`, the `synth_*` idiom of the IP tests) is admitted by the same spine and certified through the same endpoint (`wrapAdd_entry_observes`); calls with cone operands and sequential/Bool-output/projection leaves inside cones are gate-accepted and byte-gated but have no entry contract; nested/multiple instances, parameters, and the SV/parse layers for `.inst` statements (open-module view) remain; every single-output child shape (any arity, with or without clk/rst) is covered as a root by `InstanceGPreserves`. |
| `translateFallback` → `Rec.translateExprToWireCached` / `translateExprToWireImpl` | No blanket fallback theorem | Unfolding/type queries, application normalization, primitive and structural routes below. |
| `synthesizeCombinationalWithParameters`, symbolic dimensions | Not covered by S0–S2 endpoint | Parameter interpretation, width positivity/zero-width behavior, emitted parameter syntax and instantiated execution. |
| `synthesizeHierarchical*` / `validateDesignNames` | Name validation is implemented; the one-level linked semantics (`evalAssignsH`, per-cycle `stepAssignsH`/`runH`) and the canonical-parent forwarding theorems (`instBody_linked`, `instBody_runH`) give compiled parent/child pairs their composed meaning. | General multi-level designs, port/parameter linkage beyond the canonical shapes, and the hierarchy-aware printed text. |

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
| `handleBitVecOps`, primitive application handling inside `translateExprToWireImpl` | Concatenation and sign-extension handling require varying-width source semantics and matching AST/RTL rules (zero extension, truncation and in-range slices of the canonical map form are certified arms now — see the mux / width-changing row). The application handler has additional paths; enumerating only `handleBitVecOps` is insufficient. |
| `handleApplicative`, `handleTupleProjections`, `splitReturnLeaves`, `openRecordInputs` | General map/ap/tuple/record interfaces, flattened outputs and inputs are outside the scalar quoted endpoint. Track source-to-port mapping and multiple output observations. |
| Unit/PUnit application branches and zero-width cleanup | Successful terminator/zero-width paths are outside the positive-width theorem. Prove erasure semantics and interface behavior. |
| `handleDefinitionUnfold`, applicative normalization, canonical instance checks | Definition expansion and hardware-module recognition need explicit source correspondence; successful fallback is not ruled out by a gate miss. |
| `handleRegister`, `handleLoop`, `handleCircuitMonad` | S4: actual state/feedback path, enable/hold, initialization and supported reset behavior, then arbitrary source traces and emitted sequential execution. Circuit-monad handlers also contain structural cases; classify those individually. |
| `handleMemory` | The canonical sync-read shapes no longer reach this handler (see the memory arm above: certified end to end). The handler keeps multi-port, initialized and concrete-domain memories without a theorem. |
| Hardware-module instantiation / design cache | Canonical single-scalar-output instance parents are certified end to end for the two-input combinational shape and the one-input sequential-child shape (gate at the run's tag predicate, provable lowering byte-equal to legacy, `InstancePreserves`/`Instance1Preserves` monoliths, real-parent endpoints, linked-semantics observation of the source composition and of the source register stream), and the combinational shape is generalized to every arity (`InstanceNPreserves`), every single-output child shape is covered by `InstanceGPreserves`, and field projections of multi-output children by `ProjInstancePreserves`. Cones over instance leaves (multiple calls included) are certified in the linked semantics (`HierConePreserves`). Pipelines of calls are certified. The emitted-SV and parsed-text layers reach instance-bearing combinational parents through the linked/open bridge (`hier_pipeline_transfer`), and the optimizer on instance-bearing modules is validated by `optCheck` on the interface-extracted pair (`hier_shipping_transfer`, capstone `parentMix_shipping_opt` on the shipping text). Open: record-returning parents, cone operands of calls, sequential/multi-output cone leaves, design registration, multi-level linking, parameters, SV hierarchy layer. |

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
merging and both selections of checked optimization. For the certified
sequential shapes the passes are covered by checked steps: the sequential
duplicate merge and the optimizer by the proved `seqOptCheck` (composed as
`shipping_pipeline_transfer_merged`, instantiated at the FULL entry by
`regAcc_shipping_full`), and the memory shapes by the lawful body-identity
gate (`memAcc_shipping_full`). This is still not a universal
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

## Measured corpus coverage (2026-10-01)

The tables above say which routes HAVE a theorem. This section says how
often the repository's own designs take them. It is a measurement, not a
theorem, and it is reproducible:

```sh
lake build Tests.AllTests          # the files are run against built oleans
scripts/shipping-coverage/run.sh   # never next to a running `lake build`
```

**Method.** The compiler logs the front end of every synthesis when
`SPARKLE_PROFILE=1` (`certified front end`, `mixed certified front end`,
or the legacy start line). Pass 1 runs every file under `Tests`, `IP` and
`Examples` that contains a synthesis command and aggregates the log by
declaration. Pass 2 appends a classifier to a copy of each file: for a
declaration that only ever took the legacy route it reports whether the
gate rejected a binder, and otherwise which head constants of the body
lie outside the certified vocabulary. Declarations of the certification
tests themselves (`Tests/Compiler/Shipping*`) are counted separately so
they do not flatter the result.

**Scope of the run.** 190 files, 167 elaborate, 23 do not: unbuilt
import trees (RV32, H.264, YOLOv8 and a few others are not part of
`Tests.AllTests`), intentional error tests, and one stale file. None of
the failures comes from the compiler changes of this branch; a file that
did (the Issue #107 regression) was found by this measurement and fixed.
The designs in the unbuilt trees are the largest in the repository, so
the real share of certified compiles is, if anything, lower than below.

**Result.**

| Group | Certified front end | Legacy only | Total |
| --- | --- | --- | --- |
| Real corpus | 47 (12%) | 342 | 389 |
| Certification tests | 115 | 21 | 136 |

After the applicative arm (same day): real corpus **54** certified, 335
legacy only. The five additions are the tagged table modules of the IP
library — `SHA256.kMux`, `SHA512HW.kMux`, `keccakRcHW`, `rconHW`, `sboxHW`
— i.e. the CHILDREN of the eight `synth_*` wrappers above, so for those
wrappers both the parent and the child now pass a certified gate.

After the slice arm (same day): real corpus **60** certified, 329 legacy
only. The six additions are `synth_canopenFc` and `synth_canopenIsNmt`
(the CANopen COB-ID demultiplexer's function code and NMT decode — real
IP bodies reached through the projection wrapper), and four test
circuits (`synth_slice`, `test_extract_opcode`, `test_slice_map`,
`test_slice_upper`). Nothing left the certified set; the same 23 files
fail to elaborate.

After the concatenation arm (same day): real corpus **63** certified, 326
legacy only. The three additions are test circuits (`synth_concat`, `synth_bus_pack`, `test_concat`); no IP body is added, because the IP library concatenates inside `circuit do` bodies and mostly with a literal operand. Nothing left the certified set.

After the front-end normalisation landed (re-measured 2026-10-02, pass 1;
the reason tables below are from the run before it): real corpus **49**
certified, 340 legacy only — the two additions are the IP wrappers
`synth_droneCanNodeFilter` and `synth_mil1553Parity`; the same 23 files
fail to elaborate as before.

"Certified front end" means the gate accepted the declaration, i.e. the
syntactic precondition of the theorems holds. It does not discharge the
premises of [the trust base](ShippingCompiler-TrustBase.md). Of the 47,
39 are small operator, mux and register test circuits. The other 8 are
concrete-domain wrappers around tagged IP modules (`synth_aesSbox`,
`synth_aesRcon`, `synth_keccakRc`, `synth_sha256KMux`, `synth_sha512KMux`,
`synth_tlpHeaderByte`, `synth_tcpChecksum`, `synth_tcpHeaderByte`),
accepted since the instance spine admits a closed clock-domain argument.
For those the certified statement is about the PARENT: it is a
width-linked instance of its child. The children themselves are compiled
by the legacy front end, so their correctness stays a premise
(`ChildCorrect`). At the time of this table no IP design body was
certified end to end; the two added by the normalisation are.

**Why declarations miss the gate, as written** (337 of the 342
legacy-only declarations classified; a declaration counts once per
feature it contains):

| Feature outside the certified vocabulary | Declarations | Sole blocker |
| --- | --- | --- |
| A user definition or structure the legacy front end inlines | 250 | 30 |
| Concrete clock domain (`defaultDomain`) | 212 | 3 |
| `fun` (a lambda in the body) | 82 | – |
| `let` | 81 | 2 |
| Tuples (`bundle`, `Prod`, projections) | 62 | 1 |
| `Signal.loop` beyond the certified register shapes | 31 | – |
| `circuit do` runtime beyond the two certified shapes (`HList`, `RegList`, `Reg`) | 31 | – |
| `BitVec.extractLsb'` (slices) | 26 | – |
| `HAppend` (concatenation) | 21 | 1 |
| `Signal.fst` / `Signal.snd` | 20 / 18 | – |
| Applicative lifting (`<$>`, `<*>`, `pure`) | 16 | – |
| `Signal.memoryComboRead` | 10 | – |

Besides the body: 83 legacy-only declarations return a non-scalar
(structure or tuple) result, which no certified family produces; 21 are
rejected at a binder (a structure-typed or tuple-typed input, or a type
parameter); 9 contain instance calls in positions the instance gates do
not admit; 2 use only certified vocabulary in a shape no gate admits.

**The surface view is misleading.** The table above classifies the
declaration as written. Most real declarations are thin wrappers —
`synth_x := (someIpHW a b).field` — so on the surface 165 of them are
blocked by "a user definition" alone. That does not mean unfolding
definitions would certify them. It was tried: a prototype front-end
normaliser (delta-beta of untagged user definitions, projection of a
constructor, zeta of the lets in front of that constructor — the
reductions the legacy translator performs on the fly) was run over the
same corpus (pass 3 of the script, `normalize_tail.lean.in`).

- With delta-beta alone, 197 of the 337 declarations change and NOT ONE
  then passes a gate.
- On hand-written test shapes the same normalisation is exact: for 17
  shapes (helpers at the root, inside cones, repeated, nested, around
  registers, muxes, comparisons, loops, at a concrete domain, width-generic)
  the certified compile of the unfolded body is byte-identical to the
  legacy compile of the original.

What remains after normalisation, as blocker SETS (a declaration is
unlocked only when everything in its set is certified):

| Declarations | Blocker set after normalisation |
| --- | --- |
| 42 | `circuit do` runtime, `let`, `fun`, tuples, structures, applicative lifting |
| 30 | the same plus slices/concatenation |
| 19 | `circuit do`, `let`, `fun`, tuples, structures, slices/concatenation |
| 16 | `circuit do`, `let`, `fun`, tuples, structures |
| 15 | the 30-row set plus instance calls |
| 14 | non-scalar result and a rejected binder |
| 11 | `circuit do`, `let`, `fun`, tuples |
| … | 65 distinct sets in total |

| Feature (after normalisation) | Declarations containing it | Blocked by it alone |
| --- | --- | --- |
| `fun` | 288 | 0 |
| `let` | 273 | 6 |
| Tuples | 256 | 0 |
| Structures / remaining user definitions | 233 | 0 |
| `circuit do` runtime | 221 | 0 |
| Applicative lifting | 155 | 1 |
| Slices / concatenation | 144 | 3 |
| Non-scalar result | 83 | 0 |
| Instance calls outside the instance gates | 51 | 0 |
| `Signal.loop` beyond the certified shapes | 32 | 0 |

**What the measurement says about the remaining work.** The certified
families were built bottom-up from operators; the corpus is written
top-down: an IP module is a `circuit do` state machine over several
registers, with `let`-bound intermediate signals, applicative-lifted
operators, slices, and a structure of outputs, and the synthesised
declaration projects one field of it. No single family unlocks a
meaningful part of the corpus — every feature above is the sole blocker
of at most 6 declarations. Coverage of real designs needs these TOGETHER:

1. **Front-end normalisation** (definition unfolding, projection of a
   constructor). Cheap, exact on the tested shapes, and a prerequisite of
   everything below. DONE (`entryConst`,
   `Tools/ShippingInlineSoundness.lean`): definition unfolding and
   projection of a constructor. By itself it brings the first two real IP
   modules through a certified front end — the two combinational modules
   whose bodies are plain cones under `let` (DroneCAN node filter,
   MIL-STD-1553 parity) — and nothing else, as the blocker sets predict.
2. **The general `circuit do`**: N register slots with cross-coupled
   next-state cones, the body evaluated once for the next state and once
   for the outputs. The certified one- and two-slot shapes are special
   cases. This is the centre of the corpus (221 declarations).
3. **Hardware `let`**: the legacy handler names the wire after the binder
   and shares it through a separate cache; a certified arm has to
   reproduce both.
4. **Applicative lifting and Bool/BitVec value operators** inside
   `<$>`/`<*>` lambdas, **slices and concatenation**. DONE for the
   Bool-result binary lifts (comparisons, `&&`, `||`, `^^`) that make up
   most of the IP library's applicative uses and all of `kLut!`. Open:
   two-level bodies such as `a && !b`, unary and BitVec-result lifts.
   SLICES are DONE as a vertical unit: `x[hi:lo]` on a plain reference
   is now an IR right-hand side of the optimizer check (`simpleRhs`),
   the typed-expression layer, the printer theorems and the parse-back
   theorems, and `Term.slice` in the front half. CONCATENATION of two
   Signals is DONE the same way (`{a, b}` of two references through the
   back half, `Term.concat` in front, the width sum folded by the front
   end), and so is a literal operand (`0#k ++ a`, `a ++ 0#k` — the
   zero-extension and constant-shift idioms of the IP library).
5. **Structure and tuple results**, i.e. multi-output modules.
6. **Concrete-domain registers and memories** (the reset kind is read
   from the domain), then general `Signal.loop`, instance calls with cone
   operands, combinational-read memories.

Each item is a family in the sense of this file: a provable arm that is
byte-identical to the legacy handler, a contract, a gate, and a clause
of the bundle. None may shrink what the compiler accepts. Progress on
this list should be read from the blocker sets, not from the count of
passing declarations, which will stay near zero until item 2 lands.

### What the certified work changed on the legacy route

The dispatch arms and the legacy normalisation of `<$>`/`<*>` are shared
by both front ends, so a change there shows on legacy-route designs too.
Every generated output of the corpus is compared against the previous
compiler (`scripts/shipping-coverage/compare_outputs.py OLD/out NEW/out`
on two pass-1 runs). The applicative arm needed two changes to the legacy
`normSpine`, both pure rewritings of the expression the legacy lowering
then receives:

- the operand `Seq.seq` passes through a `Unit` thunk is beta-reduced
  where the spine is normalised (it used to be reduced at the use site);
  without this the new arm received a beta-redex and 18 IP test benches
  stopped compiling — found by the suite, never committed;
- the lifted function's binders get canonical names (they are hygienic
  macro names, different at every occurrence of the same `(· op ·)`).

Both make two occurrences of one lifted expression the same cache key, so
the legacy route now SHARES hardware it used to emit twice. Measured
against the previous compiler on 191 outputs: 173 byte-identical, 18
identical up to the numbering of fresh `_tmp_N` wires (fewer raw
statements, the same optimised text), 0 different. No design stopped
compiling and none changed its hardware; 18 changed their internal wire
numbers.

The slice arm changed no lowering — the arm emits exactly what the
legacy `Signal.map` handler emitted for the same expression — but it
changed which modules the optimizer result is KEPT for. `checkedOptimize`
keeps the optimised module of a simple (assignment-only, every
right-hand side a known shape) body only when the proved checker
accepts the pair, and otherwise ships the input module; a body that is
not simple gets the optimizer's output unchecked. With the part-select a
known shape, purely combinational modules that contain a slice became
simple, and the checker's normal form does not cover slices (it knows
constants, references and the six binary operators), so those modules
now ship UNOPTIMISED: one assignment per source operator, with the
intermediate wires declared, instead of one folded expression. Measured
against the previous compiler on 192 outputs: 182 byte-identical, 0
renumbered, 10 different, and every difference is a purely combinational
module containing a slice, e.g.

```
- assign out = (_gen_cobId[10:7] & 4'd15);
+ logic [3:0] _gen_out;
+ assign _gen_out = _gen_cobId[10:7];
+ assign out = _gen_out;
```

The files: `IP/YOLOv8/Primitives/Activation`, `Tests/CompilerTests`,
`Tests/IP/Bus/CANopenHWTest`, `Tests/IP/Bus/LINHWTest`,
`Tests/SynthesisTests`, `Tests/Synthesis/SynthCatalog`,
`Tests/TestCompilerExtensions`, `Tests/TestErrorDetection`,
`Tests/TestUnbundle2`, `Tests/TupleProjectionTest`. The hardware is the
same; the text is longer and, for these modules, it is now the text the
theorems speak about rather than an unchecked rewriting of it. This was
a policy choice put to the user (retain, as for muxes, comparisons and
casts before; the alternative is to teach the checker's normal form
slices so the folded text is kept and proved). Modules with a register,
a memory or an instance are unaffected: they were never simple.

The concatenation arm has the same two effects and no other. It fires
only on the folded form (result width a literal), which the legacy route
never sees — the declaration as written carries the sum — so no legacy
lowering changed. And `{a, b}` on two references joined the simple
shapes, so purely combinational modules that concatenate two wires and
are otherwise simple now ship unoptimised as well. Measured against the
slice compiler: 184 of 193 outputs byte-identical, 0 renumbered, 9 different — 13 modules, every one purely combinational and containing a concatenation of two wires (`IP/RV32/Bus` `busDecoderSignal`, `IP/YOLOv8/Primitives/Dequant` `dequantPacked`, `Tests/IP/Control/LQRTest` `lqrCtrlTop`, and ten test circuits in `Tests/CompilerTests`, `Tests/SynthesisTests`, `Tests/Synthesis/SynthCatalog`, `Tests/TestCompilerExtensions`, `Tests/TestUnbundle2`, `Tests/TupleProjectionTest`). This reaches further than the slice case: the legacy mixed form `{const_wire, a}` and tuple packing (`bundle2`) are also `{ref, ref}`, so tuple-returning combinational designs are retained too, and their unoptimised text shows what the optimizer used to merge — e.g. `useHalfAdder` now declares `_gen_sum` and `_gen_sum_1` for a helper the source calls twice. Same hardware function, more wires in the text; teaching the checker's normal form concatenation and slices would restore the folded text WITH a proof, and is the open alternative.

The literal-operand arm changed nothing on the corpus: 193 of 193
compared outputs byte-identical (the literal forms fire only on the
folded entry constant, and their modules were already retained through
the `{ref, ref}` shape). The certified count stays at 63: in the IP
library these idioms live inside `circuit do` bodies.

The two map idioms and the `Nat`-difference fold: 194 of 194 corpus outputs byte-identical (both arms emit what the legacy handlers emitted, and the certified count stays at 63 — the idioms sit inside `circuit do` bodies). The front-end
unfolding now also descends into the value and the body of a `let` —
without that, nothing inside a `circuit do` body was normalised at all,
which the classifier below showed.

The unary NOT and the two-level Bool lifts: 193 of 195 compared outputs byte-identical, 2 different — three purely combinational test modules whose body is a NOT of a wire (`testComplement8`, `testComplement32`, `test_not`), now retained unoptimised like the slice and concatenation cases. The lift arms themselves changed no legacy output.

### What a real `circuit do` body still needs (measured 2026-10-02)

`scripts/shipping-coverage` classifies the legacy-only declarations on
their ENTRY-normalised value. Of 324, 186 contain a `runCircuitH`: slot
counts 1 to 14 (one with 30), 815 `BitVec` slots and 153 `Bool` slots,
159 over a concrete domain. Only 18 have no other residue than the
circuit machinery itself — and those are test circuits. A real body also
needs, by number of declarations: a structure result selected by a field
projection (164), the two-level Bool lifts `x && !y` / `!(x || y)` (60),
a field of a sub-module's result (41), constants that are computed
(`2 ^ k`, `BitVec.ofInt`, 37), and `Bool`/`BitVec`-result lifts of other
shapes. The lifted functions that remain after this unit, by
declarations: `x && !y` 32, `!(x || y)` 26, `x &&& lit` 15, `x ||| y` 8,
`!x` 6. So the first real sequential module (the Goldilocks field
multiplier: five heterogeneous slots, twenty `let`s, a structure result)
needs the general `circuit do`, `let`, the result projection and the
two-level Bool lift TOGETHER.

### The machine route (measured 2026-10-02)

With the general `circuit do` on the certified route, **82 of 389
real declarations pass a gate (63 before), 19 of them on the machine
route**: the seven `circuit do` test circuits of `Tests/CircuitDoTest`,
the two `SignalLoopTest` counters, two round-trip flip-flops, the tagged
child `latch8mod` of the hierarchy tutorial, and seven IP declarations
behind their field-projecting wrappers — the CAN CRC-15, the CANopen NMT
state machine, the LIN checksum, the MIL-STD-1553 Manchester encoder,
and the AES-GCM counter, tag-fire and tag-Y registers.

The text of these modules CHANGES, by the decision recorded in the
hand-off (the certified route may differ from the legacy compile when
the function is the same): `compare_outputs.py` reports 8 files
different, 188 identical; split by module, 16 modules changed in
seven of the files and every one of them is a machine-route module — no
legacy-route module changed (the eighth file differs only in the wording
of a design-rule warning about the machine-route child `latch8mod`). What changes: one register per slot named after the handle
(`_gen_<slot>`), the transition's wires, the packed wire `_gen_out`, a
`next_gen_<slot>` wire per slot and `out` as a part-select of the packed
wire; the legacy packed loop wire and its zero-width `Unit` tail are
gone. Design-rule warnings are the same in number (the wording of the
"output is not registered" warning differs).

The function is checked two ways on five declarations
(`Tests/Compiler/ShippingMachineEntryTest.lean`): the emitted module is
run with the IR semantics for 40 cycles against the library's own
`Signal.loop` evaluation of the source, and two of them carry the
end-to-end theorem. As a one-off (a probe, not a suite test) the same
simulation was run for 60 cycles on ALL 19 real machine-route
declarations: every emitted module agrees with its source.

**With hardware `let`s kept (same day).** A classifier on the
declarations the first version refused (first failing stage of
`machineShape?`) said: 159 contain no `circuit do`; of the rest, 86 ran
out of the UNFOLDING budget — the `let`s — 22 failed on reset values, 15
at the gate, 14 are not a `circuit do` at the root. With the `let`s kept
as binders and fields (`closeLets`), **111 of 389 real declarations pass
a gate, 48 on the machine route**, with 1 to 10 slots and up to 60
`let`s: beside the nineteen above, the I²C, SPI, SBUS, CRSF, DroneCAN
and UART engines, HKDF, RLP, and the P-256, secp256k1 and BLS12-381
field and Miller-loop controllers, each behind its field-projecting
wrapper. Against the previous commit 36 modules changed text (19 of 197
files), every one a machine-route module (29 newly on the route, 7
already on it whose `let`s are now wires); against the compiler before
the machine route, 45 modules in 22 files. All 48 emitted modules agree
with their source in the 60-cycle IR simulation, and the run status of
every corpus file is unchanged. In the raw module every source `let` is
a wire `_gen_<name>`; the optimizer that runs before printing resolves
such an alias to the wire that drives it, so the printed text shows the
driver's name.

What the same classifier says about the 278 that remain, reading the
`let`s as the compiler now does: 159 without `circuit do`; 8 that need
only a structure result (the 29 scalar ones it predicted pass now); 89
refused at the gate — by what the refused
expressions contain: computed constants (`2 ^ k`, `BitVec.ofInt`,
negation, `allOnes`, about 25 declarations), a sub-module call inside the
body (16), register reads spelled through other library forms (17), a
Lean-level `if` on constants (6), and 24 with no foreign head at all
(unsupported shapes of supported operators).

**With structure results (same day).** 118 of 389, 55 on the machine
route, 7 of them declarations whose result is a structure — one module
with one output port per field: `pairRecordCdo`, the `pe` child of the
multi-instance test, and five tagged sub-modules of the ECDSA, P-256 and
FIDO2 demos (Montgomery multipliers, UART transmitters). Only these
change text against the previous commit (most are children written to
design files; one is in the compared output). All 55 machine-route
modules agree with their source, every output port, in the 60-cycle IR
simulation; the run status of every corpus file is unchanged.

"On the machine route" is a statement about the ROUTE: the module was
produced by the proved harness and the proved IR passes. The end-to-end
theorem — emitted-module trace = source declaration at every cycle — is
instantiated for three declarations (`mThree`, `linChk`, and the IP
declaration `IP.Bus.LINHW.checksumHW` with both ports). For the others
the simulation is the evidence that the reading of the source
(`machineShape?`) is right; the generic theorems apply once the quoted
term and the source recurrence are supplied, which today is written per
declaration.

What still blocks the rest, by the refused expression (classifier
`mach3_tail`): constants computed in Lean (`BitVec.ofInt` of an `Int`
expression, `2 ^ k`, sums and differences: about 25 declarations), a
BitVec operator lifted through `<$>`/`<*>` or a `map` with a literal
(about 17), user constants that are not unfolded (state encodings such as
`sClosed`: about 10), a sub-module call inside the body (16), `~~~` on a
BitVec Signal (3).

A regression found by this measurement, not by the suite: the first
version re-ran the unfolding inside `synthesizeFromConst`, before the
memo lookup, and a design with many sub-module references
(`EcdsaSignDemoTest`) ran out of heartbeats. The machine test now reads
the entry constant (`entryConst` unfolds once and keeps the unfolding
when it is a machine shape), so a declaration that is not a machine
costs one cheap shape test.
