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
| `synthesizeCombinationalCoreWith` → `entryConst` (front-end normalisation) | The entry hands `synthesizeFromConst` the declaration as read when a gate accepts it, and the declaration with its untagged user definitions unfolded (`userInliner`: pure delta-beta of untagged user definitions, `<$>`/`<*>` at the library's Signal instances as `Signal.map`/`Signal.ap` with canonical binder names, and projection of a user structure's field out of the constructor its record head-normalises to — zeta of the lets in front, which is what the legacy projection handler's `unfoldDefinition?`/`whnf` loop does to `(ipHW a b).field` — against the run's environment, total, node-budgeted) when the original misses both gates and the unfolding passes one. Every family theorem then applies to that entry constant verbatim (`synthesizeCombinationalCore_entry_sound`, the whole bundle); real helper-structured declarations are certified end to end (`useSel_execution`, `accH_run`) under the boundary `EntryDefines`, and so are the FIRST TWO REAL IP MODULES: the DroneCAN node filter and the MIL-STD-1553 odd-parity generator, compiled through the field-projecting wrapper their test benches use (`nodeFilter_execution`, `oddParity_execution`: the module computes the IP definition's own output stream; `*_library` identify the IP definition with the quoted term by `rfl`). Byte-identical to the legacy route on 21 + 18 declarations (suite-gated), the latter including the AES S-box and round-constant tables of the IP library; `rcon_execution` proves the round-constant table end to end. | Reducible definitions, universe-polymorphic helpers and library projections (`Prod.fst`) are not unfolded; one refused node (`∀`, metadata, a primitive projection) abandons the whole normalisation; only the unified combinational and the feedback-register endpoints have `_of_entry` twins so far (the other families are reached through the bundle). |
| `synthesizeFromConst` → `certifiedShape?` → `synthesizeCertified` | S0: quoted positive-width BitVec fragment, `compiledFragment_execution` | Extend source/interface forms outside this gate without treating refusal by this gate as compiler failure. |
| `synthesizeFromConst` → `mixedCertifiedShape?` → `synthesizeMixedCertified` | S1/S2: Bool inputs/literals, canonical `&&&`/`|||`/`^^^`/`~~~`, `ult`/`ule`/`slt`/`sle`, standard BitVec/Bool `beq`, Bool-result mux over common-width BitVec operands; BitVec mux trees via `ShippingVectorMuxSoundness.execution_source_of_env` | Extend operations/results and recursive width invariants. |
| Both shape gates miss → existing synthesis/cache path | No general source-to-shipping-RTL theorem. MEASURED: 342 of the 389 real-corpus declarations take this route (see "Measured corpus coverage"). | Reconcile source opening, normalization, output leaf splitting, cached submodules and all successful legacy handlers, in the order the measurement gives. |
| `translateStepWith` → `translateCore` | Existing fragment's literals, inputs and eight binary operations; mixed order proof reuses protected pending names | Other supported surface forms must be related to the quoted source, not assumed equal. |
| `translateFallback` → Bool control/cache path | Current quoted Bool domain, including validated cache hit/miss behavior. APPLICATIVE-LIFTED Bool-result operators — `(BitVec.ule · ·) <$> a <*> b`, `ult`/`slt`/`sle`, `(· == ·)`, `(· && ·)`, `(· || ·)`, `(· ^^ ·)`, in the form the front end normalises them to, `Signal.ap (Signal.map f a) b` — take this arm (`appBoolOp?`, `translateAppCompare`/`translateAppBoolBinary`: operands under the legacy applicative hint `app_arg`, then the direct route's result assignment); they are `Term.appCompare`/`Term.appBool` of the unified domain, with the full contract, protection and order inductions, both gates, and both `circuit do` cone conversions; `kLut!` table muxes are certified through them. Numeric literals (`Signal.pure 5` at `BitVec.instOfNat`) are `Term.bitsNum`. | Lifted functions whose body is not one operator on the two variables (`fun s l => s && !l`, `x.toInt > y.toInt`), unary lifts, BitVec-result lifts (`(· &&& ·) <$>`), and Bool surface forms/custom instances keep the legacy handlers. |
| `translateFallback` → cached literal-width BitVec mux / width-changing map | Unified `Term`: mutual composition of muxes below/above arithmetic and comparison parents at either result sort, via `ShippingUnifiedExecutionSoundness.execution_source_of_env`, including validated cache hit/miss and record preservation; per-operation mixed widths and canonical width-changing maps (`Signal.map (BitVec.setWidth w)`/`zeroExtend` at literal positive widths — zero-extension, truncation and equal-width casts) are covered through the same endpoint. | Sign extension, general slice/concat surface operations and symbolic widths stay on the legacy path without a general theorem. |
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
| `handleBitVecOps`, primitive application handling inside `translateExprToWireImpl` | Slices, concatenation, zero extension/truncation and sign-extension handling require varying-width source semantics and matching AST/RTL rules. The application handler has additional paths; enumerating only `handleBitVecOps` is insufficient. |
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
   Slices and concatenation are NOT front-half work: `x[hi:lo]` on a
   plain reference and `{a, b}` of two references are IR right-hand sides
   the optimizer check (`simpleRhs`), the typed-expression layer, the
   printer theorems and the parse-back theorems do not cover yet.
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
