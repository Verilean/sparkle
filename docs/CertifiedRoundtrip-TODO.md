# Certified-roundtrip — open work

Living checklist for the certified-compilation track (branch
`poc/roundtrip-proof`, PR #134).  Grouped by area; ordering within a
group is rough priority.  Update as items land.

## Current shipping compiler TODO

Updated 2026-09-28, S2 at `075e9f4`; S3 comparisons, Bool logic/equality and BitVec mux trees connected. This section is the current
execution checklist for the CompCert-style **existing successful compiler**
goal. The older sections below retain historical/per-instance tracks; their
“next” items do not override this list. Milestone definitions and exit criteria:
[ShippingCompiler-Milestones.md](ShippingCompiler-Milestones.md).

### Completed foundations

- [x] **S0:** Original BitVec fragment connected through actual output syntax,
  bound/unique declarations, SV equations and finite delta settling
  (`compiledFragment_execution`).
- [x] **S1:** Mixed Bool/BitVec recursive translation and actual synthesis entry,
  cleanup, checked merging and optimizer selections preserve source IR values.
- [x] **S1:** Mixed output text has concrete grammar, legal unique declarations,
  declaration-derived widths and all references/targets bound
  (`syntax_source_of_env`, `2ad67ae`). The old BitVec theorem remains valid.

### Completed: S2 — mixed RTL meaning and finite settling

Owner/status: complete. Endpoint: `execution_source_of_env` in
`Tools/ShippingMixedExecutionSoundness.lean`; initialization bounds and
`EnvDefines` remain explicit.

- [x] Derive per-expression and assignment SV semantic checks from the mixed
  AST's actual declaration widths, including the Bool output; connect both
  checked optimizer selections.
- [x] Derive dependency order/single-assignment for mixed recursive translation,
  including parent-before-child allocation, protected pending names, cache hits,
  live Bool/BitVec bindings and the final output assignment.
- [x] Carry these facts through the actual cleanup/merge/optimizer pipeline.
- [x] Compose a general source-to-emitted-RTL theorem with unique bounded
  solution and finite delta-trace existence/convergence, retaining the same
  concrete text/AST and explicit `EnvDefines` boundary.
- [x] Instantiate that endpoint on real sources, audit its axioms and pass the
  full test-module build. No caller-supplied child/order/replay certificate.

S2 now includes the RTL execution theorem, beyond IR values and grammar.
Intermediate commits are checkpoints, not automatic turn/task endpoints.

### Active S3 and planned extensions / final closure

- [x] **S3 / signed comparison:** Generalize the actual recursive comparison
  path to `Signal.slt`/`Signal.sle`; derive operand sign widths; connect emitted
  sign-bit-bias syntax, selected IR and finite RTL settling. The same
  `execution_source_of_env` now covers this extension. Real nested-source
  instantiation and 2,250 source/legacy/SV/delta cases at widths 1/8/65 pass the
  full 623-job build and standard-axiom audit. This does not close all of S3.

- [x] **S3 / standard BitVec equality:** Connect the actual `Signal.beq`
  type/instance arguments and recursive comparison to `execution_source_of_env`.
  Standard equality is proved through syntax and finite settling; arbitrary
  custom BEq is outside the theorem. Fix the legacy applicative shortcut's
  custom-BEq miscompilation and add constant/reordered-instance regressions.
  `ShippingEqualityTest` instantiates the general endpoint on a real nested
  source and checks 2,250 execution cases plus 32 custom-instance cases.
- [x] **S3 / canonical Bool logic and equality:** Connect library Bool
  `&&&`, `|||`, `^^^`, `~~~` and standard Bool `Signal.beq` through the actual
  recursive compiler, syntax and finite RTL settling. Preserve cache determinacy
  and separation from BitVec meanings. Instantiate the general endpoint on
  mixed nested sources. Other overloads and mapped/unfolded forms remain open.
- [x] **S3 / BitVec mux trees:** `VExpr` covers same positive-width nested mux
  branches, existing arithmetic leaves and existing `BExpr` conditions. The
  actual recursive translation, source entry, output grammar/binding and finite
  RTL settling are connected by `ShippingVectorMuxSoundness.execution_source_of_env`.
  Backend output invariants now carry arbitrary width; existing Bool wrappers
  remain valid. Real nested-source theorem and 2,772 source/legacy/SV/delta cases
  at widths 1/8/65 pass the standard-axiom audit.
- [x] **S3 / mutual source and cache foundation:** `ShippingUnifiedSource`
  defines one typed recursive language for Bool and BitVec, preserving the old
  FExpr/BExpr/VExpr quotations, values and well-formedness. `ShippingUnifiedMeaning`
  connects it to actual library Signal observations and proves one value/type
  per Lean expression, including Bool versus BitVec 1. `ShippingUnifiedCache`
  and `ShippingUnifiedInvariant` prove actual validated-cache hit/miss and
  record-update preservation, including execution, typed body and live-wire
  values, conditional on the uncached lowering contract. Allocation and final
  assignment to a reserved name have preservation lemmas too.
- [x] **S3 / mutual mux composition:** Done. `ShippingUnifiedRecursion` closes
  the actual fuel recursion over the whole mutual `Term` domain (inputs,
  literals, all eight binaries, comparisons, Bool logic/equality/negation and
  both mux sorts), deriving the reserved-parent `inputSafe`/`recordSafe`
  hypotheses of `Inv.emit_reserved` from child frames. `ShippingUnifiedProtection`
  closes pending-parent protection and dependency order for every node kind,
  including validated cache hits. `ShippingUnifiedEntrySoundness` connects the
  contract to real output emission; `ShippingUnifiedExecutionSoundness` adds the
  extended `unifiedGateRoot` acceptance in `mixedCertifiedShape?` and the general
  `execution_source_of_env` endpoint for either result sort.
  `ShippingUnifiedSourceTest` instantiates the endpoint on real nested,
  comparison-root and width-65 arithmetic-root declarations and keeps the
  2,322 source/legacy/SV/delta regression cases, now through the certified gate.
- [x] **S3 / vector mux reuse:** Done. `translateFallback` now routes
  literal-width vector muxes through the shared validated cache wrapper
  (`translateControlCachedWith` over the new `translateVectorMuxUncachedWith`):
  a hit is checked against the recorded expression and justified by the unified
  `Meaning`/`Records` invariant, a miss lowers and records. The unified fuel
  contract, protection and order inductions cover the cached mux node; the old
  `VExpr` endpoint keeps its statement and is now derived from the unified
  endpoint through the `ofV` embedding. Repeated mux subtrees share wires.
- [x] **S3 / per-operation mixed widths:** Done. The unified `Term` is now
  width-indexed (`SType.bits w`): different subtrees may use different positive
  BitVec widths while each canonical operation keeps a common operand width.
  One fuel contract/protection/order induction covers all widths at once; the
  endpoint `execution_source_of_env` takes a per-input width assignment `vw`.
  The recognizers already checked widths per node, so no compiler change was
  needed. `mixedWidth` (an 8-bit comparison controlling a 65-bit mux) is
  gated, executed against 54 SV cases and instantiates the endpoint.
- [ ] **S3:** Build a branch/feature coverage inventory of the actual compiler's
  successful entry/dispatcher/pass paths; identify exact uncovered cases.
  [Initial structural inventory](ShippingCompiler-Coverage.md) added; detailed
  success witnesses and exhaustive branch reconciliation remain open.
- [x] **S3 / width-changing operations (setWidth):** Done. The canonical
  `Signal.map (BitVec.setWidth w)` / `zeroExtend` form at literal positive
  widths now has a total certified lowering in `translateFallback`
  (`translateSetWidthUncachedWith`, sharing the validated cache wrapper):
  zero-extension emits `{k'd0, x}`, truncation the size-cast `w'(x)` encode,
  equal widths a plain alias. `Term.setw` extends the unified source; the
  RTL chain (`simpleRhs`/`TypedExpr`/`PrintShape`/renderer/grammar/binding/
  zero-width/merge) accepts both IR shapes; `checkedOptimize` keeps cast
  bodies unchanged (`checkedOptimize_cast`, like the control branch). Gated,
  72 SV execution cases (`widen`/`narrow`/`rewidth`/`widenAdd`), endpoint
  instantiated at 8→16, 65→8 and mixed widths. Sign extension is excluded
  (legacy narrowing path is not certified).
- [ ] **S3:** Remaining combinational operations and interfaces: remaining mux forms,
  remaining Bool surface forms/comparison/shift paths, sign extension and general
  slice/concat surface operations, successful
  aggregate and parameterized/symbolic forms. Close syntax and RTL meaning for
  each extension; inventory determines the complete list.
- [x] **S4 / first unit — one register over the unified domain:** Done. The
  canonical polymorphic-domain `Signal.register initLit input` root has a
  total lowering (`canonicalRegister?`/`translateRegisterUncachedWith`, child
  first, shared clk/rst, asynchronous kind = the legacy fallback for a
  polymorphic domain; concrete domains keep the legacy handler) and a gate
  disjunct (`unifiedRegisterRoot`). `Tools/ShippingRegisterSoundness.lean`
  proves, from the real core entry (`synthesizeCombinationalCore`, the raw
  module of the `SPARKLE_NO_REGDEDUP=1` configuration): each cycle with
  admissible inputs and reset low observes the current register value on
  `out` and steps the register by the unified source cone's value
  (`register_step_of_env`); `trace_of_cycles` iterates it along `runModule`
  for the full trace from the declared initial value. The source register has
  no reset primitive, so reset is held low; asserting it re-initializes RTL
  state (outside the source's meaning). 12-cycle numeric regression and a
  standard-axioms endpoint instantiation in `ShippingRegisterSoundnessTest`.
- [x] **S4 / zero-width cleanup on the register shape:** Done. On the
  certified register module, `dropZeroWidthModule` is proved to preserve the
  body and the whole width environment (every assign target and reference
  has a positive declared width; the register input is a plain ref; `out` is
  a positive-width output port), so the cycle/trace theorems transfer to the
  cleaned module — the full `SPARKLE_NO_REGDEDUP=1` configuration of
  `synthesizeCombinational`. The two facts are part of
  `register_step_of_env`'s conclusion.
- [x] **S4 / enable-hold register:** Done. The canonical polymorphic-domain
  `Signal.registerWithEnable initLit en input` root has a total lowering in
  the legacy handler's exact order (enable cone, input cone, hold-mux wire,
  register fed by the mux, mux assignment reading the register back) and a
  gate disjunct; the cycle theorem `registerEnable_step_of_env` proves each
  admissible cycle observes the current value on `out` and updates by the
  capture/hold recurrence (matching the fixed source semantics from main's
  d53d5a9), with a width-bounded register seed; the generalized
  `trace_of_cycles` (state-reading updates) iterates it over `runModule`.
  12-cycle capture/hold regression and endpoint instantiation with standard
  axioms in `ShippingRegisterSoundnessTest`.
- [x] **S4 / feedback register:** Done for the single-register loop. The
  canonical `Signal.loop (fun s => Signal.register initLit cone)` root over
  a polymorphic domain has a total lowering (`canonicalLoopRegister?` +
  `translateLoopRegisterUncachedWith`: the register output wire is allocated
  FIRST, the loop binder is bound to it — with a collision guard on the
  fresh binder id — the cone is translated reading it back, then the
  statement-only `emitRegisterStmt` closes the loop) and a gate disjunct
  (the loop binder is one more width-`w` input pushed onto the gate kinds).
  `synthesizeMixedCertified_loopRegister_sound`/`loopRegister_step_of_env`
  prove, at the real core entry: each admissible cycle with reset low and a
  width-bounded state observes the current value on `out` and steps the
  register by the cone evaluated AT the current state (the loop binder is
  unified-source input `kv`); no protection lemmas are needed — the register
  wire is used before the cone translates, so the execution frame preserves
  it. `trace_of_cycles` (state-reading updates) iterates it over `runModule`.
  `accLoop` passes the gate definitionally and 12 feedback cycles match the
  loop recurrence; endpoint instantiated, standard axioms only. Zero-width
  cleanup is proved preserved on this shape as well, so all three certified
  register shapes cover the `SPARKLE_NO_REGDEDUP=1` configuration. The
  packaged trace endpoint `loopRegister_run_of_env` (via the
  invariant-carrying `trace_of_cycles_inv` and the general
  `loop_register_val` stream lemma) closes the full-run statement: for
  every admissible seeding discipline, the compiled `runModule` trace
  observes exactly the source `Signal.loop` register fixpoint's stream
  (`accLoop_run` instantiates it against the library `.val` stream). The
  plain and enabled shapes have the same packaged trace endpoints
  (`register_run_of_env` via the state-ignoring `trace_of_cycles`,
  `registerEnable_run_of_env` via `trace_of_cycles_inv` with the width
  bound as the invariant, and the definitional `registerWithEnable_val`
  stream recurrence); `regAcc_run`/`regHold_run` instantiate them against
  the library `.val` streams, so all three certified register shapes now
  expose the full `runModule` trace as the source stream.
- [x] **S4: multiple registers — the two-stage shift chain.** The gate's
  register root now also accepts one cascaded register stage
  (`Signal.register i1 (Signal.register i2 cone)`, same width both
  stages); the translation itself was already recursive, so the compiler
  is unchanged apart from the gate disjunct. The monolith
  `synthesizeMixedCertified_register2_sound` decomposes BOTH fuel-fixpoint
  levels (outer register at fuel 1048575, inner at 1048574, cone contract
  at 1048574), kills both validated cache hits against the empty prepared
  record, and proves the two-register cycle: `out` observes the outer
  register, the outer register shifts in the inner one's (width-bounded)
  value, and the inner register steps by the cone; zero-width cleanup is
  proved to preserve the shape. `register2_step_of_env` exposes it at the
  real core entry, `trace_of_cycles2` iterates the two-state recurrence,
  and `register2_run_of_env` packages the full trace (`regChain` test:
  gate acceptance, 12-cycle regression against both registers, endpoints
  instantiated against the nested library `.val` streams, standard axioms
  only). Deeper chains (three or more stages) are gate-rejected and stay
  on the legacy handler.
- [x] **S4: `circuit do` reification, phase A (groundwork).** The
  `circuit do` macro now destructures the `RegList` handle tuple with
  `Prod` projections (`.1`/`.2` `let`s) instead of pattern `let`s: a
  pattern `let` compiles to a per-declaration auxiliary matcher constant
  that a pure shape recognizer cannot see through (and accepting
  arbitrary constants in that position would risk miscompiling sources
  the legacy path correctly rejects), while the projection form is the
  definitionally-equal plain term. Verified by rebuilding every
  circuit-do consumer. The source-level anchor lemma
  `map_fst_loop_register` identifies the reduced single-slot
  `runCircuitH` state (`map Prod.fst` of the loop over
  `bundle2 (register …) (pure ())`) with the plain certified
  feedback-register stream. Phase B (landed): `canonicalCircuitDo?` purely recognizes the
  single-slot `runCircuitH` application (polymorphic domain, one
  `BitVec w` slot, projection-destructured handle, one write, the
  register's own read returned), `cdoConeToLoop` rewrites the cone into
  the loop-binder form (coerced `Prod.fst _ _ r` reads become the
  binder; the vanished `RegList` binder index is squeezed out; any other
  use of the handle rejects), and `translateCircuitDoUncachedWith` plus
  a gate disjunct route it through the certified feedback-register
  lowering. The synthesized module is IDENTICAL to the explicit
  `Signal.loop` form (checked statement-for-statement in the register
  test), and `cdoAcc_val` identifies the source streams definitionally
  through `map_fst_loop_register`, so the loop cycle/trace theorems
  transfer to `circuit do` sources of this shape. The general endpoint chain is now
  stated on the circuit-do quote form itself: `cdoE` transcribes the
  elaborated single-slot `runCircuitH` application exactly (the register
  `let` binder name is a parameter; the macro's continuation binder was
  hardened to the hygiene-free `_cdoK`, since `Expr` equality compares
  binder names), the pattern-match `canonicalCircuitDo?` recognizer is
  proved on it, `cdoConeToLoop_quote` distributes the read-normalizer
  over the unified quote, and the `CdoPreserves` monolith (the loop
  monolith across the same fuel decomposition) feeds
  `cdo_step_of_env`/`cdo_run_of_env` — instantiated on the real
  `circuit do` declaration (`cdoAcc_step`/`cdoAcc_run`, standard axioms
  only). Multiple slots have their compiler
  phase: `canonicalCircuitDo2?` purely recognizes the TWO-slot
  `runCircuitH` (same-width slots, projection-destructured handles, one
  write per register, one register's read returned), `cdo2ConeToLoop`
  rewrites both cones into the two-state form (slot 0 at `.bvar 1`,
  slot 1 at `.bvar 0`; cross-register reads are the explicit
  `(x : Signal dom (BitVec w))` ascription coercions real designs already
  use), and the lowering allocates and binds both register wires before
  either cone translates, so cross-coupled cones work; gate-accepted and
  pinned by a 12-cycle two-register regression. The two-slot PROOF chain is
  closed on the quote form for the returned-slot-0 shape: `cdo2E`
  transcribes the elaborated call (domain at seven binder depths, user
  register-let names, the returned read as a parameter), the shallow
  pattern-match recognizer's acceptance is proved through the two-state
  `cdo2ConeToLoop_quote` distribution, the `Cdo2Preserves` monolith
  replays the feedback monolith with doubled self machinery (an explicit
  propositional distinctness guard between the fresh slot binders — the
  monolith needs it as a proof fact) and chains the second cone's
  contract from the first's outcome invariant, and
  `cdo2_step_of_env`/`trace_of_cycles2_inv`/`cdo2_run_of_env` expose the
  per-cycle and full-trace theorems at the real entry, instantiated on
  the real declaration (`cdo2X_step`/`cdo2X_run`, standard axioms only).
  The source-level identification is
  also closed: `loopPair`/`loopPair_val` show the reduced two-slot
  `runCircuitH` state's projected register streams follow the mutual
  cone recurrence (proved directly from `loopGo_eq`, no induction —
  both sides reference the same fixpoint), and `cdo2X_run_val`
  instantiates the packaged trace endpoint against the actual
  `circuit do` output stream, the declaration being definitionally
  `map Prod.fst` of the packed loop pair. Still open: the
  returned-slot-1 mirror, slots at differing widths, more than two
  slots, and cones whose reads go through the Reg-lifting operator
  instances.
- [ ] **S4:** Remaining state/reset scope: the sequential `mergeDuplicates`
  (the UNVALIDATED `mergeDuplicatesRaw`; needs register-bisimulation
  validation or proof — the register test exercises the merged default
  configuration numerically for 12 cycles). Groundwork landed:
  `mergeDuplicates_seq` proves the shipped sequential merge IS the raw
  merge (the validated path only covers pure-assign bodies), and the raw
  merge is checked to be the IDENTITY on all five certified register
  modules in the register test (the translator's expression cache leaves
  no duplicate nodes, so the partition refinement ends discrete). The
  remaining obligation for carrying the register theorems to the default
  configuration is a structural proof of that identity on the certified
  shapes (reasoning through the imperative partition-refinement loop),
  or a sound rename/alias bisimulation checker for the general merge;
  a premise-based default endpoint does not work because the core module
  is existential in `synthesizeCombinational_reads`' decomposition.
  BOTH sequential trust gaps are now closed by one proved checker: the
  rename-equivalence checker `seqOptCheck` (Sparkle/IR/OptCheck.lean)
  pairs the registers of two sequential modules in body order (same
  clock/reset/kind/init/width, outputs possibly renamed), treats
  register outputs as width-fitting inputs, normalizes both assign
  segments with the mux-aware `seqNormE`, and accepts when every module
  output and every register's next-value expression agree under the
  renaming. It takes no part in the pipeline; the register test gates
  that it accepts, on every certified shape, both the optimizer's
  output (the sequential printed-SV gap) and the sequential merge. Its
  soundness is PROVED (Tools/ShippingSeqOptSoundness.lean, standard
  axioms only): `seqOptCheck_step_sound` (one cycle: both modules step,
  outputs agree, register updates pair name-for-name with equal,
  width-bounded values; the accepted module's environment is any env
  agreeing with the σ-renamed original on its reference domain) and
  `seqOptCheck_run_sound` (k-cycle `runModule` trace equivalence under
  the canonical `seedIn` seeding, by induction with the register-state
  coupling as the invariant). `accLoop_run_optimized` in the register
  test composes it with the loop-register trace endpoint: any
  checker-accepted module — in the real pipeline `optimizeModule` of
  the merged module, whose acceptance the runtime gate pins — runs and
  observes the same source stream. The composition is done for ALL SIX
  certified shapes (`regAcc`/`regHold`/`accLoop`/`regChain`/`cdoAcc`/
  `cdo2X` `_run_optimized`, via the packaged `seqOptCheck_transfer`),
  each audited to standard axioms. The chain now also reaches the
  EMITTED SV SEMANTICS: Tools/ShippingSeqSVSoundness.lean proves the
  checked module's IR trace (at the checker's `declWidth` environment)
  equals the emitted Verilog's `runModuleSV` trace (M4 `seqCheck`
  fragment at the emitter's `weOf∘moduleWof` environment) — via a
  reference-domain width congruence (`runModule_we_congr` over
  `seqNames`) and the M4 capstone replayed with a boundedness invariant
  (`forward_trace_inv`), packaged as `seq_run_to_sv`; the register test
  gates `seqCheck` acceptance and the width agreement on all six
  optimized modules and instantiates `*_sv_optimized` for every shape
  (standard axioms). The BYTE-level connection is closed in the
  PARSE direction: the emitted SV AST cannot carry the asynchronous
  reset sensitivity (`SVSensitivity` holds a single edge), so instead
  `seq_run_to_parsed` proves the module the shipping parser reads back
  from the actual printed Verilog (`parseAndLowerHierarchical ∘
  emitModule`) is trace-equal to the checked module — through the
  roundtrip census (`bfragCheck_sound`/`body_trace_roundtrip`), a
  clamped twin of the canonical seeding (`seedInC` + a seed congruence
  on width-bounded states), and the width congruence; the register test
  PARSES the real printed text of all six optimized modules, gates
  `semFragCheck`/`bodyImage`/`bodyReorderCheck`/fragment membership, and
  instantiates `*_parsed_optimized` per shape (standard axioms). The
  remaining trusted step for sequential text is the parser/lowering
  itself (byte→AST), the same boundary the corpus roundtrip validation
  accepts; a render-direction proof would need the SV AST extended with
  compound sensitivities. Also open in S4: user-level reset muxes and
  the remaining shape breadth below.
- [ ] **S5:** Actual memory compilation and trace semantics, including latency,
  masks and supported read/write interactions. STARTED — the semantics
  layer of the canonical shape is proved (Tools/ShippingMemorySoundness
  .lean): `Signal.memory` over direct input operands compiles to the
  pinned single-port sync-read body (`memBody`: one `.memory` statement,
  `rdata` latch, `out := rdata`), and `memStep`/`trace_of_cycles_memArr`
  /`memory_run`/`memory_run_val` prove its whole `runModule` trace IS
  the source `Signal.memory` stream (read-old latch = `memState` at the
  masked address, enabled writes landing masked, `BitVec` bridge via
  `ofNat_toNat`/`setWidth_eq`); the test pins the compiled body
  byte-for-byte, runs a 12-cycle regression, instantiates the endpoint
  on the pinned shape, and audits standard axioms. The ENTRY-LEVEL
  connection is now PROVED (Tools/ShippingMemoryEntrySoundness.lean):
  the gate disjunct `unifiedMemoryRoot` + total lowering
  `translateMemoryUncachedWith` route the canonical shape through the
  certified front end (byte-identical output, corpus regression green),
  and the monolith `synthesizeMixedCertified_memory_sound` — the four
  operand translations are pure input reads (state unchanged, pinned by
  `translateStep_fvar_returns` + `prepare_const` valuation transport),
  the emitter appends exactly the `.memory` statement and `rdata` wire —
  yields `memory_body_of_env`/`memory_run_of_env`: the real entry's
  module IS `memBody` and its whole trace observes the source stream
  (`memAcc_peel`/`memAcc_run` instantiate on the real declaration,
  standard axioms). CONE OPERANDS are also proved: the gate
  admits all four operands through the unified combinational grammar
  (`unifiedMemoryRoot` over `unifiedGateBitsBody`/`BoolBody`), the
  four-child monolith chains the unified contracts (frames, invariants
  and orders threaded four deep — operand values settle in the
  elaborated pre-body and feed the latch/write masked), and
  `memoryCone_step_of_env`/`memoryCone_run_of_env` expose per-cycle and
  whole-trace endpoints, instantiated on a real declaration whose write
  data is an arithmetic cone (`memAccC` = `Signal.memory wa (a+b) wen
  ra`; `memAccC_peel` by rfl, `memAccC_run` identifies the trace with
  `Signal.memory` over the cone SIGNALS, standard axioms). The sequential post-processing passes
  (`dropZeroWidthModule`, `mergeDuplicatesRaw`, `optimizeModule`) are
  gated to be the IDENTITY on both certified memory shapes, so these
  endpoints describe the exact module the pipeline prints. Open in S5: `memoryComboRead` (source
  marks it non-synthesizable), `memoryWithInit`, multi-port shapes, and the
  `seqOptCheck` route for memory bodies (it excludes memories). The
  emitted-SV layer for SYNC-READ memories is now PROVED
  (Tools/ShippingMemSVSoundness.lean, additive over the M4 core): the
  extended checker `seqCheckM` (assigns + registers + single sync-read
  memories with checked read address and the M4 write-port payload
  conditions), a mixed sequential-update list carrying register
  drivers AND read latches (`emitSeqNexts`/`seqNextsSV`), phase lemmas
  cloning `emit_sem_regs`/`emit_sem_memNexts`, and the capstone
  `certified_forward_trace_mem`: on checked bodies the emitted
  Verilog's trace (`runModuleSVM`) is the IR's, every cycle. The test
  gates `seqCheckM` acceptance on both certified memory modules
  (standard axioms). The seedIn-style INVARIANT capstone is
  also in place (`forward_trace_mem_inv`, with `regNextsM_bounded`
  masking registers AND latches — the checker pins each latch name at
  the data width), so the canonical seeding qualifies directly.
  The memory TEXT route is now CLOSED at
  the emitted-SV level: the reference-domain width congruence for the
  memory fragment (`seqNamesM`, the `…M_we_congr` chain under
  `memOpsRefs` — gated operands are plain references, so write-port
  and latch evaluation is width-free), the `mem_run_to_sv` wrapper,
  and the per-declaration endpoints `memAcc_svm`/`memAccC_svm`: the
  real modules' emitted Verilog objects run to the source
  `Signal.memory` stream (gates pin `seqCheckM`, reference-only
  operands and the entry/emitter width agreement; standard axioms).
  The byte→AST parse direction is
  ALSO closed for memories (`mem_run_to_parsed` + the per-declaration
  `memAcc_parsed`/`memAccC_parsed`: the module the shipping parser
  reads back from the REAL printed bytes runs to the source stream;
  the test gates run the parser on the actual text and pin
  `semFragCheck`/`bodyImage`/`bodyReorderCheck`/`seqCheckM` of the
  parsed body). The memory pillar now matches the register pillar end
  to end: source → entry → pipeline-identity → emitted-SV semantics →
  parsed-back printed bytes, with the byte→AST parser step as the
  retained base.
- [ ] **S6:** Actual hierarchy compilation and compositional instance semantics,
  port/parameter linkage and contained state/memory. STARTED — the
  combinational linked-semantics layer exists
  (Tools/ShippingHierarchySoundness.lean): `evalAssignsH` gives `.inst`
  statements their LINKED meaning (the child's outputs are the standard
  evaluation of its own body on the connection-fed environment; the
  shipped `runModule` keeps the open-module view), `instBody_linked`
  computes the canonical single-instance parent (one `@[hardware_module]`
  child, reference connections, single output), and the test pins the
  REAL compiled parent/child byte-for-byte (probe: parent =
  `[.inst child conns, out-alias]`, child = the standard combinational
  module), runs a 16-case linked regression, and instantiates
  `parentUse_linked`: the linked elaboration observes the source
  composition `childAdd a b` (name-generic in the emitter's instance
  names, standard axioms). The sub-module is additionally gated to BE
  the child declaration's own standalone certified compile, byte for
  byte, and the child passes the certified combinational gate — the
  child-side endpoints therefore apply verbatim to the instantiated
  module. S6-2 gate plumbing DONE: `mixedCertifiedShape?` takes an
  `isInst` predicate (default-false), `unifiedInstanceRoot` is the
  (prepended) instance disjunct, the real dispatch passes
  `instancePredicate env` (`@[hardware_module]` head-constant check
  from the run's `getEnv`), `synthesizeCombinationalCore_reads`
  exposes the run's predicate, old families' gate lemmas are
  ∀-predicate and their wrappers take the ∀-form shape premise
  (652-job suite green — the accepted set is UNCHANGED because the
  v1 instance root rejects the dom argument's out-of-kinds bvar).
  S6-2 ENTRY CLOSED for the canonical two-input combinational parent:
  the instance root accepts `@child dom a b` (the dom binder is a
  `.domain` kind, so the spine check admits it), guarded by
  `mixedGateResultScalar` (record-returning parents STAY legacy — the
  certified single-out harness would drop outputs; probe-verified and
  gated), and the certified dispatch reproduces the legacy lowering
  byte-for-byte (gated for `parentUse` AND a sequential child incl.
  clk/rst auto-plumb). The dispatch tail got a PROVABLE arm
  (`translateInstanceOrFallback` → `translateInstanceUncachedWith`,
  structural helpers, named env/cache reads), and
  Tools/ShippingInstanceEntrySoundness.lean proves the full chain:
  gate (`instance_term_gate`, AT the run's predicate), step, the
  monolith `synthesizeMixedCertified_instance_sound`
  (`InstancePreserves`: the compiled parent IS the canonical
  `instBody` over the pinned child, the design holds exactly that
  child, argument wires carry the prepared source values; boundaries
  `HardwareTagged`/`SubSynthDefines`; the single-out cache needs no
  premise since hits are validated against the builder's record), the
  dispatcher, the core wrapper (the run's `getEnv` is exposed, so the
  gate holds at `instancePredicate envR`), `instance_entry_of_env`,
  and the real-parent endpoint `parentUse_instance_entry` with a
  standard-axioms audit; the instance family also joined the S7
  bundle theorem as its twelfth component (per-run-predicate clause).
  The tie to the linked semantics is ALSO closed for the
  combinational parent: `parentUse_entry_observes` combines the
  instance contract of the run with `instBody_linked`, so the
  compiled parent's linked evaluation drives `out` with the SOURCE
  value `(parentUse aS bS).val t`. The SEQUENTIAL child's entry
  contract is closed too: `Instance1Preserves` (one data port plus
  clk/rst) proves the parent is the canonical instance body with the
  clk/rst connections AND the freshly added parent clock ports
  (`instClkRst_seq` walks the real plumbing, the missing-port checks
  discharged from the prepared inputs' allocated names), with the
  monolith/dispatcher/of_env/real-parent endpoint
  (`parentSeq_instance_entry`) and both instance families in the S7
  bundle. The sequential LINKED-RUN semantics is now closed for the
  canonical parent: `stepAssignsH`/`runH`
  (Tools/ShippingHierarchySoundness.lean) give instances a per-cycle
  stateful meaning (the child advances by its own `stepModule` on the
  connection-fed, state-backed environment `connEnvS`, threading its
  register state and memories), `instBody_stepH`/`instBody_runH`
  prove the canonical parent forwards the child's whole `runModule`
  trace, and on the real pair `childSeq_run` (the register family's
  packaged trace endpoint instantiated on the child) composes into
  `parentSeq_runH_observes`: the compiled sequential parent's linked
  run drives `out` with the SOURCE register stream
  `(parentSeq aS).val j` at every cycle (12-cycle numeric regression
  of the linked run included; audited, standard axioms). The
  combinational entry contract is GENERALIZED to every arity:
  `instEN` quotes the call over an argument LIST, the arm reads the
  spine structurally (`instSpineArgs`), `instArgs_resolve` proves the
  whole argument walk a chain of pure input reads by list induction,
  and `InstanceNPreserves`/`synthesizeMixedCertified_instanceN_sound`
  give the parent as one instance statement over the port-ordered
  connection list (each connection reading the prepared wire of its
  argument) — with the gate, step, dispatcher, `instanceN_entry_of_env`
  and the real three-input endpoint `parentUse3_instance_entry`
  (byte-parity with the legacy front end gated); the S7 bundle carries
  it as its fourteenth clause. The root-instance family is now
  CLOSED for every single-output child in ONE contract:
  `instClkRstPure` models the clk/rst walk as a pure state
  transformer (`instClkRst_pure`: the monadic walk IS it, for any
  port list), and `InstanceGPreserves` /
  `synthesizeMixedCertified_instanceG_sound` cover any arity, with or
  without clk/rst — clk/rst ports connected to same-named parent
  ports (present after the walk), data ports connected in order to
  the prepared argument wires — with `instanceG_entry_of_env` and
  the real two-data-port sequential endpoint
  `parentSeq2_instance_entry` (legacy byte-parity gated); bundle
  clause fifteen. MULTI-OUTPUT children are certified through field
  PROJECTIONS: the gate admits `field (child args…)` when the record
  argument's head is tagged and the projection is a structure
  projection (`unifiedProjSpine`, `instancePredicate`), the dispatch
  tail lowers it through the provable arm
  `translateProjInstanceUncachedWith` (byte-equal to the legacy
  handlers — gated for both fields of a real two-output child), and
  `ProjInstancePreserves` /
  `synthesizeMixedCertified_instanceProj_sound` give the parent as
  ONE instance statement wiring every child output port to its own
  pairwise-distinct fresh wire plus the alias reading the projected
  field's wire (`instCallKey_returns`, `outWiresPure` /
  `instOutWires_pure`, `outWireNames_nodup`), with
  `instanceProj_entry_of_env`, the real endpoint
  `parentHi_instance_entry` (second field of a two-output child) and
  `parentHi_entry_observes`, which ties the compiled parent's linked
  evaluation to the SOURCE field `(childTwo a b).hi` through the
  any-connection linked lemma `instAlias_linked`; bundle clause
  sixteen. New run boundaries: `ProjEnvDefines`, `ProjFieldDefines`,
  `OutCacheEmpty`. The pinned child modules now carry their REAL
  fully-qualified names and the suite compares them to the compiled
  child wholesale (the earlier `childModule` pin had the short name
  `"childAdd"`, which made `parentUse_entry_observes`'s
  `SubSynthDefines` premise unsatisfiable by the real run — fixed).
  Record-RETURNING parents (the whole record as the result) stay on
  the legacy front end. INSTANCES INSIDE CONES are certified
  (S6-3): the unified recursion is generalized over a semantic
  context class (`LinkCtx`, Tools/ShippingLinkCtx.lean — the body
  predicates runs/typed/simple with the closure laws the node lemmas
  use; the flat instance is definitionally the old predicates, so
  every existing endpoint is unchanged; `HierCtx`/`hierLink` executes
  instance statements against linked children via `evalAssignsH`),
  `Meaning` gains the instance case over a `ChildSem` table, and the
  fuel induction and quoted meaning are generic in their LEAF
  expressions (`fuel_contract_leaves`, `meaning_quote_leaves`: every
  leaf brings its own contract). Tools/ShippingInstanceLeaf.lean
  proves the leaf contract for a canonical call on a single-output
  combinational child with operands under arbitrary contracts
  (`inst_leaf_contract` / `inst_leaf_fuel`; boundaries
  `HardwareTagged`, `SubSynthDefinesAll`, child facts, `ChildCorrect`
  — the pinned child computes its source function), covering both
  validated cache paths with NO cache premise (the single-out cache
  hit is validated against the builder's `translateRecord`, which
  also removed `InstanceCacheEmpty` from the four root contracts).
  Tools/ShippingHierTermSoundness.lean lifts it to the entry
  (`HierConePreserves` / `synthesizeMixedCertified_hierCone_sound`:
  the compiled module's LINKED evaluation observes the term at
  `out`), with the instance-aware gate (`hierGateBoolBody` /
  `hierGateBitsBody` / `hierGateRoot`, acceptance lemmas
  `hier_quote_accepted` / `hier_root_accepted` / `hier_cone_gate`),
  dispatcher, `hierCone_entry_of_env`, bundle clause seventeen, and
  the real endpoint `parentMix_entry_observes` (`childAdd a b + a`,
  with `childAdd_correct` discharging the child's correctness on the
  pinned module). MODULE PIPELINES are certified too: the gate spine
  `hierInstSpine` accepts operands that are binders or, recursively,
  designated calls (`hierInstRoot` for a pipeline as the whole body,
  `hier_instRoot_gate`, `hierRoot_entry_of_env`), and
  `parentNested_entry_observes` proves the linked evaluation of the
  real `childAdd (childAdd a b) b` observes its source — the outer
  call's leaf contract consuming the inner call's leaf contract as an
  operand contract. Byte parity with the legacy front end is gated
  for two calls, a repeated call (ONE instance), a Bool root, a
  sequential child inside a cone, a pipeline, a sequential stage fed
  by a combinational one, and a projection as cone leaf / as call
  operand. WIDTH LINKAGE (S6-4, the "parameters" item) is closed for
  every instance statement the provable arms emit: investigating
  parameters found a MISCOMPILE in the success domain — a
  `@[hardware_module]` with a free `Nat` width is compiled ONCE, at
  the fallback width 8 (`extractWidth`'s `return 8`), and an
  instantiation at another width (`childW 16 a b`) connected 16-bit
  parent wires to 8-bit child ports and typed the result wire 8 bits
  wide. The arms now run `instLinkCheck` before `emitInstance`
  (`instLinked`: every connected parent name is declared at exactly
  the child port's width; also on the two legacy multi-output emit
  sites) and REFUSE such a compile with a diagnostic; a width-generic
  module instantiated at its compiled width still compiles. No design
  in the suite trips the check. The check is a THEOREM in the
  contracts: `instLinked_sound` turns it into the proposition
  `Linked`, `InstanceGPreserves` and `ProjInstancePreserves` conclude
  `Linked m mc conns` for their statement, and the hierarchical
  context's typing predicate carries it through the recursion so
  `HierConePreserves` concludes `InstsLinked children m` — every
  instance statement of the compiled module is an instance of a
  linked child, width-linked against the module's declarations. The
  suite checks the executable form (`designLinked`) on seventeen
  compiled parents and that the 16-bit instantiation is refused.
  Native parameter synthesis (`#synthesizeParameterizedVerilog`,
  symbolic widths) refuses instances altogether, so no instance ever
  carries a parameter binding; per-call-site SPECIALIZATION of
  width-generic children (which would turn the refusal into a
  correct compile) is not implemented. THE SV/TEXT LAYER FOR
  HIERARCHY (S6-5) is connected through a bridge instead of a new SV
  semantics: the open-module layers already accept instance
  statements (an instance is a no-op, its outputs free inputs), so
  Tools/ShippingHierOpen.lean proves that a LINKED run is the open
  run from the oracle seeding — instance-output wires pre-seeded with
  their final values (`linked_open`) — and that the seeded values are
  the children's evaluations on what each instance reads
  (`linked_consistent`, `Consistent`), under the decidable body
  check `linkedWF`; `seedOuts_bounded` derives the seeding's width
  bound from the children's output bounds (`ChildOutsBounded`) and
  the gate `instOutWidthsOk`. Tools/ShippingHierSVSoundness.lean
  restates the emitted-SV and parsed-text transfers over the
  instance-bearing fragment `seqStmtOkI` (`seq_run_to_svI`,
  `seq_run_to_parsedI`, generated from the assign/register versions
  with the instance cases filled in) and composes them:
  `hier_pipeline_transfer(_bounded)` — the linked evaluation of a
  combinational instance-bearing module is observed by the emitted
  Verilog's semantics and by the module parsed back from the printed
  bytes, with `Consistent`. `parentMix_shipping` is the capstone on
  the real compile (gates suite-checked on the real module; the full
  entry is the identity on it); its text is the core module's own
  print. THE OPTIMIZER (S6-6): the shipping text is the print of
  `checkedOptimize m`, and on instance-bearing modules
  `checkedOptimize` returns the UNCHECKED optimizer output (it
  inlines `_gen_out` in `parentMix`). That pass is now covered by
  translation validation with the EXISTING checker
  (Tools/ShippingHierOptSoundness.lean): `openFlat` drops the
  instance statements and declares the instance-output wires as
  input ports — a no-op in the open-module view
  (`evalAssigns_openBody`) — so `optCheck` on the extracted pair
  validates the optimizer (`hier_opt_open`), and the linked meaning
  crosses it (`hier_opt_transfer`: the same oracle seeding is
  consistent for the optimized module when its instance statements
  are kept, `instsKept`, and every wire they connect is validated or
  untouched, `connAgreeOk`). `hier_shipping_transfer` composes it
  with the SV and parsed-text layers, and `parentMix_shipping_opt`
  is the capstone on the SHIPPING text: real compile → optimized
  module → emitted Verilog semantics and the module the shipping
  parser (reader-side optimizer included) reads back, with the
  linked source value at `out` and `Consistent`. The gates are
  suite-checked on three real parents (`parentMix`,
  `parentTwoCalls`, `parentNested`), including
  `checkedOptimize m == optimizeModule m`. Still open in the
  hierarchy post-pipeline: sequential children in the bridge
  (`runH`), the design-level text (children printed alongside the
  parent, `toVerilogDesign`), and the full-entry statement
  (`synthesizeCombinational` instead of the core entry). Open in
  S6: call operands that are general cones
  (`childAdd (a + b) b` — the leaf contract takes any operand
  contract, the gate spine does not yet), sequential/Bool-output/
  multi-output children as cone leaves (gate-accepted and
  byte-gated, no entry contract), registration of the linked children in
  the emitted design (the `children` table of the contract is a
  premise; the suite checks `d.modules` concretely), multi-level
  linking (a child that itself instantiates), parameters, and the
  SV/text layer for hierarchy (the M-layers' open-module view).
- [ ] **S7:** Reconcile all successful cases and compose the full shipping
  theorem; instantiate it on real circuits without substituting per-instance
  replay for coverage. STARTED — the reconciliation-1 statement exists
  (Tools/ShippingCoreSoundness.lean): `ShippingPreserves` bundles all
  ELEVEN family contracts (mixed sources, unified terms, vector muxes,
  the five register shapes, the two `circuit do` shapes, the two memory
  shapes), and `synthesizeCombinationalCore_shipping_sound` proves ONE
  successful run of the real entry satisfies them all simultaneously —
  each family's quoted-shape premise selects the applicable contract,
  so this is the single statement every per-shape endpoint routes
  through (audited, standard axioms). The sequential POST-pipeline is
  also composed (Tools/ShippingPipelineSoundness.lean):
  `shipping_pipeline_transfer` chains the checker transfer, the
  emitted-SV semantics and the parsed-bytes transfer into ONE step —
  from one canonical-seed run of the checked module, the optimized
  module, its emitted Verilog and the module parsed back from the
  printed bytes all run to the SAME trace, under the pipeline's
  decidable premises (audited, standard axioms). The hierarchy
  entry has JOINED the bundle (clauses 12–13: `InstancePreserves` and
  `Instance1Preserves`, at the run's own instance predicate). The
  MEMORY post-pipeline is composed too
  (`shipping_pipeline_transfer_mem`: from the checked module's own
  canonical-seed run, the emitted Verilog — read latch and write
  program included — and the parsed-back module run to the SAME
  trace), and the composed statements are INSTANTIATED on real
  circuits as single capstones: `regAcc_shipping` (mux/arithmetic cone
  + register: source stream observed by the optimized module, its
  emitted Verilog and the parsed-back text, one trace) and
  `memAcc_shipping` (sync-read memory: source `Signal.memory` stream
  at the emitted Verilog and the parsed-back text, one trace) — both
  from the real `RunsTo` compile under `EnvDefines` and the
  pipeline's runtime-gated premises, audited. The register
  capstone is LIFTED to the full shipping entry:
  `shipping_pipeline_transfer_merged` composes the sequential merge
  step (a second `seqOptCheck` gate, raw → merged) in front of the
  optimizer/SV/parse chain, and `regAcc_shipping_full` states the
  capstone from the real `synthesizeCombinational` run (decomposed by
  `synthesizeCombinational_reads` to its core run and the
  cleanup/merge post-step) — the suite gates `seqOptCheck raw mFull`
  on the REAL full-entry output of all six register shapes and pins
  it component-equal to the merged module the print/parse gates are
  stated on. The memory capstone is lifted the same way
  (`memAcc_shipping_full`): from the real `synthesizeCombinational`
  run, with the body-identity of the cleanup/merge post-step as an
  explicit premise (the suite pins the real full-entry output
  component-equal to the certified core module, and decides the
  premise itself with the LAWFUL `DecidableEq` on statements —
  `decide (mFull.body = raw.body)` — not the derived `BEq`). The
  hierarchy post-pipeline exists for combinational parents
  (`hier_shipping_transfer`, `parentMix_shipping_opt`: optimizer
  validated by interface extraction, emitted SV and parsed-back text
  under the oracle seeding). The legacy-success coverage is now
  MEASURED rather than listed (`scripts/shipping-coverage/run.sh`,
  results in ShippingCompiler-Coverage.md): of 389 real-corpus
  declarations 47 pass a certified gate and 342 compile through the
  legacy front end only; the miss reasons are ranked there. Open in
  S7: closing that gap. A prototype normaliser showed that unfolding
  definitions alone certifies NO real declaration (197 change, 0 pass):
  the corpus is `circuit do` state machines with `let`, applicative
  lifting, slices and structure results, projected by thin wrappers,
  and every feature is the sole blocker of at most 6 declarations.
  The measured order is therefore by dependency, not by count:
  front-end normalisation (definition unfolding, projection of a
  constructor) → general N-slot `circuit do` → hardware `let` →
  applicative lifting, slices/concatenation → structure/tuple results
  → concrete-domain registers and memories. The first step has
  LANDED for definition unfolding: the entry computes an entry constant
  (`entryConst`: the declaration as read when a gate accepts it, its
  pure delta-beta unfolding `userInliner` when only that passes a
  gate), `synthesizeCombinationalCore_reads` is restated over it (the
  existing endpoints are unchanged — `entry_kept`), the whole bundle
  holds at the entry constant (`synthesizeCombinationalCore_entry_sound`),
  the boundary is `EntryDefines` (with `of_env` / `of_inline`), and two
  real helper-structured declarations are certified end to end
  (`useSel_execution`: nested helpers of both sorts; `accH_run`: a
  helper inside a feedback loop) — the suite gates 19 unfolded
  declarations byte-identical to the legacy compile and the
  reserved/tagged/library/over-budget cases left alone. The normaliser
  also resolves a user structure's field projection against the
  constructor its record head-normalises to (zeta of the lets in
  front — the legacy projection handler's own reduction), which is the
  wrapper idiom of the IP test benches: the FIRST TWO REAL IP MODULES
  are certified end to end, `nodeFilter_execution` (DroneCAN node
  filter) and `oddParity_execution` (MIL-STD-1553 odd parity, sixteen
  shifted-and-masked bits XOR-reduced and compared), each stating that
  the compiled module computes the IP definition's own output stream. APPLICATIVE
  LIFTS have landed next: the Bool-result binary lifts
  (`(BitVec.ule · ·) <$> a <*> b`, `ult`/`slt`/`sle`, `==`, `&&`, `||`,
  `^^`) are normalised to `Signal.ap (Signal.map f a) b`, lowered by an
  arm of the Bool control path at the legacy hints, and are two new
  constructors of the unified `Term` (`appCompare`, `appBool`; plus
  `bitsNum` for numeric literals) carried through the whole stack —
  source, view/meaning, contract, protection, order, both gates, both
  `circuit do` cone conversions. `inRange_execution` proves a range
  check written with them and `rcon_execution` the AES round-constant
  table of the IP library; the suite gates 18 declarations
  byte-identical to the legacy compile, the 256-entry AES S-box among
  them. The dispatch chain is now data (`fallbackKind`), so a shape
  reaching its end is one fact. Cost on the legacy route, measured
  against the previous compiler: 18 of 191 corpus outputs renumber
  their fresh wires (more sharing), none differs otherwise. SLICES
  have landed as the first VERTICAL unit of the breadth phase: the
  part-select `x[hi:lo]` on a reference is a right-hand side of every
  layer — `simpleRhs`, `TypedExpr.slice` (width `hi - lo + 1`, needs
  `hi < we x`), `PrintShape.sliceRef`, the renderer and the grammar
  productions `partSelect`/`castShift`, name binding, rename and
  post-processing lemmas — and `Term.slice` in the front half
  (`Signal.map (fun x => BitVec.extractLsb' start len x) s` at literal
  widths, `0 < len`, `start + len ≤ ws`; arm `FallbackKind.slice`,
  byte-identical to the legacy map handler; contract, protection, order,
  both gates, both cone conversions). `fc_execution` and
  `isNmt_execution` prove the CANopen COB-ID function code (a 4-bit
  field) and NMT decode (that field compared with zero) of the IP
  library; the suite gates 11 declarations byte-identical to the legacy
  compile. 60 of 389 real declarations pass a gate. Cost, measured: 10
  of 192 corpus outputs change text — purely combinational modules with
  a slice now ship the unoptimised module (the optimizer checker does
  not normalise slices), a policy the user chose; none changes hardware.
  CONCATENATION landed the same way: `{a, b}` on two references through
  the back half (`simpleRhs`, `TypedExpr.cat` at width `we a + we b`,
  `PrintShape.catRef`, renderer, name binding) and `Term.concat` in
  front, indexed by the sum of its operand widths. Its lowering
  allocates the result wire before the operands, so the contract,
  protection and order lemmas are the binary operator's (pending
  parent) at the hints `concat_hi`/`concat_lo`, under the fallback
  arms' cache wrapper. The one new front-end fact: the elaborator
  writes the result width as `m + n` and parents carry that sum in
  their type arguments, so the front end now folds literal `Nat` sums
  (`inlFoldNat`) and the arm fires only on the folded form — the legacy
  route, which sees the declaration as written, is untouched.
  `cSwap_execution` proves a nibble swap (two slices concatenated);
  the suite gates 11 declarations byte-identical to the legacy compile
  of the declaration as written. 63 of 389 real declarations pass a
  gate. LITERAL OPERANDS followed (`v#k ++ b`, `a ++ v#k`:
  `Term.concatLitHi`/`concatLitLo`, arm `FallbackKind.concatLit`): the
  concatenation lemmas were restated over operand actions
  (`translateConcatActs`, `concat_outcome`/`_protect`/`_order` taking
  `ActionSpec`/`ActionProtect`/`ActionOrder`), a literal operand being
  the action that allocates and assigns a `concat_const` wire
  (`concatConst_spec`/`_protect`/`_order`); `cWide_execution` proves
  `(0#1 ++ a) + (0#1 ++ b)`, the first step of the LIN checksum; 15
  declarations gated byte-identical; no corpus output changed. Open
  next: the general `circuit do`, which is where every IP body now
  stops. TWO MAP IDIOMS followed: `a.map (fun v => BitVec.append (0#k)
  v)` (`Term.zextMap`; its lowering is the zero-extending cast's, so the
  cast's lemmas apply through `setWidth_eq_zero_append`) and the slice
  written `f <$> a` (`Term.sliceF`; the slice lemmas, now stated for any
  child hint, at the `Functor.map` handler's hint `a`). The front end
  folds literal `Nat` differences and descends into `let`s.
  `zNarrow_execution` proves widen-add-narrow; 9 declarations gated
  byte-identical. 63 of 389 real declarations pass a gate. The corpus
  classifier (entry-normalised values) now says what a real `circuit do`
  body needs beyond the general arm: a structure result behind a
  projection, `let`, and the two-level Bool lifts (`x && !y`,
  `!(x || y)`), which need unary `not` as a back-half shape. Both
  LANDED next: the bitwise NOT of a reference is a right-hand side of
  the back half (`simpleRhs`, `TypedExpr.not1`, `PrintShape.notRef`,
  the renderer's width-pinned form and the grammar productions
  `maskNot`/`bitNot`, name binding), and the three two-level bodies are
  `Term.appBool2` in the applicative Bool arm, the inner application
  on its own wire as the legacy emits it. `bBusy_execution` proves the
  busy flag of a bit-serial engine; 8 declarations gated byte-identical.
  63 of 389 real declarations pass a gate. What remains for a real
  sequential IP module is the general `circuit do`, `let` and the
  structure-result projection — none of which can be byte-identical to
  the legacy lowering (the packed state has a zero-width `Unit` wire;
  the `let` cache is a MetaM heuristic), so they need the user's
  decision on emitted-text changes on the certified route. The two
  halves that do NOT depend on that decision are in place:
  `ShippingMachineSource.circuit_state` — for ANY slot list, the state
  of `runCircuitH inits body` is the initial tuple at cycle 0 and the
  pending writes' values afterwards, given that the writes are pointwise
  in the state (one `rfl` per declaration, `pointwise_of_const`) — and
  `ShippingMachineTrace.trace_of_cyclesN` — the k-cycle `runModule`
  trace of a module with any number of registers, from its per-cycle
  step. `machine3_state` instantiates the first on three slots of
  different types, one of them never written.
- [x] **The general `circuit do` on the certified route (the machine
  route).** Decision of the user (2026-10-02): the certified route may
  emit text that differs from the legacy compile when the function is
  the same. A `circuit do` with any number of Bool/BitVec slots and one
  Signal result — directly, or one field of a structure result — is
  compiled as its TRANSITION: the result and every next value packed
  into one bit vector (`result ++ next₀ ++ … ++ nextₙ₋₁`), a
  combinational body over the declaration's binders plus one binder per
  slot. `machineShape?` reads it off the unfolded declaration PURELY
  (zeta of the hardware `let`s; the `Circuit.next` writes in order — the
  last write of a slot wins, an unwritten slot holds; the result, with a
  structure-field projection resolved) and offers it to the unified gate;
  `synthesizeMachineCertified` compiles it with the SAME certified
  combinational harness and closes the slot ports into registers with
  the pure IR function `Sparkle.IR.Machine.closeMachine`. No new
  monadic compiler proof: `closeMachine_step` (IR), then
  `synthesizeMachineCertified_sound` (`MachinePreserves`: one cycle of
  the emitted module, from a run of the real harness),
  `machine_trace` (any number of cycles, for any valuation of the slots
  over time that starts in the registers and follows the transition),
  `synthesizeCombinationalCore_machine_sound` (the real entry; boundary
  `MachineDefines`). END TO END, emitted-module trace = SOURCE
  declaration at every cycle, standard axioms only: `mThree_execution`
  (three slots of two kinds, one never written) and `lin_execution` —
  the LIN checksum of the IP library (`IP/Bus/LINHW.checksumHW`, some
  twenty `let`s, a structure result). Measured: 82 of 389 real
  declarations pass a gate (was 63), 19 of them on the machine
  route; 16 modules changed their text, every one a machine-route
  module (8 of 196 output files differ), and every one of the
  19 emitted modules agrees with its source in a 60-cycle IR
  simulation. OPEN on this route: structure (multi-output)
  results as such; the optimizer/print pipeline for machine modules
  (the family-agnostic `shipping_pipeline_transfer` is not yet composed
  with `machine_trace`); domains other than a binder or
  `defaultDomain`; `let` as a term binder (zeta is budgeted — over
  budget the declaration stays on the legacy route); a generic source
  bridge (the two endpoints prove the source recurrence per
  declaration, from `circuit_state` and one `rfl`).
- [x] **Hardware `let` on the machine route.** The first version unfolded
  every `let`, and a classifier showed 86 of the remaining declarations
  running out of the unfolding budget: `circuit do` copies its `let`s
  into every write and into the result, and `let`s mention `let`s, so the
  unfolded tree is exponential. Now a hardware `let` (its type a Bool or
  positive-width BitVec Signal) is a BINDER of the transition and a
  FIELD of its packed value
  (`let₀ ++ … ++ letₖ₋₁ ++ result ++ next₀ ++ …`, a `let` value
  mentioning earlier `let`s only); copies of one value are one `let`.
  The transition is compiled ONCE; `Sparkle.IR.Machine.closeLets` then
  drives each `let` port from the operand wire of its field, right
  after the statement that drives that wire, checks the result is in
  dependency order, and removes the ports. Proved:
  `closeLets_eval` — by the uniqueness of the solution of an acyclic
  assignment body (`equations_eval`), no reasoning about statement
  order — `chain_values` (the operand wires hold their fields),
  `synthesizeMachineCertified_sound` under `LetsHold` (the valuation
  gives every `let` binder the value of its field), `machine_trace`.
  `lin_execution` is re-proved on the eighteen-`let` form: `lin_lets`
  says the source's own `let` values satisfy the transition's `let`
  equations. New boundary `MachineCloses` (this run tied the `let`s;
  proved outright for a shape without `let`s). Measured: **111 of 389**
  real declarations pass a gate (82 before), 48 on the machine route —
  among them the I²C, SPI, SBUS, CRSF, DroneCAN and UART engines, the
  HKDF and RLP state machines, and the P-256, secp256k1, BLS12-381
  field and Miller-loop controllers behind their wrappers. 36 modules
  changed text against the previous commit, all machine-route; every
  one of the 48 emitted modules agrees with its source in a 60-cycle IR
  simulation. OPEN, by a classifier on the 278 that remain: 8 would pass
  with structure results; then computed constants (`2 ^ k`,
  `BitVec.ofInt`, negation: about 25), sub-module calls inside a
  `circuit do` (16), and a tail of unsupported shapes.
- [x] **Structure results on the machine route.** A `circuit do` whose
  result is a user structure of Bool/BitVec Signals is ONE module with
  one output port per field, named after the field (the names the legacy
  front end gives them) — the IP declaration itself, no wrapper.
  `Layout.outs` lists the ports and their fields of the packed value;
  `closeMachine` drives each with a part-select; `machOuts?` reads the
  ports off the result type and the structure facts of the environment
  (`StructEnv`: field accessors and, per structure, constructor and
  field kinds), which `entryConst`/`machineShape?` now take. A port name
  must not be one of the module's own (`outNameOk`: not `_…`, `next…`,
  `clk`, `rst`). `closeMachine_step`, `MachinePreserves` and
  `machine_trace` speak about every output port. `linHW_execution`:
  the LIN checksum module of the IP library, `IP.Bus.LINHW.checksumHW`
  itself, both ports `acc` and `chk`, emitted-module trace = source at
  every cycle. Measured: 118 of 389 real declarations pass a gate, 55
  on the machine route (7 with a structure result: the Montgomery
  multiplier and UART-transmit sub-modules of the ECDSA, P-256 and FIDO2
  demos among them). Only those 7 modules change text; the run status
  of every corpus file is unchanged.
  WHAT THE COUNT MEANS: a declaration "on the machine route" is compiled
  by the proved harness and the proved IR passes, and its emitted module
  agrees with its source in the 60-cycle simulation; the end-to-end
  THEOREM was instantiated for three of them (`mThree`, `linChk`,
  `checksumHW`) when this was written. It is now generated for every one
  of them (below: "The machine endpoint, generated").
- [x] **The reference machine** (`Tools/ShippingMachineRef.lean`). The
  valuation `machine_trace` asks for is constructed from the terms alone:
  `RefMachine` (state: reset values, then the slot fields of the packed
  transition value; `let` binders computed in order by `letStore`), and
  `machine_ref_trace`: the emitted module shows, at every cycle and on
  every output port, the field of the reference machine. Its side
  conditions are decidable — each `let` field reads earlier positions
  only (`LetsScoped`, through `reads` and `eval_congr_reads`), reset
  values inside their widths. Instantiated as `linHW_reference`. What a
  declaration still owes is that its Lean meaning IS the reference
  machine; proving that once, generically (typed valuations of the
  `circuit do` state against the store), is the next step.
- [x] **A `circuit do` is its reference machine, proved once**
  (`Tools/ShippingMachineDenote.lean`). `denote_state`: if the body's
  pending writes are, for every state signal and cycle, the typed values
  of the next-value terms (`H2` — `rfl` for a declaration), the state
  tuple of `runCircuitH inits body`, encoded, is the reference machine's
  state at every time; `denote_out`: a typed term that is a field of the
  packed core has the reference machine's output. Behind them: typed
  valuations with `dite` casts that reduce on concrete widths (`TVal`,
  `slotVal`, `letVal`), the agreement of typed and store valuations
  (`agree_slots`, `agree_lets`, by `eval_congr_wf`), the fields of a
  packed value (`packList_field`). `linHW_execution_generic` re-proves the
  LIN module's two-port end-to-end theorem with NO declaration-specific
  reasoning: data (typed `let`s, next-value terms, binder sorts), `rfl`
  (`linHW_writes`, the outputs), and decided side conditions. So the
  per-declaration endpoint is now mechanical; generating it (an unquote
  of the machine shape into terms, and the facts) for every machine-route
  declaration is the next step.
- [x] **The machine endpoint, generated** (`Tools/ShippingMachineAuto.lean`,
  `Tools/ShippingMachineCommand.lean`). `#machine_endpoint f` reads the
  typed terms off the transition of `f` (`unq`, the inverse of `quote`,
  constructor by constructor; it is NOT verified — the kernel checks what
  it returns), adds `f.machineData`, and the kernel checks six
  `Eq.refl`s: `f.machine_ok` (ONE Boolean, `MachineData.ok`, deciding
  every side condition of the endpoint: the binder split, widths and
  positions, well-formedness of the packed term, `LetsScoped`,
  `TermFacts`, the fit of the slots and the ports with the packed core),
  `f.machine_body` (the transition body IS the quotation of the terms),
  `f.machine_inits`, `f.machine_writes` and `f.machine_result` (on ANY
  state signal the body's pending writes and its result are the typed
  values of the next-value and result terms), `f.machine_source` (the
  declaration is the result of its body on the state loop). From these
  `machine_trace_of_data` concludes `f.machine_sound`: a run of the real
  synthesis entry on `f` returns a module whose every output port shows,
  at every cycle, the SOURCE declaration `f` — for every domain of a
  domain binder, the ids and registers chosen before the domain
  (`MachineTrace`). No proof script per declaration; 0.1 to 1.5 seconds
  each. MEASURED (`scripts/shipping-coverage/endpoints.sh`): **55 of
  the 55 machine-route declarations have the theorem** (3 before,
  written by hand). `checksumHW_ports` unfolds the generated statement
  into the one `linHW_execution` makes. Three things had to change for
  it: (a) the typed valuation reads a position by a `match` on
  `Nat.decEq`, not an `if` — with `if`, the kernel meets a read while the
  other side is the `ite` of a mux, fails on the arguments and unfolds
  BOTH, which evaluates the mux's condition; for a comparison against
  `x + p` with the 381-bit modulus that is unary in `p` and never ends
  (the Fp2 multiplier); (b) the source check is split in two so that
  values are compared on an abstract state signal only; (c) a lift
  written directly as `Signal.ap (Signal.map f a) b` — the tests of
  `circuit do`'s `match` — carried hygienic binder names, so its body was
  the quotation of NO term: `machCanonAp` gives them the names of the
  `<$>`/`<*>` normaliser (machine route only; two modules; against the
  previous compiler one wire of `fsmHoldCdo` has another number
  (`_tmp_concat_lo_13` → `_11`; the module is otherwise the same text)
  and nothing else in the corpus changes). What `f.machine_sound` still
  assumes is its boundary: `MachineDefines` (the run read this shape) and
  `MachineCloses` (the run tied the `let`s; proved when there are none).
- [x] **Normal forms on the machine route** (`machNorm`, `kernelNat` in
  `Sparkle/Compiler/Elab.lean`). The measured reasons the remaining
  `circuit do` declarations missed the route were mostly OTHER WAYS OF
  WRITING what the gates already accept. They are rewritten to the
  accepted form before the transition is read, on this route only:
  a constant computed in Lean (`BitVec.ofInt 32 (64 * 2 ^ 16)`,
  `2 ^ 256 - 2 ^ 32 - 977`, a user constant such as a state encoding) —
  also as a reset value, a slice start or a concatenation operand — as
  its literal, the value read by the KERNEL's own reduction
  (`Lean.Kernel.whnf`, a pure function of the environment: no second
  evaluator to trust, and `machineShape?` stays pure); `Signal.lit`; an
  operator with one operand a plain `BitVec` (`sig + c`); a `BitVec`
  operator lifted through `<$>`/`<*>` or a `map` with a constant; `~~~`
  on a `BitVec` Signal (`allOnes ^^^ a`, which is `BitVec.not` by
  definition). No new `Term` constructor and no new proof: the endpoints
  speak about the normalised transition, and that it means what the
  declaration AS WRITTEN means is the kernel check of the generated
  endpoint. MEASURED: **175 of 389 real declarations pass a certified
  gate (118 before), 112 on the machine route (55), and all 112 have the
  generated, kernel-checked theorem `f.machine_sound`.** Against the
  previous compiler: 177 output files identical, 21 different — 47
  modules, every one newly on the machine route, none that was on it
  before; run statuses unchanged; all 112 modules agree with their
  sources, every port, in the 60-cycle simulation. The suite's RTL
  structure check found one thing: its reachability walk did not know the
  machine route's register-input wires (`next_gen_*`) and called a live
  register dead; the check now reads them (`isWireName`), nothing else
  about it changed. Still refused, by the classifier: a sub-module call
  or a second `runCircuitH` inside the body (about 35), hand-written
  `runCircuitH` chains (6), a tuple result (1).
- [x] **Machine modules to the emitted Verilog** (`Sparkle/IR/RefineCheck.lean`,
  `Tools/ShippingRefineSoundness.lean`, `Tools/ShippingMachineShipping.lean`).
  The machine theorems ended at the module the CORE entry returns; what
  ships is that module after the duplicate merge and the optimizer, printed.
  The existing sequential checker (`seqOptCheck`) accepts NO machine module:
  its normal forms have no part-select and no concatenation, and it pairs
  registers by position. `refineCheck m o` is a new result check for every
  assign + register module: normal forms over the inputs and the register
  outputs with the two-operand operators, shifts, comparisons, NOT /
  negation, mux, two-part concatenation and part-select, and with what the
  optimizer does to them (a wire replaced by its definition; `e & mask` and
  `e & 0`; `c ? 1 : 0` on one bit; a part-select through a concatenation,
  of a constant, of the whole expression); registers paired by NAME, and a
  register of `m` that `o` lacks is allowed (dead-register removal). Proved
  sound: `rSlice_sound`, `rNormE_sound`, `refineCheck_step_sound` (one
  cycle), `refineCheck_transfer` (any number of cycles: the outputs agree).
  `machine_ships`: `MachineTrace` of the core module + `refineCheck` on
  the merge + `refineCheck` on the optimizer + the emitted-Verilog check
  (`EmitSem.seqCheck`, `seq_run_to_sv`) ⇒ the optimized module AND its
  emitted Verilog show the source declaration on every output port at
  every cycle. `machine_ships_full` states it from a run of the FULL entry
  `synthesizeCombinational`; `#machine_endpoint f` adds it as
  `f.machine_ships`. The gates are decidable facts about the modules of the
  run (premises, as for the register capstones); the suite evaluates them
  on thirteen declarations and `scripts/shipping-coverage/pipeline.sh` on
  the corpus: **all gates hold for 104 of the 112 machine-route
  declarations**. The others: 6 are outside the emitted-Verilog
  fragment (`seqCheck`; the PCIe / TCP / Ethernet header parsers), 2
  have normal forms too large to compare (bit-serial CRCs: the normal forms
  are trees). Not covered: the module parsed back from the printed bytes
  (the reader's own optimizer goes further than the writer's on
  multi-register modules), and reset.
- [ ] **S7 / trust:** Resolve or explicitly retain `EnvDefines` in the final
  claim; record execution-model/external-tool boundaries without hiding them.
  RECORDED — docs/ShippingCompiler-TrustBase.md states the retained base
  in one place: the kernel + three standard axioms, `EnvDefines` (retained,
  with rationale), the runtime-gated decidable premises pattern, the
  byte→AST parse direction (and the sync-read-memory gap in M4), the
  linked-instance meaning, and the two boundary predicates the S6 entry
  work will add (`SubSynthDefines`, instance-cache cleanliness) with the
  unresolved cache-history trade-off that stages S6-2. FINAL FORM
  (2026-10-01): the document is rewritten around what the finished
  hierarchy work actually retains — the run-environment boundaries as
  one table (the single-out cache boundary is gone: hits are validated),
  the premises about a linked child, the decidable gates the suite
  evaluates, the meaning-carrying definitions, what the hierarchical
  text statements do and do not say, and what lies outside every
  theorem (legacy-route compiles first).

Latest validation: `lake build Tests.AllTests` passed all 675 jobs (2026-10-02, machine route), with
standard-axiom audits of the general endpoint and real signed/equality/Bool-logic
source instantiations. Vector mux adds 2,772 source/legacy/SV/delta cases and
real source theorems for nested and computed-condition muxes (no Bool input
required). The unified source/cache foundation adds 2,322 regression cases and
a standard-axiom audit, without extending the shipping endpoint yet. Bool equality and logic tests check 1,890 and 1,962
source/legacy/SV/delta cases; custom asymmetric Bool BEq is checked on all inputs.
Existing coverage includes 2,250 signed and 2,250 BitVec equality execution cases,
32 custom-BEq cases and 14 exhaustive applicative compilations. The existing
2,700 mixed source/SV/delta cases cover 18 paths, 6 accepted and 12 retained optimizer
selections, three bounded internal seeds, and shared expressions.
No schedule/session estimate is asserted. See the milestone plan for the
precise scope of the proved source fragments and S2's starting proof modules.

## Historical and other certification tracks

The sections below record older milestones and separate certification work.
An unchecked item can be closed for a named shipping fragment while remaining
open for the full domain or another route; use the current checklist above for
active shipping priorities.

## A. Composition chain (Signal ≡ emitted SystemVerilog)

- [x] The seam: `inlineConeT` / `resolveSlicesT` total twins +
  width/eval preservation (`cone_agrees_with_fold`,
  `cone_resolved_agrees_with_fold`); goal generators call the twins.
- [x] `#verify_elab` per-instance chain: `regstep` / `state_trace` /
  `signal_runModule` / `signal_sv` (Signal ≡ runModule ≡ runModuleSV).
- [x] Deep-side G1 glue (`{f}_deep_coneEval_*`): the general-theorem
  route's `Cdo.irState` cone terms land on the bridge language.
- [x] **Replay the bridge stack over `Cdo.irState`** — DONE.
  `#verify_elab_deep` emits per circuit: `{f}_deep_envAt` (the seed
  `envOfC nm (natJoin (irState t) inp)`), `_deep_seed_bounded`
  (`envOfC_bounded` + `irState_eq` + `BitVec.isLt` — no fold-side
  bounds), pointwise seed readers (`_deep_envAt_r{i}` / `_i{j}` /
  `_other`), `_deep_step_{reg}`, `_deep_regstep`, `_deep_envSt` /
  `_deep_st0` / `_deep_envSt_bounded`, `_deep_state_trace`, and per
  output port `_deep_signalM0` / `_deep_step_out` / `_deep_signal_fold`
  / **`_deep_signal_run`** (unconditional: Signal ≡ runModule trace).
  Struct outputs share one recurrence via `Cdo.irState_congr` (irState
  reads only next/inits).  Holds on all 13 demos + crc32Engine; the
  bridge lemmas are sorryAx-audited like the capstone.
- [x] **`evalOk` — absolute fold-success.**  `evalExpr` fails only on
  shape, so a decidable `evalOk` checker + soundness discharges fold
  success unconditionally; `{f}_signal_run` is the resulting
  hypothesis-free corollary.  (Deep-side / `signal_sv` still take a
  run hypothesis — wiring those is follow-up.)

## B. IR → Verilog remainders

- [x] **Optimizer — as translation validation, formally.**  Instead of
  proving `optimizeModule` (1.1 kloc, ten partial defs), the chain is
  CARRIED ACROSS it per instance.  Measured on every certified circuit,
  the optimizer changes an elaborator module's fully-inlined,
  slice-resolved cones in exactly one way — `inlineSingleUseWires`
  re-inserts identity width masks `and [e, const (2^w-1) w]` — and after
  `stripMask` (Tools/ConeFoldOpt.lean, with `stripMask_eval` on bounded
  envs via `sfrag_eval_bounded`) the optimized cones are SYNTACTICALLY
  the original ones.  `#verify_elab` now emits, over the OPTIMIZED body
  (the module `toVerilog (optimizeModule m)` actually prints; raw
  statement order, no topo-sort needed): `{f}_bodyOpt`, per-register
  `_maskEq_*` (native_decide), `_stepOpt_*`, `_regstepOpt`,
  `_state_traceOpt`, `_stepOpt_out`, `_signal_foldOpt`,
  `_signal_runModuleOpt`, `_signal_runOpt`, and **`{f}_signal_svOpt`** —
  Signal ≡ the Verilog-subset semantics of the emission of the optimized
  module, every cycle.  All 7 #verify_elab circuits (the optimizer may
  re-root a register at an alias-free input wire — twoReg — so cones
  are rooted at the OPTIMIZED registers, identities checked equal).
  Formalizes #verify_emit's informal "stepwise ⇒ sequential" claim.
  Remaining (optional): the same opt-bridge on the deep route; genuine
  per-pass optimizer proofs are no longer needed for circuit-do designs.
- [x] **M3 string layer — per instance.**  `#verify_elab` now emits
  `{f}_text := toVerilog (optimizeModule m)` (the printed Verilog),
  `{f}_text_parses` (the shipping parser+lowerer applied to that text
  yields `{f}_bodyRT`, by `native_decide` — the parser is trusted as an
  EVALUATED ORACLE, not proven), and replays the chain over `bodyRT`:
  **`{f}_signal_runRT`** — Signal ≡ runModule of the body the shipping
  parser reads back from the printed text, every cycle.  Registers are
  matched by name (the reparse lists them in another order); cones are
  mask-equal after `stripMask`.  All 7 #verify_elab circuits.
  What remains research-scale and is NOT claimed: a verified
  printer/parser inverse for the SV sub-language (a total renderer
  proven equal to the shipping printer + correctness of the 1 kloc,
  26-partial-def recursive-descent parser).  The trusted base here is
  "the parser as executed on this text", the same class as the
  native_decide checker discharges.
- [x] **Shared-route bridges to the printed Verilog (2026-09-14).**
  The `#verify_elab_deep` shared route (`sparkle.deepShare`) now
  replays its chain over the OPTIMIZED body and over the body the
  shipping parser reads back from the printed text, at shared-wire
  granularity: `{f}_sdeep_signal_runOpt`, `{f}_sdeep_signal_svOpt`
  (M4 forward semantics, when `seqCheck` admits the body),
  `{f}_sdeep_text_parses` + `{f}_sdeep_signal_runRT`.  Per-slot
  `native_decide` mask equations `rtNorm ∘ stripMask` (new
  `Tools/ConeFoldRT.lean`: the printer's 1-bit `not` form
  `1'(x ^ 1'd1)` comes back as `slice (concat [0, xor [x,1]]) 0 0`;
  `rtNorm_eval` proven) + `rtBridge_eval`.  Generator pre-checks every
  bridge precondition and SKIPs with a named reason; the PROVEN line
  lists exactly what holds; CI greps every clause and rejects any
  SKIPPED (except crc16's documented SV skip).  Measured: shareX4/8
  fully connected (55 s both); crc16CcittHW trace + replay + Opt + RT
  proven, SV skipped by the shl fit rule (754 s).  The link-by-link
  guarantee list with trust per link: `docs/SharedRoute-Guarantees.md`.
  Follow-up (scoped, not done): an `SF4` rule for a literal shift
  under the node-width mask, which would give crc16 the forward link.
- [ ] **M4 residual fragment** — the honest exclusions: byte-strobe
  RMW `shl` width rule, `CVT32ModuleS0`'s `sub 0'7 x` cone (not
  carry-free).  Revisit only via a width-indexed `emit_sem` if ever
  worth it (measured payoff was ~1 array; parked).

## C. Deep-elaborator coverage

- [x] **uart orphan goal — DONE (`uartTxHW` PROVEN, both `TxOut`
  ports, in ~4 s).**  Root cause was generic, not uart's: `Cdo.stateAt
  … ⟨i, _⟩ : BitVec (Γr.get ⟨i, _⟩)` puts a defeq-but-not-literal width
  on every state read, and Lean's simp set has `Fin.val_zero/one/two`
  only — a register index ≥ 3 stays `[…][↑3]` forever (uart was the
  first 4-register circuit).  simp then refuses the mixed goals
  ("not type-correct under instances transparency"), bv_decide /
  bv_omega reject the atoms, and `generalize` left the contradictory
  split hypotheses untouched.  Fix (Tools/DeepElab.lean): the Signal-
  side bridge never sees `stateAt`.  Per port the generator emits
  literal-width readers `{f}_deep_rd{i} : params → Nat → BitVec w_i`
  (definitionally `stateAt`), `_rd{i}_zero`, `_rd{i}_succ` (the cone
  as a shallow literal-width BitVec expression, `toShallow` mirroring
  `CExpr.denote` node for node) and `_deep_outS` — all `rfl`, since the
  deep semantics is structural and `CEnv.join`'s casts K-reduce on
  closed widths.  The trace proof packs the readers, rewrites one
  recurrence step with the `_succ` lemmas, generalizes the readers to
  plain variables BEFORE any split, and closes with `bv_decide`.  Two
  more generic fixes fell out: `sigval_append` was never retrieved for
  literal-width `++` ascriptions (simp indexes the implicit result type
  `BitVec (m+n)` — `simp -index` fixes it), and the fidelity lemmas
  now close by `rfl` rather than `simp`.  Also: the sorryAx audit ran
  under async proof elaboration and could report a failed bridge as
  PROVEN — the command now elaborates synchronously.  Closed BitVec
  constants (`crc32`'s `private abbrev poly`) are unfolded with the
  Signal helpers.  `uartTxHW` joined `Tests/Verification/
  DeepElabRealIP.lean`; all 13 demos + crc32 still PROVEN.
- [x] **Nested `circuit do` composition — DONE** (Tools/DeepElab.lean;
  demos `outerNest` / `outerFb` in DeepElabReifyDemo).  Facts learned:
  the IR flattens nested circuits into one register list, and because
  `runCircuitH` evaluates its body twice (next-state and output) the
  elaborator emits a nested circuit's registers TWICE (identical
  recurrences; the output reads one copy, the outer registers the
  other) — e.g. `closedLoopCircuit` has 5 registers for a 3-register
  design.  The Signal side keeps one `Signal.loop` per `runCircuitH`
  node.  Generator: discovers every `runCircuitH` node (top + nested,
  through the collected helpers) with its slot signature (width, init,
  Bool-ness), locates candidate register blocks in the IR by signature,
  abstracts the top loop as `L` and proves its trace once (`hLt`); each
  nested loop is discharged by the new `loop_trace_guarded_at`
  (Tools/VerifyElab.lean — the inner body may read the enclosing live
  signal, known only as a prefix) against a candidate block, trying the
  candidates in turn; duplicate copies get generated `_dup_r*`
  equalities (induction on the readers' step lemmas) that normalise
  whichever copy the proof picked.  Also fixed: the helper filter
  treated every `Sparkle.*` name as core, so helpers under
  `Sparkle.Tests.*` were never unfolded.
- [x] **Deeper nesting — DONE** (`lvl0 ⊃ lvl1 ⊃ lvl2`, the innermost
  reading both enclosing registers).  Term nesting exceeds circuit
  nesting (the inner circuit's input carries the mid loop's term, whose
  body carries the inner circuit again — four levels for a two-level
  design), and a deep step obligation needs prefix facts about EVERY
  enclosing live signal: `loop_trace_guardedP_at` takes an arbitrary
  prefix predicate `G` (a conjunction, extended by one equation per
  level) and the discharge recurses with level-indexed hypothesis names
  (shadowing was the first failure mode).  Recursion depth is adaptive:
  (#candidate alternatives)^depth ≤ 64, depth ≤ 5.
  `SPARKLE_DEEP_NOFIRST=k` runs alternative k unguarded for debugging.
- [ ] **Arithmetic size frontier** — `closedLoopCircuit` (PID + plant,
  32/64-bit fixed-point multiplies) times out at `isDefEq` in the
  definition phase (readers' `rfl` step lemmas / fidelity over the
  multiply cones) before the bridge runs; bv_decide on 64-bit multiply
  would be the next wall anyway.  Needs a different closer strategy
  (toNat-level arithmetic lemmas, or `decide`-free normalisation).
- [x] **Elaborator: duplicated nested-circuit registers — FIXED.**  The
  emitted hardware really was doubled (5 registers for
  `closedLoopCircuit`'s 3).  Two layers: (1) the elaborator's
  `Signal.loop` handler now has a canonical-key cache (with logic-`let`
  zeta and a result-wire ↔ loop-wire alias), which catches nested
  circuits that do not read the enclosing state; (2) the two body
  passes reduce an outer register read differently (`Reg.mk … live`
  projection vs a named let wire), so no syntactic key is stable for
  the feedback case — `Sparkle/IR/RegDedup.lean` merges the copies at
  the IR level by partition refinement (coarsest bisimulation over
  assigns and registers, alias-aware); non-representatives become
  aliases so no name disappears.  Runs right after zero-width cleanup
  in `synthesizeCombinational`.  `closedLoopCircuit` 5 → 3, `outerFb`
  5 → 3 (pinned in DeepElabReifyDemo).  Follow-ups from the first CI
  round (Build + IP Tests red): (a) user-named nodes (`_gen_*`, module
  outputs) keep their own statement — the JIT reads them by name and a
  plain alias is folded away; (b) the representative is the FIRST
  member in body order, or the alias points forward and the certified
  chain's `woCheck` rejects the body (every `#verify_elab` optimizer
  bridge was silently SKIPPED); (c) the optimizer's DCE phases 2/4 now
  treat OBSERVABLE wires as used — with more cache hits the elaborator
  emits `_gen_done := _gen__done` aliases whose uses constant-propagate
  away, and the pruned alias was exactly the wire `JIT.resolveWires`
  looked up (`h264-bitstream-test`, `oracle-accuracy-test`).
  `SPARKLE_NO_REGDEDUP=1` / `SPARKLE_NO_LOOPCACHE=1` A/B switches.
- [x] **Non-Signal value parameters — DONE** via the specialized-wrapper
  pattern synthesis already needs (`def accK15 d := accK 0x0F#8 d`).
  The wrapper's body is an application, not a `runCircuitH`; the
  generator now follows the head chain by delta-unfolding (arguments
  substituted, so the inner circuit's `inits` are closed) and unfolds
  it in the proof with the constants' first equations (`rw [accK.eq_1]`).
  Demos `accK15` (BitVec param) and `accN200` (Nat param →
  `BitVec.ofNat`) in DeepElabReifyDemo.  Found on the way: `Signal.lt`
  is not synthesizable at all ("Cannot infer hardware type from Nat" —
  a synth-elaborator gap, not a deep-route one; recorded in the
  synth-gotchas memo).
- [ ] Sub-instances (`.inst`) in the deep grammar; `memoryWithInit`
  (no synth support) and multi-port memories.  (Single-port memories,
  synchronous AND combinational read, are DONE — capstone and replay,
  on demos and on shipping IP.)
  **Prerequisite landed:** `Signal.memory` / `memoryComboRead` /
  `memoryWithInit` were `opaque` + `implemented_by` — no logical
  definition, so NOTHING about a memory-bearing circuit was provable
  on either route.  They are now `def`s whose bodies are the pure
  `Signal.memState` recurrence (contents after the writes of cycles
  `< t`; registered read = `memState n (readAddr n)` at `n+1`,
  read-old; combo read at `t`; withInit starts from `initData`), with
  `_val_zero/_succ`, `memState_zero/succ` rfl lemmas; the array
  implementations are unchanged and pinned to the spec by
  `Tests/MemorySpecTest.lean` (64 scripted cycles, all three).  The
  simulator, the IR semantics (`syncReadLatches` read-old) and the
  Verilog `always_ff` agree on timing — checked, no sim/synth gap.
  **Capstone landed** (single-port synchronous `Signal.memory`): the
  deep circuit is a `CdoM` (Tools/DeepElab.lean — `CMem` contents per
  memory, `NextM` = cone | latch, one write port per memory, `memUpd`,
  `stateAt`/`stateSig_eq`/`elab_general` mirroring `Cdo`; cones never
  read a memory directly, only its latch slot, so `CExpr`/`compile`/
  `compile_correct` are untouched).  Signal side: `Signal.memory_eq_loops`
  presents a memory as two nested loops — the read latch as a one-slot
  loop (`eq_loop_const`) over the contents loop (`memStep`,
  `memState_eq_loop`) — so the nested-loop discharge handles it with two
  more alternatives (packs `rd_latch s` / `md_k s`, `funext` before the
  closers; `md_k` is not `generalize`d: that left a metavariable).  The
  generator reifies `.memory` (latch slot after the registers, write-port
  fidelity lemmas) and emits the capstone `{f}_deep_trace` via
  `CdoM.elab_general`.  Demo `memAcc` in DeepElabReifyDemo.  RegDedup
  now merges duplicated `.memory` statements (single-port sync) too.
  **IR replay landed** (`memAcc_deep_signal_run`, the same `runModule`
  statement as for memory-free circuits, sorry-free): the seam facts are
  applied to the body WITHOUT its memory statements
  (`Tools/ConeFoldMem.lean`: `stripSyncMem`, `evalAssigns_stripSyncMem` —
  a synchronous memory is a no-op for `evalAssigns`, so the memory-free
  seam theorems apply to the stripped body verbatim), while the state
  step keeps the full body: `stepIterM` threads an `MEnv`,
  `runModule_stepIterM` / `runModule_isSomeM` (`bodyEvalOkM`) redo the
  reindexing and fold success without `memFree`.  Generator side: the
  IR memory contents at cycle t are `{f}_deep_memAt t` = `CMem.natView`
  of the deep contents (in-range indices read the array, others 0 — the
  IR never writes them), `_deep_regstep` lists the updates in BODY order
  with the latch entry via `syncReadLatches` on `memAt t`
  (`CMem.natView_latch`), `_deep_memstep` shows `memNexts` lands on
  `memAt (t+1)` (`CdoM.memUpd_natView` = `memWritePorts`' single-port
  update), state_trace/signal_fold/signal_run run over `stepIterM`.  A
  cone slot's IR step is `CdoM.irState_succ_cone` (through
  `compileCone`), a latch slot's `CdoM.irState_succ_latch` (through
  `NextM.latchAddr?`; the address cone's width is made explicit with
  `@CExpr.compile` — a type ascription is lost on the way into the
  implicit argument).  Write-port cones get their own G1 glue and step
  lemmas (`_deep_coneEval_m{k}_{wa,wd,we}`, `_deep_step_m{k}_…`).  **Audit fixes found on the way:** the sorryAx
  audit looked up the generated theorems by their SIMPLE name, which
  inside a `namespace` found nothing — it had never checked anything in
  the test files (now resolved in the current namespace); and theorems
  were elaborated asynchronously, so a kernel-rejected proof
  ("declaration has metavariables") was reported PROVEN — every generated
  theorem is now `set_option Elab.async false in` (`elabSync`) and the
  proof term is checked for metavariables.
  Two memories per module: demo `memTwo` (capstone + replay) — the
  second memory's ports are evaluated against the state the first
  already updated (`memNexts` threads it), so the payload lemmas are
  generic in the resolution state; and the bridge's reader abstraction
  is `gen_occ` (a `generalize` that FAILS when the pattern is absent —
  plain `generalize rd _ = g` of an absent reader succeeds vacuously
  and leaves the hole as a metavariable, rejected by the kernel with no
  tactic error to point at).
  **Combinational reads landed** (`Signal.memoryComboRead`, the
  Regfile / KVCache primitive; capstone AND replay, demo `comboAcc`).
  The read data is not state but a READ SLOT: `CdoM` gained a context
  `Γc` of read widths, `reads : Fin Γc.length → CRead` (memory index +
  address cone over registers and inputs — a read address reading
  another combinational read is outside v1) with the width side
  condition `hreads` (rfl slot by slot), and the cones live over
  `Γr ++ Γi ++ Γc`; the IR seed is `CdoM.irEnv` (registers, inputs,
  reads).  Signal side: `memoryComboRead_eq_loop` (the contents loop
  read at the address, same cycle) — one more inner-loop alternative.
  Replay: the seed carries the deep read value (`comboReads` recomputes
  and OVERWRITES it, so the IR trace is the IR's own), and the read
  statement is dropped from the fold by `evalAssigns_comboSeeded`
  (Tools/ConeFoldMem.lean): the read address's value after the memory-
  free prefix is the address cone at the seed (the seam on the prefix
  body `_deep_bodyP{c}`), which is what the read slot holds
  (`CdoM.irReads_eq`).  Only synchronous reads are stripped up front
  (`stripSyncOnly`, unconditional); `bodyEvalOkM` admits both kinds.
  Two things this exposed: (1) `topoSortBody` puts every memory first,
  which is WRONG for a combinational read whose address is a local wire
  (`evalAssigns` evaluates `comboReads` at the statement's position) —
  the deep route now orders its body with `deepOrderBody` (Kahn over
  assignments and combinational reads; the SV lowering's `topoSortBody`
  is untouched, its theorems are guarded by `woCheck`); (2) RegDedup now
  merges duplicated combinational-read memories too (the two-pass copy
  was two BRAMs).
  Remaining: `memoryWithInit` (no synth support today), multi-port
  memories, sub-instances (`.inst`), read addresses that read another
  combinational read.
- [x] **Register init from a value parameter — generator scope leak
  (found 2026-09-10, FIXED 2026-09-12).**  `Signal.reg k` with `k` a
  value parameter died in `#verify_elab_deep` with an internal `unknown
  free variable` while the emitter was correct.  Cause: `openLams` /
  `openLams'` opened the definition's lambdas with `withLocalDecl` and
  returned the collected `runCircuitH` applications OUT of that scope
  (root and helper sites); `nodeOf` then analysed them outside the
  local context they mention.  Fix: analyse inside the callback — only
  validated `LoopNode`s cross the boundary.  Evidence and regression
  gate: `Tests/Verification/ValueParamInitRepro.lean` (literal init,
  param-in-body, param-as-init, `Nat`-derived init, two-level wrapper
  chain — all PROVEN with `_deep_trace` + `_deep_signal_run`).  Axioms,
  CORRECTED from an earlier "standard only" claim: the capstone
  `_deep_trace` uses the three standard axioms; the replay
  `_deep_signal_run` additionally rides `native_decide` axioms (23 for
  `initCirc7`, from 7 replay lemmas) — the F2 trust boundary, `Lean.
  ofReduceBool`.  No `sorryAx`.  CI checks the five circuit NAMES in
  the PROVEN lines and a per-circuit `VPI OK:` line emitted by a
  `run_cmd` that verifies both theorems exist and use ONLY allowed
  axioms (subset check; `native_decide` auxiliaries recognised by name
  structure, not substring; negatives confirmed rejected); a missing
  test file fails the gate.  Full suite exit 0.
  The `have`/`letFun` case in `findRC` was also fixed (separately,
  earlier) and kept.
  **Retracted:** the "`Prod.fst` argument / `match_1` auxiliary
  traversal gaps" recorded on 2026-09-11 were observations of a scratch
  probe that over-unfolded the wrapper, NOT of the generator — the
  generator's `headChain` finds `runCircuitH` before reaching either,
  and the two-level wrapper chain proves with no traversal change.  No
  open traversal item remains from this defect.
  **Still open (small):** the generator has no designed refusal for a
  genuinely non-literal init (e.g. one that depends on a Signal); today
  `nodeOf` returns `none` and the top-level "could not locate the
  top-level runCircuitH" message fires, which names the symptom rather
  than the cause.  Worth a targeted message when a case appears.
- [ ] Bridge v1 limits: register inputs / memory ports that aren't
  `.ref` wires (the replay is skipped with a message; the capstone is
  still emitted).

- [x] **Generator compile time** — `Tools/DeepElab.lean` went from
  ~220 s to a 1287 s LCNF-compiler heartbeat timeout as the one
  `#verify_elab_deep` do-block grew (~2,500 lines): the compiler's cost
  on a single function is superlinear.  The per-port bridge and the
  replay are now `let rec` blocks (lambda-lifted into their own
  compilation units): 108 s.  Keep new phases as blocks.

- [x] **Real shipping IP: four more circuits** (2026-09-08) —
  `regFile` (ECDSA signer's 64×256 BRAM: the first shipping memory on
  the route, capstone AND replay), `transferIdTrackerHW` and
  `frameAccumulatorHW` (DroneCAN / S.BUS), `spiMasterHW` (SPI master, 7
  registers — the widest state chain).  17 ports total with crc32Engine
  and uartTxHW; CI gate raised.  Two generator fixes fell out:
  * seed boundedness is now an explicit case cascade.  `repeat' split`
    was used before, and at 7 registers `split`'s internal simp exceeds
    its step limit; `repeat'` SWALLOWS that failure, leaving the `ite`
    chain unsplit and the residual goal to `omega`, which cannot see
    through it.  Beware `repeat'` over a tactic that can fail loudly.
  * every generated declaration is elaborated with `maxRecDepth`
    raised (the `Fin`-literal name table is deep).
  Two new named boundaries: `crc16CcittHW` (cone blowup — measured at
  16 MB of `repr` text for a 94-statement module's single register
  cone; the duplication happens in `inlineConeT`, which substitutes a
  wire's definition at every use, so it is the CONE that needs sharing,
  not just the reified `CExpr` — and every theorem above
  `cone_resolved_agrees_at_seed` is stated over the inlined shape) and
  `kvHw` (≥ 16 state slots + inputs: the match
  compiler stops enumerating `Fin` literals past 15 arms, and neither a
  `i.val` match nor a catch-all arm survives the reader proofs).  The
  list-backed table was then built and measured: it DOES clear the
  exhaustiveness failure, but the "not a slot" reader still fails,
  because with a symbolic context length `List.finRange` presents as a
  `List.ofFn` that simp will not unfold (over a literal `Fin 18` it
  does).  Both pieces are needed together.

- [x] **State correspondence + duplication-freedom** (2026-09-08) —
  `Sparkle/IR/StateCorrespondence.lean`, pinned by
  `Tests/Verification/StateCorrespondenceTest.lean` and wired into the
  gate.  The trace theorems are INVARIANT under duplicated hardware
  (two copies of one register hold the same value at every cycle), which
  is why all three duplication bugs on this branch were found by eye.
  Two decidable checkers with soundness proofs close it:
  * `stateCorrespondence` — the DSL's state bindings map one-to-one onto
    emitted registers/memories (`matchSlots`, order-insensitive since
    the emitter may reorder); `stateCorrespondence_count` derives the
    count equality that a doubling violates.
  * `noDuplicateDefs` — no two defining statements share a canonical
    form modulo their own name (`noDupSigs_nodup`).
  Measured on all six proven shipping circuits: state counts match the
  DSL exactly and all six are duplication-free.
  **A size bound was considered and rejected as the primary property:**
  a constant factor loose enough to allow legitimate fan-out also allows
  a doubling, which is precisely the bug class.  (A monotonic
  emitted-weight metric is still useful as a CI bloat guard — separate
  from correctness.)
  **Calibration that mattered:** the first canonical form counted plain
  wire ALIASES (`x := y`) as duplication, so five of six circuits
  "failed" — `crc32Engine` alone carries one wire under eight names.
  Aliases are naming, not hardware (copy propagation collapses them),
  so they are excluded.  The test file's negative section pins
  non-vacuity against the real historical shapes: duplicated register
  block, duplicated BRAM, dropped state, repeated logic.

- [ ] **Cone sharing** (the CRC16 / arithmetic-size blocker, now scoped).
  MEASURED on `crc16CcittHW`: inlined cone 16 MB of `repr` text,
  sharing-preserved cone 43 chars, whole module body 14 KB — a ~1200×
  blowup from `inlineConeT` alone, which substitutes each wire's
  definition at every use (`crc16Step` unrolled 8× reading its input 3×).
  Note the emitted VERILOG is fine; the 16 MB exists only inside the
  proof, so a circuit-size bound would pass and the replay would still
  fail.  Affects the replay chain only — the CAPSTONE proves
  (`crc16Fixed_elab_trace`, per-instance route, 1 register).
  **Scoped, 2026-09-08:** `cone_agrees_with_fold` is already generic in
  the stop set (checked: re-proving it with a widened `stopAt` is
  literally the same term), so stopping early needs no new mathematics
  there.  The blocker is one premise of the seam theorem
  `cone_resolved_agrees_at_seed`: `hfrozen : ∀ n, stopAt.contains n →
  n ∉ writesOf body`.  The cone is evaluated at the SEED environment,
  where an intermediate wire has not settled yet, and `writesOf`
  collects every statement's LHS — so an intermediate wire can never be
  frozen and the shared cone cannot go through this theorem unchanged.
  **The enabling theorem LANDED** (`Tools/ConeFoldMem.lean`):
  `shared_cone_agrees_at_settled` states the agreement at the SETTLED
  environment, where the frozen premise is unnecessary — no
  `evalAssigns_frame` reindexing, so intermediate wires may be stop-set
  members.  It is additive, so the proven circuits are untouched.
  **Stop-set policy measured:** stopping at the wires READ MORE THAN
  ONCE (26 of them on crc16CcittHW) takes the cone from 16 MB to 954
  chars — a ~17000× reduction, and exactly the wires whose inlining
  duplicates work.
  Remaining for this item, and it is NOT just plumbing (scoped
  2026-09-08): the new theorem needs the SETTLED env bounded (`hb1`),
  where the seed-side one needed only the seed (`hb0`) — the seam's own
  design note says boundedness is required of the seed only, precisely
  because the frame argument moves the cone back before slice
  resolution.  A settled-env bound means "the fold's own writes are
  width-bounded", i.e. an expression-level bound.  One exists
  (`sfrag_eval_bounded`) but only inside the heavy `SFrag` fragment,
  which the seam deliberately avoids.
  **The fragment-free version's per-case facts are PROVEN and landed**
  (`Tools/ConeFoldMem.lean`): `evalOp` has exactly five result shapes
  and each one's bound is now a checked lemma — `mask_lt_sem` (the
  masked cases: and/or/xor/add/sub/mul/shl/neg, plus not/asr which mask
  at their operand's width), `compare_bounded` (0/1 at node width 1),
  `shr_bounded` (unmasked but only drops bits, so bounded by its value
  operand) and `mux_bounded` (returns one of its arms), together with
  the three `widthOf` rules those rely on (`widthOf_shr`,
  `widthOf_mux`, `widthOf_cmp`).
  **All 21 per-operator bounds landed** (`evalOp_bounded_*`), one named
  lemma per constructor.  `evalOp` is NOT recursive so it has no
  functional-induction principle, and a shared `first` cascade over
  `split at h` keeps claiming the wrong branch (the mux and masked
  closers overlap) — hence one lemma each: mechanical but deterministic.
  **The expression shapes landed too**: `evalExpr` IS recursive, so
  functional induction gives exactly five value-producing cases —
  `const`/`ref`/`slice` proven directly, `op` from the per-operator set,
  and `concat` via `concat_elem_bounded` (shift-or of two disjoint
  ranges, using core's `Nat.or_lt_two_pow`).
  **`evalList_bounded` landed** — indexed operand bounds for an
  argument list, the half of the assembly the `op` case consumes,
  standalone and independent of the per-operator dispatch.
  **`evalExpr_bounded` LANDED (2026-09-13, `Tools/ConeFoldMem.lean`),
  standard axioms only.**  Two corrections to the plan above, both
  found by reading the definitions rather than retrying tactics:
  (a) the proposed arity side-lemma `evalOp … = some r → args.length =
  arity o` is FALSE — `evalOp` matches `args` as a wildcard for most
  operators; only `vals` has forced arity.  The dispatch lemma
  `evalOp_bounded_gen` is therefore stated over both lists with
  `vals.length = args.length` and closes by `cases o <;> rcases args <;>
  rcases vals <;> simp at hlen <;> first | exact <21 landed lemmas> |
  (simp [evalOp] at h; done)` — length mismatch kills 20/25 shapes per
  operator, so the `first` alternatives never overlap.
  (b) the bound is FALSE in general: `mux` returns an arm unmasked at
  the TRUE arm's width, so a wider false arm escapes.  Every other
  operator masks, compares, or only drops bits.  Hence the new
  decidable side condition `widthOk` (mutual with `widthOkL`, mirroring
  `evalOk`): every mux's false arm is no wider than its true arm —
  trivially true for elaborator IR (both arms carry the DSL type).
  The induction is a MUTUAL THEOREM by structural recursion on the
  `evalOk_isSome` pattern, not `evalExpr.induct`.  Concat needs no
  recursive bound at all: `evalExpr.go` masks each element (`go_bounded`
  via `go_restW`, the zip-fold rest width = `widthOf.go` of the rest).
  **`evalAssigns_bounded` LANDED (2026-09-13)** — memory-free bodies,
  `bodyWidthOk` decidable side condition with non-vacuity guards.
  Every premise of `shared_cone_agrees_at_settled` is now provable.
  **Step (3) is a DESIGN DECISION, not a reroute — measured on crc16
  (2026-09-13, `SPARKLE_DEEP_TRACE` markers, the run otherwise stalls
  silently):**
  | inlined IR cone (`coneRaw`) | 16.25 M chars |
  | slice-resolved cone | 14.3 M |
  | reified `Cdo.next` arms SYNTAX | 26.8 M |
  | shallow bridge rhs (`_rd0_succ`) | 64.4 M — its `rfl` had not finished at the 1500 s timeout (NOTHM defs-only, MemoryMax=24G, single run) |

  Findings: (a) the reifier reifies the INLINED IR cone, so the deep
  side is as large as the IR side (correcting "blowup is not in
  reification"); (b) the constants add and the G1 glue CLOSES, because
  `native_decide` evaluates compiled code with sharing; (c) the run's last
  marker before the timeout is the Signal-side bridge's `_rd0_succ`, a
  kernel `rfl` over a 64 M-char term with no sharing.  Therefore sharing has to enter the deep grammar itself: a
  BINDING LAYER in `Cdo`/`CdoM` (ordered wire slots `Γw` with small
  per-wire `CExpr`s, `next`/`out` referring to wires), whose denotation
  evaluates wires in order before `next`/`out`.  That makes every
  reified term, bridge lemma and G1 small; the IR side links wire-for-
  wire via `shared_cone_agrees_at_settled` (stop set = the wire slots),
  `_deep_step_w` per wire at the settled env.  Touches `Cdo.elab_general`
  (a wire-evaluation lemma) and the reifier's stop set.  Estimated a
  multi-session item.  **Go-ahead given 2026-09-13**, staged: (1) trace
  strings lazy [done]; (2) premises on crc16's REAL body [done —
  `Tests/Verification/ConeSharingPremises.lean`, build-time, CI-gated:
  26 shared wires, register cone 954 chars, per-wire ≤ 589, memFree /
  noSelfRead / woCheck / bodyWidthOk / hwfCheck all true, frozen check
  false as predicted]; (3) prove the binding layer on a small memory-
  free circuit end to end (reification, bridge, replay) and scale the
  sharing depth, comparing generated size AND proof time against the
  inlined route — completion is "proofs finish and reduction does not
  re-expand", not "syntax is smaller"; (4) apply to crc16; CdoM after.
  **Step 3 baseline (2026-09-13, current inlined route).**  Family
  `shareX_n`: `r ← reg 0; w0 := r + i; w_k := (w_{k-1} + w_{k-1}) ^^^ i;
  r <~ w_n + w_{n-1}; out w_n` (add/xor only — a first `*`-based family
  hit the arithmetic-size frontier at n=4 and was discarded as
  confounded).  Conditions: `lake env lean`, timeout 600 s per file,
  `MemoryMax=24G`, one run each:
  | n | result | wall | inlined cone (`coneRaw`) | bridge rhs |
  | 2 | PROVEN | 28 s | 2,030 chars | 6,852 |
  | 4 | FAILED — `shareX4_deep_trace`: heartbeat timeout at `whnf` (1.6 M) | 87 s | 11,474 | 36,738 |
  | 6 | FAILED (isDefEq heartbeats) | 89 s | 56,762 | 188,163 |
  | 8 | FAILED (whnf heartbeats) | 95 s | 312,026 | 902,298 |
  | 10 | FAILED (whnf heartbeats) | 113 s | 1,546,586 | 4,237,859 |
  | 12 | FAILED (whnf heartbeats) | 63 s | 7,071,578 | 22,740,506 |
  | 14 | FAILED (whnf heartbeats) | 80 s | 35,594,074 | 104,373,795 |

  Both sizes grow ≈ 5× per step (2^n behaviour).  At n=4 the bridge
  `_rd0_succ` (37 K chars, `rfl`) still COMPLETES; the failure is the
  Signal-side TRACE THEOREM — so the binding layer's job is (a) small
  readers/bridge lemmas and (b) a trace proof that generalises wire
  readers to atoms and keeps their defining equations as hypotheses,
  never re-inlining them.  Comparison target for the shared route: the
  same family, same conditions, n up to 14 and beyond.
  **`CdoW` semantics landed** (`Tools/DeepElab.lean`, root namespace,
  2026-09-13): `wiresAt`/`wenv`/`full`, both recurrences, and
  `CdoW.elab_general`, standard axioms (statement without `let` — a
  `let` there broke `rw ←`'s syntactic match).  Generator does not use
  it yet.
  **Step 3 SHARED-ROUTE PROTOTYPE (2026-09-13)** — hand-emitted in the
  generator's output shape (`bench/cone-sharing/emit_shareW.py` +
  `shareW_trace.tpl`; n=4 pinned as `Tests/Verification/
  ConeSharingProto.lean`, CI-gated).  Same family, same conditions as
  the baseline (600 s, 24G, one run each):
  | n | shared route | inlined baseline |
  | 4 | PROVEN, 4 s | FAILED (heartbeats) |
  | 8 | PROVEN, 16 s | FAILED |
  | 12 | PROVEN, 46 s | FAILED |
  | 14 | "Missing cases" in the `nm` `Fin`-literal match (17 slots) — the KNOWN slot-count ceiling, not sharing | FAILED |

  Axioms: standard three + `bv_decide`'s native axioms (same trust class
  as the baseline's closer).  **Heartbeat limits (2026-09-14):** the
  generator fixes its trace theorem at `maxHeartbeats 1600000`
  internally (`Tools/DeepElab.lean`, the `set_option … in` around the
  trace command), so an outer `set_option` on `#verify_elab_deep` does
  NOT raise it — a "baseline at 4 M" attempt still reported 1.6 M and
  is not a valid comparison.  The prototype's trace theorem is
  therefore run at 1,600,000 too (emitter default), and its `sorry`
  fallback closers were replaced by hard `fail`s.  **Equal-limit
  measurement (1,600,000 heartbeats both routes, 600 s, 24G, emitted
  files gated to contain the limit and no `sorry`):** shared route
  n=4 3 s, n=8 16 s, n=12 46 s, all PROVEN; inlined route FAILED at
  every n ≥ 4 (heartbeat timeouts, table above).  The prototype's
  advantage is therefore not an artefact of a higher limit.  Every per-wire lemma is `rfl` on a
  one-wire cone; the trace theorem takes the wire equations as
  hypotheses and `bv_decide` bitblasts linearly on the IR side.
  **DSL side made LINEAR too (2026-09-14, plan item 1 DONE).**  No
  custom let-floating was needed: core `extract_lets` descends into
  subterms and under binders and merges equal values by default.
  Recipe (`shareW_trace_lin.tpl`, now the committed prototype): stage-1
  `simp -zeta` keeps the `have` chain, `extract_lets a w0 … wn p` lifts
  it to NAMED local defs (the binders are anonymous, so names must be
  given), per-wire `have e_k : w_k.val m = … := by simp only [w_k,
  sigval_*]` ties each def to its predecessor, the register read to the
  reader via `hpre`/`hLt`, the pack binding `p` is unfolded (small), the
  pair goal split, and `bv_decide` sees only atoms + linear hypotheses.
  Measured with a goal-size probe (`shareW_trace_lin_diag.tpl`,
  `Expr.sizeWithoutSharing`), 1.6 M heartbeats, 600 s, 24G:
  | n | goal before extract (step / out) | goal before bv_decide (step / out) | wall |
  | 4 | 2,942 / 2,708 | 194 / 40 | 4 s |
  | 8 | 4,134 / 3,900 | 194 / 40 | 17 s |
  | 12 | 5,326 / 5,092 | 194 / 40 | 46 s |

  Pre-extract sizes grow by a constant per step (linear); the goals the
  closer sees are CONSTANT.  Wall time still grows: definitions + rfl
  lemmas alone (Phase A) take 1 / 5 / 15 s at n = 4 / 8 / 12 — each
  `rw_k_eq` `rfl` unfolds k levels of `wiresAt`, so Phase A is
  quadratic (a `wiresAt` step lemma would make it linear; not needed
  yet); the trace theorem itself takes ~3 / 12 / 31 s, bv_decide over
  2n+ hypotheses.
  **Plan item 2 DONE (2026-09-14): REPLAY on the shared route, shareX4**
  (`Tests/Verification/ConeSharingReplay.lean`, hand-written in the
  generator's output shape, builds in 8 s, CI-gated with an in-file
  axiom policy).  Chain: per-slot G1 glue `coneEval_*` (each cone =
  ONE wire's definition, stopping at the other shared wires — a wire's
  own stop set excludes itself, otherwise inlining `.ref w` returns
  `.ref w`); seed `envAt` = registers, inputs AND deep wire values, its
  bound (via `CdoW.natJoin_full`), pointwise readers; per wire in slot
  order `settled_w*` (from `shared_cone_agrees_at_settled` with the
  wire's stop set and `hb1` from `evalAssigns_bounded`) then `wire_w*`
  (settled value = deep wire value, by `evalExpr_congr` on the cone's
  refs: registers/inputs by `evalAssigns_frame`, earlier wires by
  induction, using the new general lemmas `CdoW.irWiresAt_stable` /
  `CdoW.irWires_eq_at`, landed next to `CdoW`); `step_r` / `step_out`
  (seed-side evaluation by the same congruence); `regstep`; `envSt`
  (state-indexed seed, masked so it is bounded for ANY state), `henv`
  (agreement with the seed when the state matches the spec), `state_trace`,
  `signal_fold`, **`signal_run`**.  Axioms: `trace` std + 2 bv_decide
  aux; `signal_run` std + 61 native_decide/bv_decide aux; no sorryAx.
  Demo-only: `weM := fun _ => 8` (all wires 8-bit here); the generator
  will use the module's width table.  Lessons for the generator: the
  settled lemmas need an explicit expected type and `(e' := coneRaw)`
  or `native_decide` sees a metavariable; `congr 1`/`try exact`
  cascades time out — use explicit cases; the G1 statements must use the
  literal context list, not an abbrev, for `rw` to match.
  **Plan item 3 DONE (2026-09-14): slot ceiling cleared on the shared
  route, verified to 32 slots.**  Two `Fin`-literal matches hit the
  15-arm ceiling: the name table `nm` (17 slots) and, once that was
  cleared, the `CdoW.wires` field (one arm per wire).  Fixes, both in
  the emitter (`SHAREW_NMLIST=1`): `nm := fun i => nmL.getD i.val ""`
  over a `List String` (the shared route reads `nm` only through
  `envOfC_names` / `envOfC_notin` / decidable facts — never by simp
  unfolding, which is what broke the earlier list-backed attempt on the
  inlined route); and `wires := fun j => (wlOk j) ▸ (wl.getD j.val
  default).2` over a width-tagged list `wl : List (Σ w, CExpr Γ w)` with
  `wlOk : ∀ j, (wl.getD j.val _).1 = Γw.get j` by `decide` — the cast
  K-reduces on closed widths, so every `rfl` lemma still closes.
  `hinj` moves to `native_decide` (32² string comparisons).  Linear
  recipe, 1.6 M heartbeats, 900 s, 24G, one run each:
  | slots | n | result | wall |
  | 17 | 14 | PROVEN | 73 s |
  | 19 | 16 | PROVEN | 74 s |
  | 23 | 20 | PROVEN | 143 s |
  | 32 | 29 | PROVEN | 473 s |

  (inlined route: FAILED from n=4.)  Wall time grows faster than linear.
  Breakdown at 32 slots: Phase A (definitions + per-wire `rfl` lemmas)
  204 s, trace theorem ≈ 269 s.  Phase A is quadratic by construction
  (each `rw_k_eq` `rfl` unfolds k levels of `wiresAt`); a `wiresAt`
  step lemma (`wenv ρ ⟨k⟩ = (wires k).denote (join ρ (wiresAt ρ k))`,
  stated once, used by `rw`) would make it linear — do this when crc16's
  numbers say so, not before.
  **Generic DSL half (`signal_lets`, 2026-09-14):** the tactic replaces
  the hand-named `extract_lets` + equations; `shareW_trace_gen.tpl`:
  17 / 23 / 32 slots in 51 / 144 / 476 s (named variant 73 / 143 /
  473 s) — the generator no longer needs to count or name the DSL's
  `have`-bound wires.
  **Plan item 4 DONE (2026-09-14): the GENERATOR's shared route**
  (`set_option sparkle.deepShare true` or `SPARKLE_DEEP_SHARE=1`;
  v1 scope memory-free / single-port / no nested loops, anything else
  refused with a named message — verified on `memAcc`).  From
  `#verify_elab_deep`, trace theorem AND IR replay, real IR names, the
  module's width table (`lake env lean`, 24G, 1.6 M heartbeats):
  | circuit | slots | wall | replay axioms |
  | shareX4 | 7 | 7 s | std + 57 aux |
  | shareX8 | 11 | 33 s | std + 89 aux |
  | shareX14 | 17 | 241 s | std + 137 aux |

  (default route: FAILED from n=4).  `Tests/Verification/ConeSharingGen.lean`
  pins shareX4 + shareX8, CI-gated on both PROVEN lines.  Default route
  unchanged (43 PROVEN across RealIP / ValueParamInit / ReifyDemo).
  Cost note: `Tools.DeepElab` now compiles in ~425 s (was ~140 s) — the
  shared block is one large `do`; split into `let rec` sub-blocks if it
  grows further.  The replay dominates wall time at n=14 (241 s vs 51 s
  trace-only in the prototype): each wire's settled lemma re-checks
  `hwfCheck` on its own stop set by `native_decide`.
  Generator-side gotchas (recorded for the next integration): identifiers
  introduced inside quotations are hygienic — `intro n`, `rcases … with
  ⟨kv, hk⟩`, `{v : Nat}` cannot be referred to from another quotation
  (use `mkI` names, positional args); resolved cones must be `def`s
  (delta-unfoldable), not literal constants, for `exact` against
  `resolveSlicesT wt coneRaw`; `a | b` is an `rcasesPatMed` — build case
  splits as sequences of two-way `rcases` with focused bullets; after
  `simp`, Fin literals normalise (`⟨0,_⟩` → `0`) so close with `exact`
  up to defeq rather than `rw`.
  **Plan item 5 DONE (2026-09-14): crc16CcittHW PROVEN on the shared
  route — trace theorem AND IR replay** (`Tests/Verification/
  ConeSharingCrc16.lean`, CI-gated as its own step): 1 register, 3
  inputs, 17 shared wires (alias reads excluded from the count; 16 since
  2026-09-14, when a full-width slice of a slot became an alias), replay
  axioms = standard + 160 decision-procedure auxiliaries, no sorryAx.
  709 s wall (`lake env lean`, 24G, 1.6 M heartbeats per generated
  declaration).  The default route's inlined cone for this circuit is
  16 M chars and never got past its bridge.
  What it took beyond the shareX family, each found by measurement and
  recorded in the code: (a) every generated declaration under the 1.6 M
  heartbeat limit (a per-wire `rfl` on 16-bit cones exceeded the
  200 000 default, logged not thrown); (b) `signal_lets` builds its
  equations as EXPRESSIONS (`mkAppM` + `mkEqRefl` + `assert`), not by
  re-elaborating delaborated values (unknown-identifier errors with
  recovery → sorryAx); (c) `clear_value *` on the extracted bindings so
  bv_decide cannot zeta-expand them into one opaque nested term
  (spurious counterexample); (d) width normalisation — `dsimp` with the
  Nat simprocs on each equation and `change` on each binding's type —
  because `BitVec (8 + 8)` from `++` made bv_decide abstract the two
  widened-byte equations as Boolean atoms and cut the chain; (e) lemma
  lists built from QUOTATIONS (resolved in the generator's scope), since
  runtime `mkIdent` names resolve in the caller's file, which need not
  open `Sparkle.Core`; (f) the output half as `first | zeta-off +
  extraction | zeta-on without extraction`: with zeta off the register
  `match` on the pack cannot reduce (the pack sits behind mkRegList's own
  lets) and extraction reached under the lambda; with zeta on the
  next-chain expands only linearly when no helper body is unfolded, and
  such circuits' output is a register read.  Cost: `Tools.DeepElab` now
  compiles in ~760 s (shared block + tactic); the replay dominates the
  709 s (per-wire `hwfCheck` by native_decide on each wire's stop set).
  Remaining v1 limits (refused with a named message): memories, more
  than one output port, Bool-typed outputs, nested loops.
  Follow-ups: Phase-A/replay time (a `wiresAt` step lemma; share one
  `hwfCheck` per wire family); multi-port outputs; memories (CdoM) —
  out of scope until asked.
  Until then crc16 / arithmetic-size circuits remain capstone-only.

## C2. Build time of the generator and of crc16 (measured 2026-09-19)

Method rule from the review: measure first, one change, same conditions,
and never report an inferred cause as measured.  Conditions for every
row below: `lake env lean`, MemoryMax 30G (generator) / 24G (crc16), 32
cores, dependencies prebuilt, no other heavy job running, one run each.

**The three measurements asked for.**
1. No-change rebuild of `Tools.DeepElab`: 0 s.  Caching works.
2. `Tools/DeepElab.lean` alone (profiler, 2 s threshold): total 1042 s,
   of which `compilation (LCNF base)` 1010 s, `do element elaborator`
   13.5 s, `elaboration` 1.13 s.  The generator's cost is Lean compiling
   the elaborator's own code to native, not proving anything.  LCNF is
   superlinear in a single function's body size.
3. crc16 verification alone (3 s threshold): total 877 s, `type
   checking` 702 s, `tactic execution` 159 s, `interpretation` 10.6 s,
   `elaboration` 0.15 s.  61 per-item `type checking` entries ≥ 3 s,
   max 24.2 s, mean ≈ 10 s, summing to 614 s; the 88 s remainder is
   entries under the threshold.  No nesting: the 159 s is a separate
   phase.  A run of 14 consecutive entries at 19.2–19.3 s is a repeated
   per-slot cost.  CONCLUSION HELD AT: crc16's time is concentrated in
   kernel type checking.  Nothing further claimed yet.

**Attributing the generator's largest LCNF item to a function.**  The
profiler's items are anonymous.  Recompiling an existing constant is a
no-op (measured: 0 ms), and with `Elab.async` on, `addAndCompile` only
ENQUEUES — the timer around it measures nothing while the real compile
runs later (measured: every closure "0–1 ms", 488 s of wall).  Both
were artefacts and are NOT reported as measurements.  With
`Elab.async false` and a fresh copy of each lifted closure compiled
individually:

| closure | LCNF time |
|---|---|
| `sharedRoute.sharedReplay` | 361.6 s |
| `sharedRoute` | 68.6 s |
| `portBlock.replayBlock` | 39.4 s |
| main body | 12.1 s |
| `portBlock.bridgeBlock` | 3.1 s |
| `portBlock` | 1.8 s |

So the 365 s item is `sharedReplay` — whose `replayOver` and
`sharedBridge` were plain `let` lambdas inlined into one ~770-line body
— and NOT `replayBlock`, which two earlier inferences had pointed at.

**Changes, each a pure restructuring (same code, order, obligations):**

| step | total | LCNF base | largest item | elaboration |
|---|---|---|---|---|
| baseline | 1042 s | 1010 s | 598 s | 1.13 s |
| shared route → `let rec sharedRoute` | 598 s | 565 s | 369 s | 1.15 s |
| port loop body → `let rec portBlock` | 519 s | 487 s | 365 s | 1.21 s |
| `replayOver`/`sharedBridge` → `let rec` | 190 s | 163 s | 67 s | 1.2 s |

The third row removed the 365 s item outright: it became 35.8 s + 4 s,
and the largest remaining item is `sharedRoute` at 67 s.  An unchanged
re-run between rows 2 and 3 (an edit that failed its assertion and wrote
nothing) gave 520 s / 365 s against 519 s / 365 s — a reproducibility
point for the measurement itself.
Verification after the first two: shareX4 37/55/56/55, shareX8
61/91/92/91, nothing skipped — identical to before.

Generator work stopped after the third row (190 s), per instruction.

**crc16, per DECLARATION with names (2026-09-19).**  Every generated
theorem re-added to the kernel synchronously (`Elab.async false` —
with it on, `addDecl` only enqueues and a timer measures nothing) under
a fresh name, timed, with the proof term's `sizeWithoutSharing`.
348 theorems, re-check total 697 s — consistent with the profiler's
702 s of type checking, so the attribution is complete.

| declaration | kernel | proof nodes | type nodes |
|---|---|---|---|
| `_sdeep_trace` | 22.4 s | 5,286,453 | 4,119 |
| `_sdeep_envAt_w{0..15}` (each) | 19.2–19.4 s | 30,489 | 1,609 |
| remaining ~331 | ≈ 366 s total, mean ≈ 1.1 s | | |

The 16 readers cost ≈ 309 s = 44 % of crc16's type checking.  They are
BODY-INDEPENDENT (emitted once, not per replayed body).
**Separation, term size vs reduction, on the reader:** the trace and a
reader take the same kernel time with a 173× difference in proof size
(5.3 M vs 30 k nodes).  At the trace's per-node rate a reader would be
~0.13 s; it is 19.3 s.  So the reader's cost is REDUCTION, not term
size; the trace's is the term (the `bv_decide` certificate).  The
reader's proof ends in a bare `rfl` closing
`natJoin ρ (irWires …) ⟨nR+nI+k, _⟩ = irWires … ⟨k, _⟩`, which the
kernel decides by lazy delta — the candidate being unfolded is
`CdoW.irWires`, i.e. the whole 16-wire recurrence.  **One-declaration experiment, DONE (2026-09-19), same conditions
(`Elab.async false`, one run each), same statement
(`type_of% crc16CcittHW_sdeep_envAt_w3`):**

| proof of the last step | kernel + elab |
|---|---|
| `rfl` (the generator's) | 18 959 ms |
| `exact natJoin_right _ _ 3 (by decide) _` | 6 ms |

Axioms of the lemma route: the standard three.  Cause CONFIRMED: lazy
delta through `CdoW.irWires`.  `natJoin_right` (generic, kernel-cheap:
`natJoin r x ⟨Γr.length + k, h⟩ = x ⟨k, hk⟩`) is now in
`Tools/DeepElab.lean` and the 16 reader sites use it; nothing else
changed, no check weakened.  Expected crc16 saving ≈ 16 × 19.3 s ≈
309 s of 880 s — an ESTIMATE until the row below is measured.

| crc16, same harness (lake build, 24G, cgroup peak) | wall | peak |
|---|---|---|
| before (`rfl` readers) | 880 s | 2.797 GB |
| after (`natJoin_right` readers) | 593 s | 2.867 GB |

MEASURED saving 287 s (−33 %) against the 309 s estimate; peak +70 MB
(+2.5 %).  Auxiliaries unchanged (replay 108, Opt 162, RT 162), the one
documented SV skip preserved, shareX4/8 unchanged (37/55/56/55,
61/91/92/91, nothing skipped).  **Post-fix per-declaration profile with names, aggregated by KIND
(2026-09-19; same harness, 348 theorems, re-check total 412 s):**

| kind | sum | n | mean proof nodes | reading |
|---|---|---|---|---|
| `wire_w*` (orig / Opt / RT, 80.5 s each) | 241 s (59 %) | 48 | 1.19 M, growing ≈ 127 k per wire index (w12 1.77 M → w15 2.15 M; 9.6 s → 18.3 s) | term-size-bound; O(k) per wire ⇒ O(nW²) total |
| `settled` [orig] | 52.5 s | 16 | 442 | tiny term, 3.3 s each; the same kind on Opt/RT is 0.19 s |
| `hwfL` [orig] | 33.4 s | 16 | 321 | tiny term, 2.1 s each; Opt/RT 0.25 s |
| `trace` | 22.4 s | 1 | 5.29 M | the `bv_decide` certificate |
| `rwN_eq` + `rdN_succ` | 24 s | 17 | 53–77 | `rfl` readers on the Signal side (reduction) |
| everything else | ≈ 40 s | 250 | | |

The orig/Opt-RT asymmetry has an obvious candidate: the ORIGINAL body is
the un-optimized module (94 statements) while Opt/RT are 20, and every
settled/step lemma re-proves `woCheck` / `memFreeCheck` /
`noSelfReadCheck` over it by kernel `decide` — the same proposition,
34 times per body.  MEASURED one decide at a time (kernel, same conditions):

| fact | body | statements | kernel |
|---|---|---|---|
| `woCheck [] body` | orig | 94 | 6817 ms |
| `noSelfReadCheck body` | orig | 94 | 347 ms |
| `memFreeCheck body` | orig | 94 | 4 ms |
| `woCheck [] bodyOpt` | Opt | 20 | 374 ms |

So the asymmetry is `woCheck` over the un-optimized 94-statement body,
re-proven by every settled and step lemma of that body (33 sites).
Fix (queued, one change at a time): prove `woCheck`/`memFreeCheck`/
`noSelfReadCheck` ONCE per body as named theorems and reference them —
the F2-step-1 pattern.
**`wire_w*` separated on w15:** the proof is 2.15 M nodes as a TREE but
5615 nodes as a DAG (depth 110); the kernel works on the DAG, so 18 s
on a 5.6 k-node term is REDUCTION, not size — the earlier "term-size-
bound" reading was a tree-count artefact and is withdrawn.  The growth
with the wire index points at the fuel-indexed `irWiresAt … k` being
unfolded by the wire-slot bullets' `show` (a right-block `natJoin`
projection decided definitionally, the same shape as the readers).
That hypothesis was KILLED by measurement: the projection alone is
10 ms by `rfl` at fuel 15 (5 ms via the lemma, 7 ms at fuel 3, 4 ms for
the left-block bullet).  So `wire_w15`'s proof was RECONSTRUCTED from
the generator's script in a scratch (faithful: 18 653 ms vs the 18.3 s
measured on the real theorem) and split: body WITHOUT the congruence
`hc` 4 ms; `hc` ALONE 18 680 ms.  All of the cost is inside `hc` (the
`evalExpr_congr` with one bullet per earlier slot: `hsub` by
`native_decide`, the membership `simp`, an `rcases` chain, then per
slot `rw [wire_wj, envAt_wj]; show …; rw [envOfC_names]; …`).  Bisected
within `hc` (each row = the same `hc` with the wire bullets' tail cut
by `sorry` after the named step; register/input bullets real):

| cut after | ms |
|---|---|
| prefix only, every bullet `sorry` | 20 |
| wire bullets: `rw [wire_wj, envAt_wj]` | 54 |
| + `show envOfC … (snm ⟨idx⟩) = _` | 88 |
| + `rw [envOfC_names …]` | 104 |
| + `show irWiresAt … k ⟨j⟩ = irWires … ⟨j⟩` | **18 648** |
| + `rw [irWiresAt_stable … k …]` | 18 827 |
| + `unfold irWires` | 18 964 |
| full | 19 093 |

One step — the second `show`, a right-block `natJoin` projection
decided by definitional unfolding (different heads on the two sides,
so the kernel's lazy delta unfolds `irWiresAt … k`, the fuel-k wire
recurrence) — carries the entire cost.  It is the same shape as the
fixed readers.  Note the interaction: a SINGLE wire bullet with that
step is 59 ms; 15 of them are 18.6 s — the cost across bullets is
strongly superlinear, so the per-bullet isolated measurement (10 ms)
under-read it.  Count curve and fix, MEASURED (same `hc`, same conditions):

| real wire bullets | ms |
|---|---|
| 2 | 16 210 |
| 4 | 16 764 |
| 8 | 17 445 |
| 12 | 18 547 |
| 15 | 19 241 |
| only wire 0 (full) | 16 757 |
| only wire 14 (full) | 61 |
| all 15, `show` → `refine (natJoin_right …).trans ?_` | **246** |

So the cost is not per-bullet: ONE bullet — wire index 0, whose
projection the kernel decides by unfolding `irWiresAt … k ⟨0⟩` — is
16.8 s, the rest add ~0.2 s each, and the earlier per-bullet
measurement at index 14 (10 ms) missed it because it was the wrong
index.  The fix keeps the head `natJoin` on both sides so the kernel
never unfolds: 18.7 s → 0.25 s for the congruence, standard axioms.
Applied at the generator's wire-bullet site (one line).  MEASURED,
same harness (lake build, 24G, cgroup peak, one run each):

| crc16 | wall | peak |
|---|---|---|
| before (`show` bullet) | 593 s | 2.867 GB |
| after (`natJoin_right` bullet) | 343 s | 2.824 GB |

Saving 250 s (−42 %) against the ≈ 240 s estimate; peak −43 MB.
Auxiliaries unchanged (108 / 162 / 162), the one documented SV skip
preserved; shareX4/8 unchanged (37/55/56/55, 61/91/92/91, nothing
skipped), 65 s.  Cumulative for crc16 today: 880 s → 343 s (−61 %),
with no change to any obligation.
**Shared body facts, DONE (2026-09-19).**  Proposition identity checked
on ALL arguments: inside `replayOver` every site is `woCheck []
$bodyXId` (`done = []` everywhere), `memFreeCheck $bodyXId` (the `_`
unifies to the same constant from the lemma's statement) and
`noSelfReadCheck $bodyXId` — the same three propositions per body,
re-proven at 2 / 7 / 2 kinds of site.  Now one theorem per body
(`{f}_sdeep_hWO{tag}` / `_hMF{tag}` / `_hNSR{tag}`; orig / Opt / RT are
distinct constants and keep distinct theorems).  Measured, same
harness, one run each:

| | before | after |
|---|---|---|
| shareX4+8 wall | 65 s | 42 s |
| crc16 wall | 343 s | 202 s |
| crc16 peak | 2.824 GB | 2.192 GB |
| crc16 auxiliaries | 108 / 162 / 162 | unchanged |
| SV skip | 1 | 1 |
| shareX4/8 auxiliaries, skips | 37/55/56/55, 61/91/92/91, none | unchanged |

The peak fell by 630 MB — the duplicated decide proofs were also the
memory.  crc16 today: 880 s → 202 s (−77 %) with no obligation changed.
**Post-change by-kind aggregation** (357 theorems, re-check total
108.7 s, was 412 s):

| kind | sum | n | mean proof nodes |
|---|---|---|---|
| `hwfL` [orig] | 33.3 s | 16 | 321 |
| `trace` | 22.4 s | 1 | 5.29 M |
| `rwN_eq` [orig] | 18.1 s | 16 | 53 |
| `rdN_succ` [orig] | 6.0 s | 1 | 77 |
| `hinl` [orig] | 5.3 s | 17 | 236 |
| `hwfL` [Opt] / [RT] | 4.0 s / 3.9 s | 16 / 16 | 321 |
| `hWO` [orig] | 3.3 s | 1 | 77 |
| everything else | ≈ 12 s | | |

`wire_w*` and `settled` no longer appear.  JUDGEMENT: no COMMON waste
(the same proposition re-proven) remains.  What is left is per-item:
`hwfL` [orig] is 16 DISTINCT propositions (one stop set per wire, each
a kernel walk over the 94-statement body — reducible only by a new
lemma deriving the per-wire check from the full-stop-set one plus one
width fact, not by sharing); the trace is one 5.3 M-node certificate;
`rwN_eq`/`rdN_succ` are Signal-side `rfl` readers (the known Phase-A
item; a `wiresAt` step lemma would make them cheap).  Per instruction,
build-time work stops here and F2 resumes.

**F2 step 8 DONE (2026-09-19): `resolveSlicesT` kernelised; the
refs-membership facts (`hsub`) leave `native_decide`.**  Same two
blockers as the cone walk (table read through `wt.get?`; recursion on
(fuel, expression) with same-fuel re-entry ⇒ well-founded), same two
fixes in `Tools/ConeFoldRT.lean`: `assocGetR` + `foldInsert_get?_eq` /
`wtFold_get?_eq` (lookup agreement from `get?_insert`, no
`native_decide`); `stepR` / `resolveSlicesS` (fuel-outer, `stepR` not
even recursive; axioms `propext` only); `resolveSlicesT_eq_S` by
induction on FUEL (every call from level f+1 is at level f, so one
hypothesis covers the re-entries; the `rsT_*` reduction lemmas expose
the arms; both sides then differ only in compiled `match` auxiliaries,
closed by `rfl`); `resolveSlicesT_list` composes.
Real `hsub` obligations, kernel vs `native_decide`, standard axioms:
shareX4 slot 3 27 ms vs 3 ms; crc16 slot 15 60 ms vs 4 ms.
Generator: `hsub` is body-independent, so ONE theorem per slot
(`{f}_sdeep_hsub_{slot}`) referenced from all three replays.

| | before | after |
|---|---|---|
| shareX4 aux (replay/Opt/svOpt/RT) | 37/55/56/55 | 31/49/50/49 |
| shareX8 aux | 61/91/92/91 | 51/81/82/81 |
| crc16 aux (replay/Opt/RT) | 108/162/162 | 90/144/144 |
| crc16 wall / peak | 202 s / 2.192 GB | 203 s / 2.191 GB |
| shareX4+8 wall | 42 s | 43 s |
| skips | crc16 1 (documented), shareX 0 | unchanged |

The drop is one per wire plus two per body's steps (−6 / −10 / −18),
exactly the removed sites.  **F2 step 9 DONE (2026-09-20): the G1 glue's four obligations by the
kernel — no new implementation.**  Checked directly first: `concatNorm`
and `noSingle` are already structural (axioms `propext` only),
`CExpr.compile` and `CdoW.wires` axiom-free, so the kernel computes
them as they are.  Per slot: `hres` is the cone constant's definition
(`rfl`, 0 ms); `hinl` is the step-7 kernel theorem reused (1 ms; the
original body's `hinl_*` are now emitted before the glue and the replay
skips re-emitting them, decided by body tag — an environment lookup by
simple name misses namespaced declarations, measured as a duplicate in
ConeSharingGen); `hns` and `hnorm` are `decide` after rewriting the
cone to the structural resolver (`{f}_sdeep_hresL_*`): 2 ms and 21 ms
vs 1 and 4-6 ms native.  Whole glue theorem per slot: standard axioms.

| | before | after |
|---|---|---|
| shareX4 aux (replay/Opt/svOpt/RT) | 31/49/50/49 | 7/25/26/25 |
| shareX8 aux | 51/81/82/81 | 11/41/42/41 |
| crc16 aux (replay/Opt/RT) | 90/144/144 | 18/72/72 |
| crc16 wall / peak | 203 s / 2.191 GB | 211 s / 2.287 GB |
| shareX4+8 wall | 43 s | 45 s |
| skips | crc16 1 (documented), shareX 0 | unchanged |

The drop is 4 per slot (24 on shareX4's 6 slots, 72 on crc16's 18).
crc16's replay is now at 18 auxiliaries (from 152 on 2026-09-16).
**F2 step 10 DONE (2026-09-20): the hwfL lookup-agreement facts are
instances of `stopOfL_contains_elem`.**  The stop-set entity is the
same on both sides (the map constants are `stopOfL stopL` /
`stopOfL (stopLw w)`, the very lists the lemma receives), so the
per-stop-set `native_decide` hypothesis became
`fun n _ => stopOfL_contains_elem stopL n`.  One line; no new checker,
no fallback.  Measured, same harness, one run each:

| | before | after |
|---|---|---|
| shareX4 aux (replay/Opt/svOpt/RT) | 7/25/26/25 | **2**/20/21/20 |
| shareX8 aux | 11/41/42/41 | **2**/32/33/32 |
| crc16 aux (replay/Opt/RT) | 18/72/72 | **1**/55/55 |
| crc16 wall / peak | 109 s / 2.07 GB | 107 s / 2.10 GB |
| shareX4+8 wall | 28 s | 28 s |
| skips | crc16 1 (documented), shareX 0 | unchanged |

The replay theorems now carry ONLY the trace theorem's `bv_decide`
auxiliaries (2 on shareX4, 1 on crc16; confirmed by `#print axioms`).
Everything else on the replay side of the shared route — inlining,
resolution, G1 glue, refs-membership, hwfCheck and its lookup agreement,
the width table, the body facts — is kernel-checked.  Still
`native_decide`, read off `#print axioms` of shareX4's Opt bridge: per
replayed body, the 18 mask equations `maskEq_*` (1 per slot) and the
two `widthOk` side conditions handed to `rtBridge_eval` in every
settled/step lemma (2 per slot = 36 on crc16) — 54 per body, + the
trace's 1 = the 55 reported; plus the parse oracle (1).  Both kinds are
statements about `rtNorm (stripMask (cresX …))` / `rtNorm (cres …)`.
**Step 11 probe (2026-09-20):** with the resolver rewrite they
kernel-decide on crc16's slot w15 RT (mask equation 12 ms, both
`widthOk` 2 ms) and the original-side `widthOk` on shareX4 (2 ms) — but
shareX4's Opt slot w3 STALLS on the mask equation and the replayed-side
`widthOk`.  Measured cause, each alone in the kernel: `sfragCheck wof
(.ref "_gen_i") = true` does not reduce (its axioms are the
well-founded signature); `maskOf` on an identity mask stalls through it;
`stripMask` on a mask-free cone computes.  The optimizer's masks are
present in shareX4's Opt cones and absent from crc16's w15 RT cone,
which is the whole difference.  **Step 11 DONE (2026-09-20):**
`stripMaskK` (Tools/ConeFoldRT.lean) — the same pass with the guard
`widthOk (weW wof) e` (structural; axioms of the definition: propext
only) instead of `sfragCheck`; the bound the guard exists for comes from
the fragment-free `evalExpr_bounded` on the bounded environment
`rtBridge_eval` already had (`maskOfK_eval`, `stripMaskK_eval`,
`stripMaskK_width`, `rtBridgeK_eval` mirror the originals).  Runtime
check on EVERY slot of both replayed bodies of both circuits (shareX4
6/6, crc16 18/18, Opt and RT): `stripMaskK` strips exactly what
`stripMask` strips and the normal forms equal the originals'.
Generator: per slot ONCE `{f}_sdeep_wokO_*` (body-independent), per
slot per body `{f}_sdeep_hresL_*{tag}`, `{f}_sdeep_maskEq_*{tag}`,
`{f}_sdeep_wokX_*{tag}`, all `rw [hresL…]; decide`; `toOrig` calls
`rtBridgeK_eval` with the three named facts; the pre-check's runtime
normal form uses `stripMaskK`.  Parse oracle and trace untouched.
Measured (same harness as steps 9/10, fresh cgroup, one run each):

| | before (step 10) | after (step 11) |
|---|---|---|
| shareX4 run / runOpt / svOpt / runRT / parses aux | 2 / 20 / 21 / 20 / 1 | 2 / 2 / 3 / 2 / 1 |
| shareX8 runOpt / svOpt / runRT aux | 32 / 33 / 32 | 2 / 3 / 2 |
| crc16 run / runOpt / runRT / parses aux | 1 / 55 / 55 / 1 | 1 / 1 / 1 / 1 |
| ConeSharingGen (both shareX*) wall | 28 s | 31 s |
| crc16 wall / cgroup peak | 107 s / 2.10 GB | 122 s / 2.13 GB |
| skips | none / crc16 exactly the one SV skip | unchanged |

The wall/peak deltas are single runs on a shared machine, not
attributed (the earlier 107 s vs 109 s spread was of that size too).
Remaining axioms of each FINAL theorem, by name (`#print axioms`):
`{f}_sdeep_signal_run`, `_signal_runOpt`, `_signal_runRT` — standard +
the trace's `{f}_sdeep_trace._native.bv_decide.ax_*` only (shareX4:
ax_14, ax_15; shareX8: ax_2, ax_3; crc16: ax_15); `_text_parses` —
standard + `{f}_sdeep_text_parses._native.native_decide.ax_1` (the
parse oracle); `shareX4/8_sdeep_signal_svOpt` — the trace's bv axioms
PLUS `{f}_sdeep_signal_svOpt._native.native_decide.ax_1`, which is the
M4 fragment check `seqCheck wofM (weOf wofM) bodyOpt = true` handed to
`certified_forward_trace_module` (Tools/DeepElab.lean, `hchk`).  So the
expected endpoint — trace `bv_decide` + parse oracle only — holds for
the replay/Opt/RT/text theorems of all three circuits; the SV-semantics
theorem (shareX* only; crc16's is the documented skip) carries one
more, the seqCheck, which is neither the trace nor the parse oracle and
is the next candidate.  Probed (2026-09-20): a bare `decide` on
`seqCheck shareX4_sdeep_wofM (weOf shareX4_sdeep_wofM)
shareX4_sdeep_bodyOpt = true` fails in 3 ms with "did not reduce to
isTrue or isFalse" (a stuck instance, not a timeout; `seqCheck`'s own
axioms are the standard three, so the block is the recursion form or a
`HashMap` lookup inside it, the same two causes met on the cone walk) —
it needs the structural-twin treatment, a separate change.  `bv_decide`
in the trace is a separate item, untouched by instruction.

### C3. crc16 memory, by stage (measured 2026-09-20)

Dependencies prebuilt; each stage in a FRESH `systemd-run --scope`
cgroup; one run each.  Two peak metrics, which measure different
things and must not be subtracted from each other as if they were one:
`child_maxrss` = `getrusage(RUSAGE_CHILDREN).ru_maxrss` of the `lake
env lean` child (includes the ~1.6 GB of `.olean` files it maps, which
are shared page-cache pages); `cgroup_peak` = `memory.peak` of the
fresh cgroup (charges only pages first touched in it, so the already
cached `.olean` pages are excluded).  `memory.stat` read after exit is
near-empty and says nothing about the peak, so the breakdown below was
SAMPLED every second and the sample at the highest `memory.current`
kept (re-runs of stages 3 and 4, fresh cgroups; wall 55 s and 204 s,
peaks 1.536 GB and 2.241 GB — within 1 % of the first runs):

| at peak | anon | kernel | file | file_mapped |
|---|---|---|---|---|
| stage 3 (trace) | 1.29 GB (of which THP 0.86 GB) | 74 MB | 0 | 74 KB |
| stage 4 (full) | 1.70 GB (THP 0.39 GB) | 75 MB | 0 | 74 KB |

So the cgroup peak is the `lean` process's anonymous heap; there is no
file-cache or kernel component of note, and the mapped `.olean` pages
do not appear here (they are charged elsewhere), which is exactly why
`child_maxrss` sits ~1.4 GB above `cgroup_peak` at every stage.

| stage | wall | child_maxrss | cgroup_peak |
|---|---|---|---|
| 1. imports only (`IP.Bus.DroneCANHW`, `Tools.DeepElab`) | 0.6 s | 1.66 GB | 264 MB |
| 2. + synthesize crc16 to IR (94 statements) | 0.7 s | 1.69 GB | 282 MB |
| 3. + trace theorem only (`SPARKLE_DEEP_TRACE_ONLY=1`, new diagnostic switch) | 58.5 s | 2.78 GB | 1.54 GB |
| 4. + replay, optimized body, reparsed body (the full command) | 212 s | 3.23 GB | 2.25 GB |

Reading, stated as deltas of the cgroup metric only and as an
indication, not an exact accounting: synthesis is negligible (+18 MB);
the trace stage is the largest step (+1.25 GB) at 58 s; the replay and
the two bridges add +0.71 GB over 154 s.  **What the command RETAINS (harness `retained.lean`: every generated
constant, value sized as a DAG — what occupies memory — and as a tree;
`ConstantInfo.value?` returns none for theorems here, the value is read
directly):**

| stage / kind | constants | DAG nodes | tree nodes |
|---|---|---|---|
| trace / theorems | 22 | 18 377 | 5 321 212 |
| trace / definitions | 21 | 2 244 | 99 171 |
| replay+bridges / theorems | 378 | 236 957 | 63 193 247 |
| replay+bridges / definitions | 131 | 8 936 | 33 745 |
| total | 552 | ≈ 266 k | ≈ 68.6 M |

Largest: `_sdeep_trace` 17 209 DAG nodes; each `wire_w{k}` 4–6 k
(identical across the three bodies — the same proof three times; the
congruence inside it is body-independent, a dedupe candidate for size
but not for memory); the biggest DEFINITIONS are `weM` 1 028, the three
bodies 537–848, `wtL` 522, `swl` 410 DAG nodes (71 k as a tree — the
wire-list literal is heavily shared).  At ~100 bytes a node the whole
retained environment is on the order of tens of MB, against a 1.29 GB
anonymous peak in the trace stage and 1.70 GB in the full run.
CONCLUSION: retention is not the memory; the peaks are TRANSIENT
elaboration memory (SAT/LRAT for `bv_decide`, `simp`/`signal_lets`
state, kernel checking).  Tree-vs-DAG matters only where something
materialises the tree (none found retained).  **Attributed IN TIME** (STAGE markers now timestamped; `memory.current`
sampled every 0.5 s in the same clock; full run, fresh cgroup, peak
2.27 GB, 204 s).  `memory.current` is the resident high-water mark of a
heap that does not shrink between stages, so the table reads as
"where the level rose", not as per-stage usage:

| segment | wall | level at end |
|---|---|---|
| start → CdoW reified (16 wires), readers + equations | 30 s | 0.25 → 0.69 GB |
| trace theorem (`bv_decide`) | 25 s | → **1.53 GB** (+0.84) |
| replay: G1 glue | 20 s | 1.55 GB (flat) |
| seed + readers | 0.4 s | flat |
| ORIGINAL body: hwfL, hb1/frames, settled + wire lemmas | 95 s | → **2.26 GB** (+0.75) |
| steps, regstep, state trace, run | 0.5 s | flat |
| Opt body, all of it | 15 s | 2.24 GB (flat — heap reused) |
| RT body, all of it | 16 s | 2.27 GB (flat) |

So the peak is set by two places: the trace theorem's `bv_decide`
(+0.84 GB in 25 s) and the original body's wire-lemma segment (+0.75 GB
in 95 s); the two later bodies fit in the heap the first one grew.
The 95 s segment also contains the known kernel `decide`s over the
94-statement original body (`hwfL` ×17 ≈ 35 s, `bodyWidthOk` 4 s),
which the Opt/RT bodies (20 statements) do not pay — which is why they
take 15 s.  **Split further (per-phase and per-wire markers; rerun, peak 2.27 GB,
204 s):**

| sub-phase of the ORIGINAL body | wall | level |
|---|---|---|
| seed + readers → **hwfL facts emitted** (17 kernel `decide`s of `hwfCheckL` over the 94-statement body, one per stop set) | **87.3 s** | 1.54 → **2.25 GB** |
| hwfL → hb1 + frames | 5.1 s | 2.26 GB |
| each `settled w{k}` / `wire w{k}` (32 lemmas) | 0.0–0.2 s each, 2.3 s total | flat |
| steps + regstep + state trace + run | 0.5 s | flat |
| Opt body: hwfL facts (20-statement body) | 9.8 s | flat |
| RT body: hwfL facts | 9.9 s | flat |

So the second contributor to the peak is identified: the kernel
evaluation of `hwfCheckL we stop body` over the 94-statement original
body, repeated for 17 stop sets (16 per-wire + the shared one) — this
is the "large definition expanded 17 times" of the study.  The wire
lemmas themselves, which dominated the TIME profile before the
`natJoin_right` fix, cost nothing here.  With the trace theorem's
`bv_decide` (+0.84 GB, 25 s) these two places account for the whole
rise from 0.69 GB to 2.25 GB.
**Fix DONE (2026-09-20), the user's better derivation:** `bodyWidthOk we
body` (every assign at its wire's width) is strictly stronger than
`hwfCheck` at ANY stop set, and was already a per-body kernel fact
(inline in `hb1_of`).  New generic lemma `hwfCheckL_of_bodyWidthOk`
(Tools/ConeFoldRT.lean); the generator proves `bodyWidthOk` once per
body as `{f}_sdeep_hBWO{tag}` and all 17 hwfL sites (same `weM`, same
body constant — checked) and `hb1_of` reuse it.  No per-stop-set walk
remains; the per-stop-set `native_decide` agreement fact is unchanged.
Measured, same harness, one run each:

| | before | after |
|---|---|---|
| crc16 wall | 204 s | **109 s** |
| crc16 cgroup peak | 2.27 GB | 2.07 GB |
| segment "seed → hwfL facts" (orig body) | 87.3 s, → 2.25 GB | 12.9 s, → 2.07 GB |
| same segment, Opt / RT bodies | 9.8 s / 9.9 s | 1.6 s / 1.6 s |
| shareX4+8 wall | 45 s | 28 s |
| auxiliaries (all theorems, both circuits) | | unchanged |
| skips | crc16 1 (documented), shareX 0 | unchanged |

What remains in that segment (12.9 s, +0.58 GB) is now the three
per-body kernel `decide`s over the 94-statement body themselves —
`woCheck` 6.8 s, `bodyWidthOk` 3.9 s, `noSelfRead` 0.35 s (measured
individually on 2026-09-19) — proven once each.  The trace theorem's
`bv_decide` (+0.8 GB, 25 s) is untouched, per instruction.
crc16 today: 880 s → 109 s; peak 2.80 → 2.07 GB; auxiliaries 152 → 18
on the replay; every obligation, skip and axiom policy unchanged.

### C3b. The trace stage's memory, attributed (2026-09-21)

Question: split the trace stage's +0.84 GB into SAT-problem generation,
solver run, and certificate construction/check; separate what is
retained from what is transient.  Method: a scratch harness that
OVERRIDES the `bv_decide` elaborator with a copy of the real pipeline
(`bvNormalize` → `closeWithBVReflection` → bitblast → CNF → `satQuery`
→ `LratCert.load` → `lratProofToString` → the two `addAndCompile`s →
`nativeEqTrue`), recording monotonic ms + this process's VmRSS/VmHWM at
every phase boundary into the `SPARKLE_DEEP_TRACE` file; a
`sat.solver` wrapper for cadical's own rusage and the CNF/LRAT files;
the 100 ms cgroup sampler; `Elab.async false`; trace-only mode.  (A
first attempt with `trace.profiler` was discarded: recording the trace
tree itself took the run to 153 s and a 3.26 GB peak at the final
print — the profiler is not a memory instrument here.)

**Result: the bv_decide pipeline is not where the memory goes.**  All
its phases together, on the UNSAT call that proves the theorem (crc16,
one run):

| phase | wall | RSS delta |
|---|---|---|
| preprocessing (`bv_normalize`) | 0.16 s | 0 |
| reflection + bitblast (AIG 5 012 nodes) + CNF (5 846 vars, 14 200 clauses, 203 KB DIMACS) | < 10 ms | 0 |
| cadical (own process; exit 20) | 23 ms, 14 MB RSS | — |
| LRAT parse + trim (8 757 steps, 328 KB binary) → certificate string 405 867 B | < 10 ms | 0 |
| compile expr def (13 269 nodes) + cert def + compile-and-run `verifyBVExpr` (the `ax_15` axiom) | 30 ms | 0 |

A second `bv_decide` inside `first | rfl | bv_decide | …` reaches the
solver and is SAT (exit 10, 3 207 vars): that attempt fails as designed
and the next closer runs; its cost is the same order.  RETAINED from
the pipeline, in the environment and the `.olean`: `_cert_def_14`
(405 867-byte string literal), `_expr_def_14` (13 269 tree nodes), the
axiom `_native.bv_decide.ax_15`, and the theorem itself (tree 5.29 M,
DAG 17 k).  Nothing else survives the tactic.

**Where it goes: the KERNEL check of the trace theorem's proof term.**
Re-checking the declared theorem alone (`addDecl` of a copy,
`Elab.async false`): 22.4 s, RSS +0.77 GB, high-water +0.97 GB — the
whole trace-stage growth, and the timeline's steady climb from the
last `bv_decide` mark to the theorem's addition matches it.  Bisecting
the proof by kernel-checking sub-terms level by level (each candidate
closed over its context and re-added under a fresh name) found two
sources:

1. `simp only [rd0_succ]` (6.3 s, one occurrence): the reader equation
   is proven by `rfl`, so `simp` used it as a DEFINITIONAL rewrite — no
   proof term, an `id` type ascription whose two sides differ by the
   unfolding of `rd0 (m+1)` — and the kernel re-derived the whole
   `CdoW.stateAt` step (re-checking `rd0_succ` alone: 6.1 s, +0.31 GB).
   Fix: drop the `simp only` line; the `rw [rd0_succ]` that followed it
   now fires and rewrites WITH the theorem the kernel checked once.
   Commit `347b6b7`: 22.4 → 16.1 s, +0.77 → +0.61 GB.
2. bv_decide's reflection proof (16 s): a chain of 71 `sat_and` nodes,
   one per hypothesis, each closed by the defeq `eval atoms E ≡ hyp`.
   Marginal-cost profile along the chain (kernel time of the sub-chain
   from node k: 16.1 s at k = 0…40, 12.7 s at 48, 8.2 s at 56, 3.7 s at
   64, 0 at the end): the 40 DSL-side hypotheses (`hval_sl_*`, atoms
   are fvars) cost nothing; the 16 IR-side wire equations `fm_k :
   rw{k} args m = cone` cost ~1 s each.  Same shape, same size — the
   difference is that the IR atoms `rw{k} args m` / `rd0 args m` are
   DEFINITIONS of large height, so the kernel's lazy delta unfolds them
   (the symbolic `CdoW.wenv` evaluation) while matching.  Fix: make the
   atoms opaque variables before `bv_decide`.  Core `generalize … at *`
   does this in the elaborator but NOT in the kernel term: it assigns
   `(fun a … => ?body) e …` and `instantiateMVars` beta-reduces the
   redex, putting `e` back (measured: proof restructured, 16.0 s
   unchanged, atoms still constants in the chain).  `sparkle_opaque e
   as a` (Tools/DeepElab.lean) closes the goal with `letFun e (fun a =>
   ?body)` instead — a constant application, left alone by
   `instantiateMVars`, checked by the kernel with `a` opaque — after
   reverting every hypothesis mentioning `e`; no `e = a` equation is
   kept.  Applied to every `rw{k} args m` and `rd{i} args m` before the
   step closer and before the output closers' `bv_decide`.

Measured after both (same harness, one run each; every PROVEN clause,
auxiliary count, skip and axiom unchanged on shareX4/8 and crc16):

| | before | after 1 | after 1+2 |
|---|---|---|---|
| trace theorem kernel re-check | 22.4 s, RSS +0.77 GB | 16.1 s, +0.61 GB | **0.08 s, +15 MB** |
| crc16 trace-only stage (`SPARKLE_DEEP_TRACE_ONLY`) | 58 s, cgroup peak 1.48 GB | 50 s, 1.14 GB | **32 s, 0.73 GB** |
| the trace theorem inside it (begin → added) | 26 s | 19 s | **1.0 s** |
| crc16 full build | 122 s, peak 2.13 GB | 114 s, 2.10 GB | **97 s, 2.07 GB** |
| ConeSharingGen (shareX4+8) | 31 s | 31 s | 27 s |

The full build's peak is now set by the original body's hwfL kernel
`decide`s (the +0.71 GB segment above), which is the next candidate.
Transient vs retained, answered: the trace stage's growth was
transient kernel working memory (it does not survive the check and is
gone now); the retained part of the trace theorem is the ~0.5 MB
listed above.

### C3c. The original body's seed → hwfL segment, per declaration (2026-09-22)

Instrument: `elabSyncS` now writes `DECL <name> begin/end rss_kb=…`
markers (monotonic ms + VmRSS) into the `SPARKLE_DEEP_TRACE` file
around every generated declaration; the generator elaborates each one
with `Elab.async false`, so a marker pair covers elaboration AND the
kernel check.  Full crc16 run, synchronous, 100 ms cgroup sampler
(`mem/s34_sync.lean`, `mem/full1.trace`): 578 declarations, 96.8 s of
declaration time in a 99 s run.

The segment (`seed + readers emitted` → `hwfL facts emitted`, original
body): 13.2 s, 50 declarations, ΣΔRSS +605 MB.  What is in it TODAY
(names and proof methods as generated — the 17 `hwfCheckL` walks of the
2026-09-20 study are gone; the `hwfL_*` facts are term-mode instances of
`hwfCheckL_of_bodyWidthOk` and do not appear in the top 15):

| declaration | proof | time | ΔRSS |
|---|---|---|---|
| `crc16CcittHW_sdeep_hWO` | `woCheck_sound [] body (by decide)` | **7 156 ms** | **+623 MB** (the largest RSS step of the whole run) |
| `crc16CcittHW_sdeep_hBWO` | `bodyWidthOk weM body = true := by decide` | 3 915 ms | +2 MB |
| `crc16CcittHW_sdeep_hNSR` | `noSelfReadCheck_sound _ (by decide)` | 371 ms | 0 |
| `hsub_r0`, `hsub_w0`, `hsub_out` | `rw [resolveSlicesT_list]; decide` | 250–300 ms each | ≤ 21 MB |
| the other 45 (`hsub_w*`, `stv`, `rhoNS`, `envSt`, `st0`, `rhoNS_eq`, `envSt_bounded`, `henv`, `wofM`, `weOf_eq`, `signalM`, `hMF`, 17 `hwfL_*`) | — | < 90 ms each | ≈ 0 |

(For the record, the largest declarations of the WHOLE run: `rw14_eq`
8.8 s / +149 MB, `rd0_succ` 7.7 s, `hWO` 7.2 s / +623 MB, `rw12_eq`
4.1 s, `hwt` 4.1 s / +466 MB, `hBWO` 3.9 s.)

**`hWO`, split.**  `woCheck done body` walks the 94 statements; per
statement it recomputes `writesOf rest` for every read and every write
name and tests membership with `List.contains` on `String`.  Counted at
runtime: 13 740 string comparisons (upper bound; almost every `contains`
scans the full list because the answer is "absent"), 9 696 statement
visits by `writesOf`, names ≈ 11 characters.  Measured in a fresh
process (`mem/kwo.lean`):

| | time | note |
|---|---|---|
| fresh `by decide` | 6 851 ms | elaborator evaluation + kernel check |
| fresh `by decide +kernel` | 3 320 ms | kernel only |
| kernel re-check of the declared `hWO` | 3 316 ms, **RSS +1 264 MB** | first big allocation in that process |
| 93 names each looked up in the 93-name write list (93 × 93 comparisons), `decide +kernel` | 1 718 ms | the membership sweep alone, over half of the kernel half |
| the `writesOf` recomputation alone (lengths only, no string compare), `decide +kernel` | 75 ms | the checker's list walking is not the cost |

So: (i) the default `decide` evaluates the checker TWICE — once in the
elaborator, once in the kernel — the elaborator half is 3.5 s of the
7.2 s and is pure duplication; (ii) the kernel half is almost entirely
`String` equality (the kernel unfolds `String.decEq` down the character
list), and that is also where the +0.6–1.3 GB is allocated; the
checker's own structural work is < 0.1 s.  (C3d measures the
per-comparison cost properly — ≈ 0.04 ms, scaling with name length —
and withdraws a "0.3 ms per comparison" figure that an earlier draft of
this section obtained by dividing a whole sweep by its comparison
count.)

**Change (one declaration): `hWO` by `decide +kernel`.**  The proof is
`of_decide_eq_true (Eq.refl true)` behind an auxiliary lemma checked by
the kernel; axioms of the result: `propext` only (checked).  Before /
after, same instrumented full run, one each:

| | before | after |
|---|---|---|
| `hWO` | 7 156 ms, +623 MB | 3 401 ms, +619 MB |
| `hWOOpt` / `hWORT` (20-statement bodies, same line) | 402 / 357 ms | 189 / 171 ms |
| segment seed → hwfL | 13.2 s | 9.4 s |
| total declaration time | 96.8 s | 92.6 s |
| cgroup peak (sampler) | 1.95 GB | 1.94 GB |
| `lake build` ConeSharingCrc16 | 97 s, peak 2.07 GB | 93 s, peak 2.02 GB |

Every PROVEN clause, auxiliary count, skip and axiom unchanged
(shareX4/8 and crc16).  The +0.6 GB of `hWO` is NOT the elaborator
pass: it stays with the kernel's string comparisons.

Same change measured on the small circuits (fresh process, one run
each; axioms of the result: `propext` only):

| | `by decide` | `by decide +kernel` |
|---|---|---|
| shareX4 (25 statements, 24 names) | 515 ms, +114 MB | 241 ms, +0 MB |
| shareX8 (41 statements, 40 names) | 1 487 ms, +201 MB | 703 ms, −1 MB |

### C3d. `woCheck`'s string matching: measured, NOT fixed (2026-09-22)

The remaining 3.3 s / +0.6 GB of `hWO` is the kernel deciding `String`
equality.  Four reformulations were measured before stopping; each is
recorded because the numbers, not the intuitions, decide this.

**What the cost actually is.**  Per-comparison, on realistic names,
`decide +kernel` over 1 000 repetitions: `==` between two distinct
17-character names 40 ms, `<` 56 ms, shared-prefix pair 40/63 ms — i.e.
≈ 0.04–0.06 ms per comparison, NOT the 0.3 ms quoted in C3c (that
figure divided a whole `contains` sweep by its comparison count and is
withdrawn).  The cost scales with NAME LENGTH at a fixed comparison
count — 93 × 93 `List.contains` over string literals:

| names | time | ΔRSS |
|---|---|---|
| 93 × 2-character literals (`n0`…`n92`) | 795 ms | +312 MB |
| 93 real crc16 names (avg 12, max 17 chars) | 1 686 ms | +12 MB |
| 93 × 28-character literals | 7 245 ms | +2 602 MB |
| 93 identical 1-character names (no mismatch scan) | 8 ms | 0 |

So the kernel unfolds `String.decEq` down the character list; `List
String` membership over long generated names is inherently expensive
for it.  `String.hash` does not reduce in the kernel at all (`decide`
gets stuck), so a hash pre-filter is not available; even
`String.length` over the 93 names costs 901 ms.

**Reformulations tried.**
1. *Sorted association list, name → writing statement index*
   (`insSorted`/`lookSorted`/`writeIndex`/`readsBefore`, drafted in
   `mem/wofast.lean`): O(N log N) comparisons instead of O(N²), runtime
   agreement with `woCheck` on all three crc16 bodies (orig/Opt/RT).
   Kernel cost: **6 867 ms, +1 962 MB — 2× WORSE** than the 3 286 ms /
   +27 MB of `woCheck` itself.  The `Option`/`bind` allocation in the
   fold outweighs the comparisons saved.  Discarded.
2. *Name-erased Nat-keyed twin* (names replaced by table indices): the
   Nat-keyed membership pattern costs **115 ms** — a genuine 30× win —
   but it needs the side condition that the name table is duplicate
   free, and THAT obligation is 93 × 93 String comparisons: **3 204 ms,
   +1 099 MB**, i.e. exactly the cost being removed.  Net zero.
   Discarded.
3. *Shorter IR wire names* (the measured lever: 2-char names would put
   the sweep at ~0.8 s).  The names are emitted by
   `Sparkle/IR/Builder.lean` (`_gen_*`) and the expression flattener
   (`_tmp_op_a_*`), and they appear in the printed Verilog, in
   `Backend/Partition.lean`'s prefix tests, and in `Backend/CSim.lean`.
   Renaming them changes generated RTL and ripples through three
   backends — a design change well outside this PR.  **Recorded as the
   next milestone's candidate, not attempted.**
4. *Proving the check by a general lemma instead of evaluating it*:
   `∀ l, l.all (fun n => l.contains n) = true` is instant (0 ms), but
   `woCheck`'s real content is not a tautology — it is a property OF
   this body — so there is nothing general to appeal to.  The obligation
   has to be evaluated on the body, one way or another.

**Conclusion and limitation.**  Within this PR's scope the string
matching is measured but not removed: every local reformulation either
loses (1), moves the same cost to a side condition (2), or requires
renaming IR wires across the backends (3).  `hWO` stays at 3.4 s /
+0.6 GB on crc16 (with the `decide +kernel` win of C3c banked), and
`hBWO` at 3.9 s has the same shape (`weM` lookups keyed by string).
Both are name-length-bound kernel `String` work; the lever is (3) and
it belongs to the next milestone together with the other performance
items.

## D. Trust base

- [x] **`native_decide` → `decide` hardening, first pass** (2026-09-08).
  The body-only, list-shaped checkers now discharge by KERNEL `decide`
  in the deep generator: `memFreeCheck`, `noSelfReadCheck`,
  `syncMemOnlyCheck`, `woCheck` and `bodyEvalOkM` (16 sites).  Measured
  on `regFile_rdata_deep_signal_run`: 108 → 76 `native_decide` axioms,
  all 45 PROVEN lines unchanged.
  Remaining 36 sites are the ones that genuinely cannot kernel-reduce:
  everything keyed on a `Std.HashMap` (`stopAtM` / `wtM` — USize
  hashing), the `inlineConeT` / `resolveSlicesT` cone equations, and
  the `concatNorm` singleton-freedom check.  Making those kernel-checkable
  means list-backed stop sets and width tables carrying their own
  lookup lemmas.
- [ ] Closed hierarchical semantics (`.inst` as state trees /
  flattening proof).  Research boundary; hier co-sim covers it
  dynamically today.  Also blocks the CompCert claim — see F6.

## E. Housekeeping

- [x] CI green (Build: umbrella imports + `sparkleModuleDeps` +
  SVParser hard-link args; zero-width symbolic-width guard).
- [x] PR #134 body refreshed (seam / composition / bug #14).
- [x] `docs/CertifiedRoundtrip-design.md` — seam / composition / bug
  #14 sections added; bug numbering aligned to the PR table (14).
- [x] Zero-width pin test — a compile-time `run_cmd` in VerifyElabDemo
  asserts no `logic [0:0]` remnant (the exe path hits the circuit-do
  inline-synth gap, so the pin lives in the `lake env lean` file).
- [ ] Untracked scratch files at repo root (`episode.json`,
  `multiDeck.json`, `schedule`, resubmission draft) — decide keep vs
  gitignore vs remove.

## F. CompCert-class guarantee

**2026-09-25 printer continuation (partial, not an end-to-end text theorem):**
`Tools/ShippingPrintSoundness.lean` proves shipping expression/assignment/body
text equals rendering of the existing SV AST, for the nested six-operator
fragment. A successful `optCheck` derives the optimized body's shape premise.
Expression-level SV semantics composes with the rendering equality under the
existing explicit `sf4Check`/boundedness hypotheses. Standard-axiom audit and
focused tests are in `ShippingPrintSoundnessTest`, imported by `Tests.AllTests`.
`ShippingModulePrintSoundness.emitModule_render` now extends byte equality
to the ENTIRE module (headers/ports/wires included), under explicit concrete
positive-width declaration and assignment-shape hypotheses. The optimizer
check supplies the body-shape hypothesis via `acceptedOptimizer_module_render`.
Tests include an arbitrary-width family and the real optimized `fragA` string.
`ShippingPrintEntrySoundness.printedModule_render` now derives all renderer
premises from the SAME actual synthesis run, under the existing `EnvDefines`,
fragment well-formedness and positive-width assumptions. The translator's
`DeclFrame` and entry's `DeclReady` carry metadata/type facts; cleanup supplies
positive wire widths. The shipping optimizer now preserves `printDeclsCheck`
when the input satisfies it, otherwise retaining the original module via the
existing fallback. Both accepted and fallback body grammars are proved.
`fragA_text_render` applies the theorem to the real declaration; negative tests
reject metadata/type changes the old semantic checker alone would accept.
Still open: identifier legality (sanitize-fixed is not enough: `1bad`,
`module`), fallback width/`assignsCheck` derivation, and composition of the
source semantics with SV evaluation. Byte equality is not parsing or RTL
semantic equivalence. Do not mark the printer complete.
See the printer continuation section of `ShippingCompiler-Soundness.md` for
the ordered next steps and review of option A.

**2026-09-26 tutorial / theorem packaging:**
`compiledFragment_artifact` combines source/optimized-IR agreement and
AST/printed-byte correspondence for one actual synthesis run. It does not
claim SV semantic equivalence or expand the source fragment. The executable
[tutorial chapter 7c](tutorial/md/Ch07c_VerifiedCompiler.md) applies it to the
real `plus8` declaration and audits its axioms, with the remaining connections
shown explicitly. Next proof work remains lexical validity and deriving
`assignsCheck`/width-environment conditions on both optimizer arms.

**2026-09-26 conditional SV bridge:** `compiledFragment_forward` now composes
source semantics with the existing SV assignment-fold semantics of the ACTUAL
emitted AST, under explicit `forwardCheck` and bounded-initialization premises.
`module_combItems` identifies the AST's assignments with `emitAssigns`;
`evalAssigns_widths` bridges source wire-only widths to printer widths including
output ports. The old width environment gives `out` width zero, so using it
directly for `assignsCheck` rejects even the real positive-width fragment.
Tests cover four real declarations, raw/optimized, and a counterexample to
`optCheck ⇒ forwardCheck` (unused assignment with mismatched target width).
This step changes no compiler behavior and discharges NO source-entry forward
check premise. Next: prove the fallback's check and initialization conditions,
then preserve them through optimizer acceptance; lexical/text interpretation
and independent AST declaration widths remain explicit boundaries.

**2026-09-26 core width premise derived:** `Inv.sized` is preserved by the
actual translator and initialized at the entry, so `PostReady` now exposes
uniform sizing of every emitted RHS, including the output read. Under wire
sanitizer stability, `core_forwardCheck` derives `forwardCheck` for the actual
CORE result, without a width premise. `dropZeroWidth_sized` carries the sizing
invariant through cleanup. This did NOT discharge the final optimized-run
check; merge transport and optimizer preservation were the next steps.
Name stability also remains separate; a real `«a#»` binder demonstrates it is
not automatic. Bounded initialization and lexical validity are still open.

**2026-09-26 merge transport and fallback check derived:**
`validateMerge_sized` proves the actual checker's accepted body has uniform
RHS sizing, including the output read, without assuming anything about the
raw merge proposal. `postprocess_sized` and `synthesizeCombinational_sized`
connect it through cleanup/merge to the returned module.
`synthesized_forwardCheck` now derives the entire pre-optimizer forward
check under wire sanitizer stability; there is no width/check hypothesis.
Tests audit standard axioms, apply the theorem to the real `fragA`, exercise
an accepted duplicate-constant merge and reject an unequal-width alias.
The runtime forward checks also include the real `dupLit` merge example.
Next: preserve the check through optimizer selection. The final optimized
`compiledFragment_forward` premise is NOT discharged yet; name stability,
bounded initialization, lexical validity and the text/grammar boundary remain.

**2026-09-26 optimized forward premise discharged:** shipping
`PrintCheck.moduleCheck` is a pure sufficient check, proved to imply
`forwardCheck` by `printCheck_forward`. The source entry establishes it
(`synthesized_printCheck`), and `optCheck` now requires accepted candidates
to preserve it whenever the original passes. `checkedOptimize_printCheck`
proves both the accepted-candidate and unchanged-fallback branches.
`compiled_forwardCheck` connects the complete selection to the actual run;
`compiledFragment_forward` now has NO optimized-check hypothesis. Remaining:
wire sanitizer stability, bounded initialization, lexical validity and the
text/grammar boundary (plus the existing fragment and `EnvDefines` scope).
Tests require the real small-fragment optimizer proposals to be accepted,
reject the old unused-width counterexample, and audit standard axioms only.

**2026-09-26 constructed initialization:** `inputEnv` supplies source values
at their allocated input ports and zero elsewhere. `inputEnv_input` proves
the correspondence using the source-derived injective port map;
`inputEnv_bounded` derives bounds from `BitVec.isLt`. The actual shipping
optimizer now preserves printer widths of ALL inputs on the checked route,
including unused ones (`inputWidthsAgree`). A pinned negative example changes
an unused input's internal declaration from 8 bits to 1: output and expression
checks still pass, but initializing that input to 255 breaks boundedness.
The new guard rejects this proposal. `compiled_inputWidths` derives the
required widths from the source entry through both optimizer branches.
`compiledFragment_forward` now constructs initialization itself and has no
boundedness/input-environment hypothesis; the old arbitrary-environment form
is retained as `compiledFragment_forward_with_initial`. General applications
to `fragA` and tutorial `plus8` reach actual SV assignment-fold evaluation.
Remaining at that stage: source-result name stability (discharged by the
repair below), lexical/text interpretation and independent AST declaration
semantics, plus `EnvDefines` and fragment scope.

**2026-09-26 actual input-port declarations:** `emitAstModule_input` interprets
the actual port's literal range without consulting IR widths.
`compiled_inputTypes` and `compiled_inputDecls` derive, from the same successful
source run, an unsigned SV input declaration of width `n` for every source
input, including unused inputs. The result is now part of
`compiledFragment_forward`, not a disconnected helper or another premise.
The `fragA` and English tutorial `plus8` theorems retain that conclusion;
all new general lemmas are axiom-audited. Internal/output declarations and
concurrent semantics remain open.

**Naming BUG identified before the repair below:** `hashCollision` with
inputs `«a#»` and `«a##»` succeeded at `synthesizeCombinational`, but printing
mapped its two distinct IR input names to the same `_gen_«a»`. The old
name-stability hypothesis excluded the example and could not be discharged
without changing the compiler. The initial reproduction checked that
`forwardCheck` excluded it; after the repair it checks correct acceptance.
The fix must preserve bindings across declarations and uses, rather than
silently replacing the user's IR-success goal with a narrower
printing-success goal. `EnvDefines`, fragment coverage, whole-AST width
interpretation and text/concurrent semantics remain explicit.

**2026-09-26 naming repair and premise discharge:** `freshName` now normalizes
non-identifier characters after stripping hygiene and BEFORE searching for a
fresh name. `NameHints.clean_ok`, `freshName_clean`, and `makeWire_clean` are
general proofs; existing freshness covers distinct hints with equal normalized
forms. The actual translator carries `DeclFrame.wireNames`, the entry derives
`DeclReady` from an empty initial module, and cleanup/merge retain those wires.
`synthesized_names` closes the printer-stability obligation from the same run.
The final `compiledFragment_forward` no longer accepts a wire-name hypothesis.
`fragA`, tutorial `plus8`, and the previously failing `hashCollision` all apply
that stronger general theorem with standard axioms only. Regression cases
exercise both the original printer collision and equal normalized hints.
No source restriction or refusal is added. Module naming and independently
created port names are not covered by this allocation repair; the complete
lexical/text contract and concurrent semantics remain open, together with
whole-AST width interpretation, `EnvDefines`, and the fragment restriction.

Repair validation: allocator/bridge tests, tutorial and `lake test` pass;
new general lemmas and the real collision-source theorem use only standard
axioms. Both collision regressions reparse actual output and preserve input
values. The saved pre-repair corpus comparison covers 302 module texts from
298 synthesis commands in 119 files: byte-identical, with unchanged exit
statuses (two existing error-example files remain errors).

**2026-09-26 output observation:** `declaredOutputWidth` reads the actual
unsigned output port's range without consulting IR widths.
`emitAstModule_outputWidth` and `compiled_outputWidth` derive width `n` from
the same successful run, including both cleanup and optimizer branches.
`compiledFragment_forward` now concludes both that declaration-width fact and
that `observeUnsignedOutput` of the final assignment environment equals the
source. No new caller premise. The mask cannot change a `BitVec n` value,
which is bounded by construction. `fragA`, `hashCollision` and tutorial
`plus8` retain the observation conclusion; new general lemmas are audited for
standard axioms only. This closes the observed output boundary, NOT the
entire evaluator width map or concurrent RTL semantics. Next: internal
declarations and lookup/shadowing agreement, together with the still-open
lexical/text contract. No shipping compiler behavior changed in this step.
Validation: bridge tests, executable tutorial and `lake test` pass, with
standard axioms only in the new general proofs and real-source applications.

**2026-09-26 whole declaration lookup:** `ShippingDeclWidths.astWidths`
reads all evaluation widths from the actual emitted AST. The new
`optimizeModule_wires_subset` proves directly that the shipping optimizer
only filters declarations. Together with entry uniqueness, input bindings,
output separation and cleanup preservation, `compiled_declarations` derives
that a name has one declaration type. This justifies both suppression of
port-backed wires and reordering the lookup from wires-first to ports-first.
`compiled_astWidths` proves lookup equality at every name;
`compiledFragment_astWidths` now evaluates using the AST-only lookup and
retains the source-value and declared-output observation conclusions.
There is no new premise or compiler change. A malformed same-name 16-bit
wire/8-bit port demonstrates why emission alone is insufficient.
Next boundaries: lexical/text interpretation and concurrent RTL semantics;
`EnvDefines` and the restricted source fragment remain explicit.
Validation: bridge tests, generated English tutorial, `lake build`, and
`lake test` pass; new general theorems and source applications use only the
three standard axioms. No shipping compiler change or new assumption.

**2026-09-26 simultaneous equations — conditional bridge completed:**
`ShippingSettledSoundness` proves ordered single-assignment folds produce
unique simultaneous solutions with fixed undriven inputs. Equation membership
is order-independent. `module_settled` connects this to the actual emitted
AST and its own widths; `compiledFragment_settled` retains the source/text
conclusions but has an explicit NEW `Acyclic (checkedOptimize m).body`
hypothesis. The shipping pipeline has not yet discharged it. Existing
in-order theorems are unchanged.

A negative control passes `optCheck` yet has an unused forward dependency,
so output equivalence alone cannot establish this ordering property. This
is a checker counterexample, not evidence the actual optimizer produces it.
The next proof obligation is ordering through actual translation, cleanup,
merging and both optimizer branches. Simulator scheduling, four-state values
and lexical/text interpretation are still outside this result.
Validation: new settled-semantics tests, executable English tutorial,
`lake build` and `lake test` pass. The new conditional source theorem and
supporting lemmas use only the standard axioms. No compiler behavior changed.

**2026-09-26 shipping leaf order:** `ShippingTranslationOrder.OrderInv`
records acyclicity of the reversed builder body and reservation of every
read/written name. `Pending` is stronger than reservation: the existing body
has not read or written that name. This distinction is necessary because the
binary handler allocates its result before translating its operands.

`makeWire_order` and `emitAssign_order` follow the actual builder operations.
`translateSignalPureLiteral_order` covers both literal emission and the
unsupported-payload no-op. `translateExprToWire_leaf_order` follows the actual
recursive entry for fvars and supported literals, including cache hit/miss and
recording, with no recursive order assumption. `translateExprToWire_leaf_settled`
consumes it with the existing semantic theorem to produce a unique simultaneous
solution carrying the source value. At this translator boundary, initial
semantic/order/binding invariants and final width agreement remain explicit.

This is a separate structural invariant, not yet incorporated into the full
recursive `Spec`. Remaining: prove that binary operand translation preserves
the pending parent result and returns a usable wire (including cache records),
then establish the invariant at the synthesis entry and transport it through
output emission, cleanup, merging and optimizer selection. The final
`compiledFragment_settled` acyclicity premise is NOT discharged by this step.
No compiler behavior, acceptance rule or previous theorem premise changed.
Validation: the order/settled tests, English tutorial, `lake build` and
`lake test` pass. The leaf entry and settled corollary pass the standard-axiom
audit. Tests distinguish reserved-but-pending names from a self-dependent
assignment and apply the entry theorem to a concrete quoted literal.

**2026-09-26 recursive translator order — binary case closed:**
`ShippingPendingSoundness.Protected` records a reserved parent result absent
from the current body's footprint, meaningful source bindings and meaningful
cache records. `translateExprToWire_protects` proves arbitrary nested
translation cannot read, write or return it, including validated cache hits.
This is proved by fuel induction alongside the existing structural `Spec`;
there is no recursive hypothesis at the real entry.

`binary_orders` derives protection for its freshly allocated result from the
existing `Inv.lookup` and `Inv.record`, preserves it through both operand
translations, and uses the resulting non-self-reference to emit the assignment
last. `translateExprToWire_orders` closes the order induction for all supported
combinations of inputs, literals and canonical `+ - * &&& ||| ^^^`.
`translateExprToWire_settled` consumes this theorem with existing semantic
preservation: the actual translated body's unique simultaneous solution
carries the source value. It has no leaf restriction, recursive premise or
caller-supplied `Protected` condition.

The translator boundary still takes initial `Inv`/`OrderInv` and final
`WidthsAgree`. The FULL synthesis-to-SV theorem's `Acyclic` premise is still
open: connect initialization and output emission, then preserve order through
cleanup, checked merging and optimizer selection. This step does not enlarge
the source-language fragment or change compiler behavior. In particular it is
not a proof for the unverified fallback handlers.

Tests apply the actual-entry theorem to a nested add/multiply expression and
show that a reserved, body-absent name with a meaningful cache record fails
`Protected`. The cache condition is not silently equated with body absence.
Validation: targeted tests, the executable English tutorial, `lake build` and
`lake test` pass. All new audited proofs use only the three standard axioms.

**2026-09-26 synthesis core order — initialization and output connected:**
The foundational IR assignment/equation theory now lives in
`Tools/ShippingAssignmentOrder.lean` (same theorem namespace), removing the
import cycle between translator order and the synthesis entry. In
`synthesizeCertified_sound`, the empty initial body supplies `OrderInv`;
the already-derived `Inv` and width agreement instantiate the recursive order
theorem. The final `out := w` cannot read itself: the returned wire is reserved,
while the actual output-name check establishes that `out` is not reserved.
The footprint invariant likewise excludes `out` from all earlier reads/writes.

`PostReady` now includes `Acyclic M.body`, derived at the actual core entry.
`fragmentDecl_core_settled` gives a unique simultaneous IR solution whose
output equals the Signal declaration at every cycle, with no caller-supplied
order premise. It retains the same `EnvDefines`, quoted-fragment and input
valuation boundaries. `fragA_core_settled` applies it to the real declaration;
it does not perform a per-instance semantic certification.
`dropZeroWidth_entry_order` transports order across positive-width cleanup,
using the already-proved body identity.

Remaining: prove order preservation of checked merging and optimizer selection,
then remove the extra `Acyclic (checkedOptimize m).body` premise from the final
SV theorem. The existing optimizer output-equivalence check alone does not
imply order (the earlier accepted forward-reference counterexample still
applies). No compiler behavior, supported fragment, lexical/text boundary or
external RTL execution model changed in this step.

Validation: entry/settled regressions and their standard-axiom audits, English
executable tutorial, `lake build` and `lake test`. No compiler corpus or
performance rerun is claimed for this proof-only change.

**2026-09-26 post-processing order — checked merging connected:**
`validateStep_order` follows the shipping validator: targets are unchanged,
new references are either original references or point into `st.defined`,
and substitution aliases only target that completed prefix.
`validateMerge_go_order` carries this invariant along the checked statement
pairs and proves both target-list equality and `Acyclic` preservation.
`mergeDuplicates_order` covers accepted proposals and unchanged fallbacks;
`postprocess_order` also covers the environment-variable path that skips merging.
No extra runtime validator or compiler behavior change is needed.

`synthesizeCombinational_settled` now reaches the actual returned IR after
zero-width cleanup and checked merging. Under the existing environment,
fragment, positive-width and input-valuation conditions, it supplies the
assignment order and a unique simultaneous IR solution whose output is the
Signal declaration's value. `fragA_synthesized_settled` applies the general
theorem to the real declaration without a circuit-specific certificate.

The next order obligation is **optimizer selection only**: the final SV theorem
still assumes `Acyclic (checkedOptimize m).body`. Output equivalence alone does
not imply this, as the existing negative test shows. First inspect the actual
optimizer's transformations for order preservation; do not strengthen a theorem
by silently assuming the existing `optCheck` establishes it. Lexical validity,
text interpretation, external RTL execution, and larger source fragments remain
separate unfinished work.

Validation: a successful alias-producing merge with a later rewritten use,
rejections of forward/self-reference proposals, actual-entry application,
standard-axiom audit, English executable tutorial, `lake build`, and `lake test`.
This is a proof-only change; no corpus or performance measurement is claimed.

**2026-09-26 optimizer selection connected — final order premise discharged:**
The shipping `checkedOptimize` now requires `assignmentOrderCheck o.body` in
addition to its existing `optCheck m o` before accepting a proposal on the
simple-body route. Rejected proposals return the original module as before;
other routes still use the unchecked optimizer. The structural checker permits
external reads, rejects duplicate targets, self-reads and forward dependencies,
and is proved equivalent to `Acyclic` by `assignmentOrderCheck_iff`.
`checkedOptimize_order` therefore covers accepted and fallback branches.
This certifies result selection, not the implementation of each optimizer pass.

`synthesized_order` derives order from the same successful synthesis run and
its environment/fragment conditions. `compiledFragment_settled` now consumes
this fact and the optimizer-selection theorem internally: its former
`Acyclic (checkedOptimize m).body` hypothesis is REMOVED. The theorem combines
actual text rendering, declared AST widths, source input initialization, output
observation and a unique bounded simultaneous two-state solution for the
emitted assignments. `fragA_final_settled` applies it to the real declaration
without an order hypothesis or a circuit-specific semantic certificate.

The remaining boundaries have not disappeared: `EnvDefines`, the quoted
positive-width combinational fragment, complete lexical validity and text
interpretation, and external RTL scheduling/four-state behavior. Other accepted
handlers, registers, memories, hierarchy and larger language coverage remain
outside this theorem. This is the completion of the assignment-order connection
for the fragment, not a whole-language CompCert claim.

Tests retain the old counterexample: `optCheck` alone accepts the unused forward
dependency, but the new combined acceptance rejects it. Self-reference and
duplicate targets are rejected too. Real fragA/B/C/D and dupLit optimizations
that the old policy accepts still pass the added check. The final theorem and
its real-declaration application are audited for standard axioms only.

Validation: the 119-file synthesis sweep compared the old selection expression
(`optCheck` only) with the new shipping selection in the same process. All
298 emitted modules were byte-identical. File exit statuses matched the prior
sweep, including the existing failures in VerifyVerilog and TestErrorDetection;
this is not a claim that all 119 files passed. Entry/settled tests, executable
English tutorial, `lake build` and `lake test` pass. No new performance estimate
is inferred from this run.

**2026-09-26 declaration-name class connected:**
`NameHints.Allocated` strengthens character cleanliness with an underscore
first character. `freshName_allocated` / `makeWire_allocated` prove it for the
actual allocator, including reserved-name suffix searches and temporary names.
`DeclFrame.wireNames` and the entry's `DeclReady` now carry this stronger fact.
No allocator behavior, accepted program or printed spelling changed.

`compiled_dataNames` transports it through cleanup, checked merging and
optimizer wire filtering, retaining input ports and the fixed output `out`.
`compiled_astDataNames` applies it to the actual emitted AST's declaration
table, including port/wire suppression. The final `compiledFragment_settled`
now includes this fact as a conclusion: each declared data name contains only
the allowed characters and starts with underscore, or is exactly `out`.
The caller supplies no name-class premise.

This settles the leading-character examples for DATA DECLARATIONS: a binder
spelled `1bad` or `module` is an allocator hint, never that raw identifier.
The new synthesis regression also reparses its emitted text and compares the
AST; that is a test, not a parser correctness theorem. The general name theorem
and strengthened final theorem have only standard axioms.

Still open: the module-name path, the raw source-name comment (including line
breaks), completeness of a lexical/keyword specification, name binding of all
expression references, and tokenization/rendered-text correctness. The existing
parser keyword list is intentionally limited and is not used as a complete
SystemVerilog standard. This step does not claim to close the lexical boundary
or external RTL execution semantics. Next inspect module-name/comment handling
before claiming a complete artifact grammar theorem.

Validation: SV-bridge and settled tests with axiom audits, executable English
tutorial, `lake build`, `lake test`. This is a proof-only strengthening; no
corpus byte-comparison or performance rerun is claimed.

**2026-09-26 source-name comments — actual prefix protected:**
The backend previously interpolated `m.name` directly into line comments.
A label containing LF or CR could terminate the comment early. Shipping
`commentLabel` now replaces those two characters with spaces, preserving
single-line labels exactly; both normal and primitive/blackbox comments use it.
`moduleComment` constructs the normal header, and the AST renderer uses the same
label policy. This changes comment text only for labels containing LF/CR.

`commentLabel_lineText` proves that the result contains neither LF nor CR;
`commentLabel_eq` proves identity on labels already satisfying this condition.
`renderModule_comment` ties it to a successful rendering: the actual returned
string starts with `moduleComment name`, whose embedded label is single-line.
The final `compiledFragment_settled` now includes both the safe-label fact and
this prefix equality for the actual `verilogOf m` artifact, with no new premise.
All proofs use standard axioms only.

The malicious-label regression checks the shipping emitter's header for both
normal and primitive modules. It deliberately does NOT assert that the entire
module has become legal: `sanitizeName` still has a separate incomplete contract
for module identifiers. Its misleading "valid identifier" docstring is corrected.
Names such as `1bad` and `module`, and arbitrary unsupported characters, remain
outside a complete module-name lexical guarantee. The change does not repair
module-identifier collisions or establish parser/lexer correctness.

Next: define and connect the module-identifier policy (including references to
modules and collision/compatibility consequences), then the remaining expression
identifier and token/grammar correspondence. Do not infer a complete text
certificate from a protected comment prefix or from roundtrip smoke tests.

Validation: printer and final-theorem tests with standard-axiom audits,
executable English tutorial, `lake build` and `lake test`. Normal-name comment
identity is proved generally; no full corpus comparison or performance rerun is
claimed for this step.

The sections above are coverage frontiers of THIS design.  This section
is the different question the user asked (2026-09-09): what separates
the current guarantee from a CompCert-style one?  Each entry names a
specific difference, not an aspiration, so it can be argued with.

Current achieved guarantee: bounded, per-instance semantic chains, with
kernel-checked proofs and explicit residual axioms. The shared route's final
text guarantee is through the shipping parser and IR execution; independent
SV semantics is a separate link and still skips crc16. This is not an
unqualified Signal-to-SystemVerilog or language-wide compiler theorem. The
state-correspondence property is tracked separately in section C. Current
scope/trust: `SharedRoute-Guarantees.md` and `CertifiedAcceptance.md`.

The gaps, in the order they weaken the claim:

- [ ] **F1. Universal quantification over the input language.**  THE
  headline difference.  CompCert's theorem is "for every well-formed
  input"; Sparkle's is "for every module of this corpus (52/52,
  1026/1026 assign RHSs) and for each circuit checked".  Per-instance
  validation is CompCert-legitimate for the optimizer, but the CHAIN
  itself is instantiated per circuit rather than quantified over the
  DSL.  `Cdo.elab_general` / `CdoM.elab_general` are the general
  theorems and are the right shape — what is missing is that reification
  into `Cdo`/`CdoM` is a per-circuit meta-program (`#verify_elab_deep`),
  so a circuit outside the deep grammar has no theorem at all.
  **Completion criterion clarified with the user (2026-09-24):** prove
  `shippingCompile source = success ir → SemanticsPreserved source ir`.
  Failure is allowed; success of the existing compiler defines the domain.
  Neither success on every Lean program nor restricting the theorem to the
  new typed frontend is the target. This includes successful paths outside
  the current deep grammar. The MetaM/environment interface and semantics for
  hierarchical/stateful outputs must be modeled, not hidden in a replay premise.
  See `ShippingCompiler-Soundness.md` for the actual entry points and proof plan.

  **Shipping-compiler worklist:**
  - [x] Fix the formal shape of success/preservation for the real `CompilerM`
    and prove two branches of the actual translator in it (2026-09-25,
    `Tools/ShippingTranslateSoundness.lean`): success predicate with
    bind/pure/lift/throw/get/set rules, oracle model for MetaM, source semantics
    on `Lean.Expr` tied to the library by `rfl`, fuel-knot induction; Signal×Signal
    canonical operators and `Signal.pure` literals. Found and fixed an accepted
    miscompile (operator instance ignored). Remaining premises are listed in
    docs/ShippingCompiler-Soundness.md, "Formal shape".
  - [x] Make the shipping knot a fuel-bounded fixpoint of a non-partial step
    (2026-09-25): `translateExprToWire` is now an ordinary definition; the
    `partial` handler block takes the entry as a parameter. Corpus output
    byte-identical (163/163 files, 297 modules), +5% time.
  - [x] Extend `Spec` with the source-binding invariant; prove the `fvar` leaf.
  - [x] One general theorem through the actual entry for inputs, literals and
    the canonical operators in any combination: `translateExprToWire_sound`.
  - [x] Expression-cache hits on the proved path validated against a pure
    record with `exprDecEq` (no `KeySound`/`InsertSpec` needed on that path).
  - [x] Establish `Inv` and `WidthsAgree` at the synthesis entry, and connect
    declarations to `Denotes` (2026-09-25). Entry made a plain definition with
    a pure front end for the certified shape (corpus byte-identical).
    Post-processing NOT included. CORRECTED (second pass): the first version's
    `∃ ci` was not tied to the run; now `RunsTo` states the same-run
    `getConstInfo`, post-read processing is `synthesizeFromConst ci`, and
    `fragA_ir_correct` applies the theorem to the real `fragA`, with the single
    environment hypothesis `EnvDefines` named.
  - [x] Include post-processing (`dropZeroWidthModule`, `mergeDuplicates`)
    (2026-09-25): `synthesizeCombinational_fragment`, `fragA_ir_correct` on the
    IR `synthesizeCombinational` returns. `mergeDuplicates` is result-checked on
    combinational bodies (`validateMerge`, proved sound; never rejects on the
    corpus).
  - [x] The optimizer before printing (2026-09-25): `checkedOptimize` keeps
    `optimizeModule`'s result on simple-shaped modules only if `optCheck`
    (proved sound) accepts it; `printedModule_fragment` /
    `fragA_printed_correct` reach the module `toVerilog` prints. Corpus
    byte-identical. Printer `emitExpr`/`exprWidthV` made total.
  - [ ] Printed text ↔ SV-subset semantics for the fragment (render the SV AST,
    derive `assignsCheck`, output-port width environment).
  - [ ] Check or prove the merge on bodies with registers/memories/instances
    (and cover the `assertions` the merge rewrites).
  - [ ] Width 0 inside the success region: a width-0 fragment declaration
    synthesizes but is not covered (`n > 0`). Decide: a specification under
    which a dropped zero-width output keeps the meaning, or an explicit refusal.
  - [ ] Give shifts a `Denotes` clause (they are on the certified front end but
    unproved); widen the certified shape (mixed widths, Bool, comparisons, mux).
  - [ ] Coverage beyond quotations: gate accepted ⇒ a meaning exists for every
    accepted body (needs the shift clause and a width argument).
  - [ ] Move the remaining IR-affecting `IO.Ref` caches (types, widths, loops)
    into pure builder state as further handlers are proved.
  - [ ] Lower non-canonical operator instances by their actual body instead of
    refusing them.
  - [x] Identify actual success boundaries: synthesis core, zero-width cleanup,
    register deduplication, symbolic-width entry and hierarchical entry.
  - [x] Measure and fix an accepted miscompile in applicative lowering:
    `fun x y => y - x`, 8-bit inputs 3/10, source 7 versus old IR 249.
    Lower the actual body with scoped argument-to-wire mappings. General
    source application rule proved in `Tools/ApplicativeLowering.lean`; nine
    shipping compilations exhaustively checked at small widths.
  - [x] Prove actual `CircuitM.emitAssign` preserves execution of the existing
    finalized prefix and all other wires (`Tools/ShippingBuilderSoundness.lean`).
    This quantifies over builder states and environments, with local RHS and
    freshness hypotheses; no whole-circuit replay premise.
  - [x] Prove the actual registry mapping and IR RHS semantics of six canonical
    BitVec binary primitives at arbitrary widths; compose with actual emission
    and the scoped `CompilerState.varMap` binding invariant
    (`Tools/ShippingScalarSoundness.lean`). Widths, source/operand correspondence
    and fresh destination are explicit hypotheses, not yet established for all
    successful MetaM executions. Overloaded instance recognition remains open;
    the later state-backed binding step below connects the persistent
    variable-map fallback locally, and the expression-cache step
    (`Tools/ShippingCacheSoundness.lean`, 2026-09-25) proves the hit and
    insertion rules under two explicit key hypotheses — see
    docs/ShippingCompiler-Soundness.md for what those are and why one of them
    cannot be discharged from core today (`Expr.equal` is opaque, so there is
    no `EquivBEq ExprStructEq`).
  - [x] Replace the actual name allocator's suffix loop with a total search
    proved to succeed within `used.size + 1` candidates. Prove freshness and
    preservation of reservations/module for both naming modes, and wire/body
    preservation for `makeWire`. Reserved temporary names are now skipped.
    Compose allocation with scalar emission: no fresh-destination premise
    remains in `allocate_emit_correct`; live bindings must still be reserved.
    See `Sparkle/IR/FreshNames.lean`, `Tools/ShippingAllocationSoundness.lean`
    and the public-builder collision reproduction in the proof plan.
  - [ ] Prove the scalar lowering/builder simulation invariant (including
    expression-cache validity, operand widths and fresh names), then connect
    the applicative rule to it. The current rule alone is NOT compiler soundness.
    - [x] Prove scoped/persistent binding transition rules on the actual list
      and Name HashMap: shadowing, persistent insert, reservation preservation,
      and fresh allocation/write preserving BOTH outer and inner scopes.
      `Tools/ShippingBindingsSoundness.lean` also proves the exact execution
      equation of the shipping `withVarMapping`. A visible-only invariant has
      a pinned counterexample. This is not yet a proof of IO.Ref lifecycle or
      expression-cache validity; no such assumption was added as an axiom.
    - [x] Remove the persistent wire-binding IO snapshot boundary: store the
      table in the actual `CircuitState`, use pure lookup/register operations,
      and prove exact `CompilerM.lookupVar`/`bindSourceVariable` run equations.
      Connect hits and registration to the source-value/reservation invariant.
      Fresh synthesis has an empty table; nested actions no longer share a
      global wire-binding ref. Other IO caches and full MetaM execution remain
      outside this local result.
    - [ ] Connect expression-cache operations to the invariant and discharge
      source-value/width invariants across every successful handler.
  - [ ] Instantiate the completed GENERAL success theorem on crc16's successful
    compilation. Track coverage in `ShippingCompiler-Soundness.md`; generating
    a separate crc16 replay theorem does not discharge this item.
  - [ ] Connect Lean.Expr recognition/unfolding to source denotation and cover
    every successful handler, state initialization/reset and interface packing.
  - [ ] Prove mandatory cleanup/deduplication passes and compose the success
    theorem for flat, symbolic and hierarchical entry points.

  **Current bounded worklist (2026-09-24; F1 itself stays open):**
  - [x] Require a complete original/Opt/reparsed/text acceptance artifact.
  - [x] Prove the checked explicit combinational compiler correct and complete
    under its naming/width conditions.
  - [x] Extend to one arbitrary-width register and prove full-cycle preservation.
  - [x] Connect the shipping single-register `runCircuitH` / `circuit do` form
    to that compiler using a general loop/body theorem; test a real surface
    definition with enable and reset (`Tools/VerifiedCircuit.lean`).
  - [x] Define typed source statements and shipping-runner semantics; prove
    total extraction, exact supported-fragment characterization and general
    `BodyMatches`; reject delayed bindings and duplicate writes
    (`Tools/VerifiedSource.lean`). No per-program `BodyMatches` proof is needed.
  - [x] Connect a bounded actual Lean Expr fragment to that typed statement
    language (`Tools/ReflectSource.lean`). The reader is unverified; each accepted
    definition carries a kernel-checked equality to the requested source.
    Automatic AST, generic replay, printed text and refusal tests are pinned.
  - [ ] Prove reader coverage or extend it beyond the bounded single-register
    fragment. Current reading inlines expressions, with a 2048-visit refusal
    budget; it does not provide the shared route's scalability or a universal
    correctness/completeness theorem about arbitrary Lean reflection.
  - [ ] Expand the verified source fragment to register banks and memories;
    independent printer/SV semantics remains a separate downstream milestone.

  **First acceptance milestone (2026-09-24):** `Tools/CertifiedRoundtrip.lean`
  provides proof-carrying `Certificate`, `Certificate.sound`, and
  `accepted_sound`; `Tools/CertifyShared.lean` adds strict commands requiring
  original/Opt/RT replay and the parse equality before emitting an artifact.
  The general theorem connects the exact text through the shipping parser to
  the source observation, so a partial PROVEN chain is not acceptance.
  Tested on shareX4/shareX8, a fresh command invocation, and crc16, plus negative
  cases. This composes existing proofs; it does NOT prove reifier correctness,
  input-language coverage, termination, or independent SV semantics. F1 remains
  open. Contract, trust, and next milestone: `CertifiedAcceptance.md`.

  **Second bounded milestone (2026-09-24):** `Tools/VerifiedBlock.lean`
  implements a total checked compiler from typed combinational let-blocks to
  actual IR assignments. `compileChecked_sound` proves `RunCorrect` for every
  accepted block and every input trace/horizon, without a per-instance replay
  premise; `compileChecked_complete` establishes acceptance under the syntactic
  naming/width checks. Both use standard axioms only. It reuses CExpr's expression
  theorem, adds binding/IR-fold/cycle proofs, and connects via `Block.certify`.
  `VerifiedBlockTest` covers the shipping printer's output and its inlined,
  masked reparse using the generic compiler theorem (parser oracle remains).
  This is a new explicit combinational source API, not a verified shallow DSL
  reifier or, by itself, a stateful compiler. The state layer is covered by the
  next milestone below. Details and exact assumptions are in
  `CertifiedAcceptance.md`.

  **Third bounded milestone (2026-09-24):** `Tools/VerifiedState.lean`
  adds a total checked compiler for an explicit typed machine with one
  arbitrary-width register, shared let-bindings, one output, and sampled reset.
  `Machine.compileChecked_sound` supplies `RunCorrect` for every accepted source,
  input/reset trace and horizon by a register-state invariant over `runModule`.
  The source observes old state and resets/updates next state; initial target
  state and seed plumbing are explicit hypotheses. `VerifiedStateTest` covers
  init=7, enable/hold, mid-run reset, overflow, refusals and a shipping-printer
  roundtrip; general compiler and replay proofs use standard axioms only, the
  final text proof also uses the parse oracle. The parser's reset-kind change
  is benign only under the existing cycle-level IR semantics, not independent
  SV event semantics. `Machine.certify` and the general step-to-run congruence
  connect this to the acceptance API. F1 remains open for the shipping reifier;
  no register-bank, memory, or universal printer/optimizer proof is claimed.

  **Fourth bounded milestone (2026-09-24):** `Tools/VerifiedCircuit.lean`
  proves the shipping single-register `runCircuitH` loop agrees with `Machine`
  from a pointwise `BodyMatches` obligation quantified over every live signal
  and time. It then composes the checked compiler theorem into
  `compileChecked_signal_sound` and `certifyCircuit`. `VerifiedCircuitTest`
  pins an actual `circuit do` definition's expansion by `rfl`, proves its
  enable/reset body correspondence without SAT, and obtains Signal-to-IR and
  Signal-to-printed-text theorems for arbitrary input signals/horizons. The
  source-to-IR theorems have standard axioms only; text adds the same parser
  oracle as before. A future-register-reading body provably fails the contract.
  **Boundary:** body extraction/correspondence for this surface definition is
  still manual. The IR is produced by the new verified compiler, not by a
  newly verified shipping `Sparkle.Compiler.Elab` reifier. The next unchecked
  worklist item above is therefore still required before closing F1.

  **Fifth bounded milestone (2026-09-24):** `Tools/VerifiedSource.lean`
  defines typed let/next/return statements with independent Signal-combinator
  semantics. A real delayed binding also has semantics but is refused by the
  one-register extractor; duplicate next writes are refused too. `extract` is
  structurally total; `extract_iff_supported` characterizes its exact fragment.
  `extract_correct` proves pending writes survive later lexical bindings via
  `weaken_denote`. `Source.extract_bodyMatches` proves the formerly manual
  correspondence for every successful extraction; `Source.compile_sound`
  composes directly to Signal-to-IR correctness, without a machine or body
  proof supplied by the caller. All use standard axioms only. `VerifiedSourceTest`
  pins the existing surface accumulator to the interpreted source by `rfl`,
  certifies its actual text, and tests hold, capture avoidance, duplicate-write,
  additional-register and layout refusals. Only parsing adds the existing oracle.
  Raw Lean-to-Source conversion remains unverified: this is a verified typed-AST
  frontend, not completion of F1 for arbitrary Lean.
  **Sixth bounded milestone (2026-09-24):** `#reflect_verified f => model`
  reads a monomorphic single-register BitVec `runCircuitH` definition, with
  BitVec Signal inputs and an optional Bool reset in the outer next-state mux.
  It generates the typed source, input/reset functions and `model_source_eq`.
  Acceptance requires kernel equality to the requested definition, with standard
  axioms only. Two existing surface circuits pass without handwritten ASTs;
  one is connected through the general compiler to actual printed text.
  Multiple registers, parameter-dependent initialization, mismatched reset,
  nested register, name collision and fabricated candidate are negative tests.
  Failed commands restore declaration state. Text still adds the parser oracle;
  the test uses identity optimization and cycle-level reset semantics.
  **Boundary:** this validates each reader result; it does not prove the reader
  universally or certify the shipping elaborator, printer or external SV semantics.
- [ ] **F2. `native_decide` out of the per-instance obligations.**
  **Shared-route inventory (shareX4 `_sdeep_signal_run`, 57 auxiliaries,
  measured 2026-09-16 by grouping `#print axioms`):** G1 glue
  `coneEval_*` 24 (4 per slot — compile / concatNorm / inlineConeT /
  resolveSlicesT equations, keyed on `Std.HashMap` `dm`/`wtM`/`stopAtM`);
  `settled_w*` 12 and `step_*` 8 (per lemma: `hwfCheck` [HashMap stop
  set], `hwt_of_assoc` [list], `hinl` = `inlineConeT … = .ok` [HashMap],
  plus `hsub` refs-membership in the steps [`refsOf` of a cone DEFINED
  through `resolveSlicesT wtM` — HashMap]); `wire_w*` 4 (`hsub`);
  singletons `hag`, `hinj`, `nm_mem_stop`, `seed_bounded`'s width fact,
  `hb1_of` (`bodyWidthOk`), `signal_run` (`bodyEvalOk`) — all
  list-shaped; trace 1 (`CdoW.elab_general`'s name-table condition).
  Each replayed body (Opt/RT) repeats the per-body kinds.
  **Step 1 DONE (2026-09-16), one kind: the width-table fact.**  The
  identical proposition `∀ p ∈ wtL, weM p.1 = p.2` was proven by
  `native_decide` inside every settled/step lemma; now ONE theorem
  `{f}_sdeep_hwt` by KERNEL `decide` (literal association list, `weM`
  an if-chain on string literals), referenced from all sites of every
  replayed body.  Measured (equal conditions, `lake build`, 24G, 1.6 M
  heartbeats): shareX4 replay 57 → 51, Opt 75 → 69, svOpt 76 → 70,
  RT 75 → 69; shareX8 89 → 79, 119 → 109, 120 → 110, 119 → 109; wall
  53 s → 55 s for both circuits (noise); crc16CcittHW replay 152 → 134,
  Opt 206 → 188, RT 206 → 188, wall 752 s → 757 s (noise).  The kernel
  `decide` on crc16's 94-entry table took no measurable time.
  **Step 2 DONE (2026-09-16), the six list-shaped kinds.**  All moved to
  kernel `decide`: the name table's injectivity (`{f}_sdeep_hinj`, now
  proven ONCE before the trace and reused as `CdoW.elab_general`'s side
  condition AND by the replay), the slot-width fact (hoisted to
  `{f}_sdeep_hagK`, was a `native_decide` `have` inside both
  `seed_bounded` and `envSt_bounded`), `{f}_sdeep_hag`,
  `{f}_sdeep_nm_mem_stop`, `bodyWidthOk` (in `hb1_of`, per body) and
  `bodyEvalOk` (in `signal_run`, per body).  Measured, auxiliaries
  before → after: shareX4 replay 51 → 44, Opt 69 → 62, svOpt 70 → 63,
  RT 69 → 62; shareX8 79 → 72, 109 → 102, 110 → 103, 102; crc16 replay
  134 → 127, Opt 188 → 181, RT 188 → 181.  Wall: shareX4+8 55 → 57 s,
  crc16 757 → 765 s (noise).  Cumulative over steps 1+2: shareX4 57 →
  44 (−23 %), crc16 152 → 127 (−16 %).
  Per-kind KERNEL check time, measured on crc16's own constants by
  re-proving each statement with `decide` (one run each): width table
  3929 ms, `bodyWidthOk` (elaborator body) 3876 ms, `bodyWidthOk` (Opt
  body) 1093 ms, slot widths 1140 ms, `hag` 1249 ms, injectivity
  442 ms, `nm_mem_stop` 250 ms, `bodyEvalOk` 22 ms (23 ms on the RT
  body).  Total ≈ 13 s of the 765 s run — the kernel cost of this step
  is real but small against the proof search; the two ~4 s kinds are
  the ones that walk the 94-statement body or the 94-entry table.
  **Step 3 (2026-09-17), the STOP SET — the first HashMap-keyed table.**
  BOUNDARY MEASURED FIRST: on shareX4 the kernel cannot reduce
  `stopAtM.contains "_gen_w0" = true` at all (`decide` fails on the
  `Std.HashMap` lookup itself), so every checker keyed on the map is
  stuck regardless of how simple it is — and `inlineConeT` reads the
  stop set AND the definition map (`dm.get?`), so a list stop set alone
  cannot reach the cone equations.  Scope therefore stayed at the two
  checkers that consult the stop set ONLY through `contains`.
  `Tools/ConeFoldRT.lean` adds `stopOfL` (the map a list induces),
  list-keyed `hwfCheckL` / `stopAtFrozenCheckL`, and the bridges
  `hwfCheckL_to_hwfCheck` / `stopAtFrozenCheckL_to_check` (proven: with
  lookup agreement on the names the body mentions, the list check
  implies the map check, so the EXISTING `hwfCheck_sound` applies
  unchanged).  The generator now builds both stop sets through
  `stopOfL` and emits one `{f}_sdeep_hwfL_*` per stop set.
  **What changed is WHAT is trusted, not the count.**  Each site used
  to trust a `native_decide` WALK OVER EVERY STATEMENT; it now runs
  that walk in the KERNEL and trusts only a lookup-agreement fact over
  the body's assign targets.  Measured on crc16 (one run each):
  the kernel walk `hwfCheckL` 4524 ms, the remaining trusted agreement
  fact 7 ms, the old fully-trusted walk 1 ms.
  Counts move by one per theorem only (the shared stop set is now
  proven once instead of once per step lemma): shareX4 replay 44 → 43,
  Opt 62 → 61, svOpt 63 → 62, RT 61; shareX8 72 → 71, 102 → 101, 103 →
  102, 101; crc16 replay 127 → 126, Opt 181 → 180, RT 180.
  Cost, same harness for both (lake build, MemoryMax 24G, cgroup
  `memory.peak`), ONE run per side: crc16 765 s → 864 s (+99 s, +13 %),
  2.757 GB → 2.781 GB (+0.9 %).
  **Attribution not established.**  What IS measured is the per-kind
  kernel cost in isolation: `hwfCheckL` 4524 ms on crc16, and the step-2
  kinds ≈ 13 s in total.  Those do not account for 99 s, and with one
  run per side the difference is not separated from run-to-run
  variation.  Treat "+99 s" as the observed end-to-end delta, not as the
  kernel's cost; the breakdown needs repeated runs and a per-declaration
  profile before any cause is claimed.
  **Step 4 attempt (2026-09-17), the DEFINITION MAP — NEGATIVE RESULT,
  scope boundary found.**  The plan was the stop set's recipe one table
  over: `inlineConeT` reads the map only through `get?`, so a
  list-backed map plus a transfer theorem should kernelise the `hinl`
  cone equations.  The transfer theorem IS proven and shipped
  (`Tools/ConeFoldRT.lean`: `dmGetL`, `dmOfL`, `dmListOf`,
  `buildDefMap_dmOfL`, and `inlineConeT_dm_congr` — agreeing lookups
  give an identical walk, by the walk's own induction).  But the kernel
  still cannot discharge the cone equation.  MEASURED on shareX4,
  three propositions:
  * `dmGetL (dmListOf body) "_gen_w0" |>.isSome = true` — kernel OK;
  * `(dmOfL (dmListOf body)).get? "_gen_w0" |>.isSome = true` — FAILS;
  * `(stopOfL stopL).contains "_gen_w0" = true` — FAILS.
  So building the table FROM a list does not help: what blocks the
  kernel is the `Std.HashMap` LOOKUP, wherever the map came from.  (The
  shipped stop-set step is unaffected — it never asks the kernel to do a
  map lookup; it runs the checker on the list and trusts only the
  agreement fact.)
  Converting the cone equations therefore needs a LIST-KEYED
  `inlineConeT` — a variant function, with the seam theorems
  (`cone_agrees_with_fold`, `shared_cone_agrees_at_settled`,
  `g1_shared`, `inlineConeT_refs`) either restated over it or bridged by
  `inlineConeT_dm_congr`-style congruences.  That is a materially larger
  change than a table swap and is NOT attempted here; the transfer
  theorem above is the piece of it that is already done.  Same applies
  to `resolveSlicesT` (width table) for the `hsub` facts.
  **Step 5 (2026-09-17): the lookups are now PROVEN equal, and the real
  blocker turns out to be the WALK's recursion, not the tables.**
  Done and shipped in `Tools/ConeFoldRT.lean`, all kernel, no
  `native_decide`:
  * duplicate-key semantics reconciled FIRST — `buildDefMap` folds
    `insert` left to right so the LAST assign to a name wins, while
    `List.find?` returns the first (measured on `[x := 1, x := 2]`: map
    gives 2, `find?` gives 1).  `dmGetR` therefore scans from the RIGHT,
    which is also what makes the fold induction go through;
  * `dmOfL_get?_eq` / `buildDefMap_get?_eq`: the shipping map's `get?`
    IS `dmGetR` of the assign list — proven by induction on the fold from
    `Std.HashMap.get?_insert` and `getElem?_empty`, generalised over the
    accumulator.  `stopOfL_contains_elem` likewise for the stop set.
    **No `native_decide` anywhere in these.**
  * `inlineConeG` — the walk with its two table reads as FUNCTION
    arguments — plus `inlineConeT_eq_G` (the shipping walk IS this walk
    at the HashMap reads) and `inlineConeG_congr` (pointwise-equal
    lookups give the same run).  So there is ONE algorithm at two
    instantiations, not a second copy; `inlineConeT_of_list` composes
    them and moves a cone equation entirely to the list side.  This is
    the "rewrite the existing function by lemma" route, and it works.
  **But the kernel still cannot run it, for a different reason.**
  MEASURED: `decide` fails on `inlineConeG` even with a two-element
  literal table and a ref that stops immediately (no recursion, no
  generated constants) — and `#print axioms inlineConeG` shows
  `propext, Quot.sound`, the signature of WELL-FOUNDED recursion.  Its
  defining equations hold only propositionally, so the kernel cannot
  compute with it at all; a structurally-recursive walk on the same data
  reduces fine (checked).  The shipping `inlineConeT` has the same
  shape, which is the real reason these equations were always on
  `native_decide` — the `Std.HashMap` lookups were only the first of two
  blockers, and the tables are now cleared.
  What remains for the cone equations is therefore a STRUCTURALLY
  recursive formulation of the walk (recursing on fuel with the
  expression handled by an inner structural recursion, or on a
  size-indexed expression), related to `inlineConeG` by a proven
  equality.  `inlineConeT_of_list` is already the socket it would plug
  into.  Not attempted here — it is a third change, and the instruction
  was to measure one slot first.
  A `decide`-friendly result comparison is also in place (`isOkEq` /
  `eq_ok_of_isOkEq`): comparing `Except String Expr` directly gets stuck
  on the interpolated error messages, so the Boolean never compares
  error strings.
  **Step 6 DONE (2026-09-17): a cone equation proven with NO new trusted
  axiom, on both circuits.**  Two findings made it work.
  (a) `decide` failing is not unprovability: the tiny stopping-reference
  case closes by rewriting with the DEFINING EQUATION
  (`rw [inlineConeG.eq_def]; simp`), axioms standard — so the obstacle
  was always computation, never truth.
  (b) The well-founded compilation came from recursing on the PAIR
  (fuel, expression).  Splitting the two recursions fixes it: `stepE` /
  `stepEL` walk the expression STRUCTURALLY at one fuel level and hand a
  non-stop reference to a `rec` callback, and `inlineConeS` recurses
  structurally on `fuel`, passing a `rec` that expands the reference and
  drops one fuel — exactly where the original consumes it, so the
  fuel-exhausted error agrees too.  `#print axioms inlineConeS` →
  `propext` only, and the KERNEL computes with it.
  `stepE_eq_G` / `stepEL_eq_GL` / `inlineConeS_eq_G` prove the agreement
  with the generic walk (results, errors and fuel accounting), and
  `inlineConeT_of_listS` chains structural walk → generic walk →
  shipping `inlineConeT` over `buildDefMap`/`stopOfL`.
  **Measured, one slot, shipping statement, `#print axioms` = the
  standard three (no `native_decide`, no `sorryAx`):**

  | circuit | slot | kernel | `native_decide` | file peak |
  |---|---|---|---|---|
  | shareX4 | `_tmp_op_a_9` (w0) | 145 ms | 3 ms | 303 MB |
  | crc16CcittHW | `_gen_shifted_4` (w9) | 418 ms | 4 ms | 367 MB |

  So a kernel cone equation costs ~50-100x the compiled one but is
  absolute: on crc16 the per-slot `hinl` sites are ~0.4 s each.
  **Step 7 DONE (2026-09-18): applied to EVERY cone equation of the
  shared route, all three bodies.**  The generator emits one named
  theorem `{f}_sdeep_hinl_{slot}{tag}` per distinct (stop set, root)
  pair, proven by `inlineConeT_of_listS` + kernel `decide`, and
  references it from the settled-wire and step sites — so a proposition
  used twice is proven once.  No `native_decide` fallback: a failure is
  an error, like every other obligation here.
  Auxiliaries before → after, per theorem:

  | circuit | replay | Opt | svOpt | RT |
  |---|---|---|---|---|
  | shareX4 | 43 → 37 | 61 → 55 | 62 → 56 | 61 → 55 |
  | shareX8 | 71 → 61 | 101 → 91 | 102 → 92 | 101 → 91 |
  | crc16 | 126 → 108 | 180 → 162 | (skipped) | 180 → 162 |

  The drop is 1 per shared wire plus 1 per register/output root, per
  body — the `settled_*` auxiliaries disappear entirely and the `step_*`
  sites go from 2 to 1 (the survivor is the excluded `hsub`).
  Cost, same harness both sides (`lake build`, MemoryMax 24G, cgroup
  `memory.peak`), ONE run per side:

  | | before | after |
  |---|---|---|
  | shareX4+8 wall | 74 s | 79 s |
  | shareX4+8 peak | — | 1.04 GB |
  | crc16 wall | 864 s | 880 s |
  | crc16 peak | 2.781 GB | 2.797 GB |

  So crc16 costs +16 s MEASURED (+1.9 %) and +16 MB.  The earlier
  "roughly +40 s" was an ESTIMATE from per-slot timings and came out
  high; the per-slot figures (145/418 ms) do not compose linearly,
  since the generator proves each equation once and reuses it.
  Verification held throughout: shareX4/8 prove every clause with
  nothing skipped, crc16 keeps exactly its one documented SV skip.
  Still excluded from this change, as instructed: `hsub`
  (refs-membership over `resolveSlicesT`), the 24 G1 glue equations, and
  the default deep route (which keeps the width-table kind at 3 sites
  and its own cone equations on `native_decide`).
  The default deep route still has the width-table kind at 3 sites and
  its own copies (not moved).
  88 sites remain (52 in VerifyElab, 36 in DeepElab) riding
  `ofReduceBool`, i.e. trusting the Lean compiler's evaluation.  The
  first pass (2026-09-08) moved the list-shaped body checkers to kernel
  `decide` and cut one theorem's trusted axioms 108 → 76, so the method
  works; what remains is everything keyed on a `Std.HashMap` (USize
  hashing cannot kernel-reduce) plus the cone-inlining and
  concat-normalisation equations.  Fix: list-backed stop sets and width
  tables carrying their own lookup lemmas.  CompCert's checkers are
  kernel-reducible, so this is a real difference in kind, not degree.

  **F2 CLOSED for the shared route (2026-09-20, steps 1–11).**  Every
  per-instance obligation of `sparkle.deepShare` is kernel-checked.
  Final axiom dependency of each shipped theorem, by name:

  | theorem | beyond `propext` / `Classical.choice` / `Quot.sound` |
  |---|---|
  | `{f}_sdeep_trace` | `{f}_sdeep_trace._native.bv_decide.ax_*` |
  | `{f}_sdeep_signal_run` / `_runOpt` / `_runRT` | the same trace axioms, nothing else |
  | `{f}_sdeep_text_parses` | `{f}_sdeep_text_parses._native.native_decide.ax_1` (the parse oracle) |
  | `{f}_sdeep_signal_svOpt` (shareX* only) | the trace axioms + `{f}_sdeep_signal_svOpt._native.native_decide.ax_1` (the M4 `seqCheck`) |

  Counts: shareX4 2/2/3/2/1, shareX8 2/2/3/2/1, crc16 1/1/—/1/1.
  The 11 steps, in order: width table (1), the six list-shaped kinds
  (2), stop sets as lists (3–4), `inlineConeT` structurally (5–6),
  `resolveSlicesT` structurally (8), the G1 glue's four obligations (9),
  the `hwfCheck` lookup agreement (10), the mask equations and their two
  `widthOk` side conditions via `stripMaskK` (11).  The
  `Std.HashMap`-keyed blocker of the first pass was solved by giving
  every checker a structural, list-backed twin with an agreement
  theorem, not by trusting the map.
  **Deliberately still trusted on this route**, each a next-milestone
  item: the trace theorem's `bv_decide` (LRAT certificate evaluated by
  the compiled checker), the parse oracle (`parseAndLowerHierarchical`
  evaluated on the printed text — F3), and `seqCheck` in the SV
  theorem (a bare `decide` on it is stuck in 3 ms, "did not reduce"; it
  needs the same structural-twin treatment).  The DEFAULT deep route
  is unchanged and keeps its own `native_decide` sites.
- [ ] **F3. The printer/parser (M3).**  CompCert trusts its assembly
  PRINTER but not a parser of its own output.  Sparkle's roundtrip
  direction trusts the 26-`partial def` recursive-descent parser as an
  executable oracle on the specific text (`{f}_text_parses` under
  `native_decide`).  Two routes, both open: a verified printer with a
  proven inverse on the emitted sub-language, or — cheaper and probably
  the right call — make the FORWARD direction (`emit_sem`, which needs
  no parser at all) the primary guarantee and demote the roundtrip
  direction to validation.  The forward chain already has total corpus
  coverage, so this may be mostly a framing and documentation change.
- [ ] **F4. `partial def`s on the shipping path.**  77 remain (Parser 26,
  Lower 38, Optimize 10, Verilog 3).  A `partial def` has no unfolding
  equations, so nothing is provable about the shipping code as written;
  the verified-core/validated-shell split (total twins + `#guard`
  agreement) is the current answer.  CompCert has no such split: the
  verified code IS the shipping code.  Fix: swap the twins in as the
  shipping emitter/lowerer, which the design doc already scopes — the
  cone passes are already the twins on the `#verify_elab` path, and the
  file-level gap reduces to optimizer preservation.
- [ ] **F5. Optimizer preservation, proven rather than validated.**
  Today the optimizer is covered per instance (`#verify_emit`
  translation validation, which CompCert also uses for some passes) and
  every elaborator module classifies `.optRewritten`, none `.bad`.  A
  proven preservation theorem per pass (DCE, copy propagation, CSE,
  RegDedup) would remove the validation step.  RegDedup is the
  interesting one: its correctness argument is a coarsest-bisimulation
  fixpoint, currently executed but not proven (see section C).
- [ ] **F6. Closed hierarchical semantics.**  Duplicated from section D
  because it also blocks the CompCert claim: instances are open-module
  no-ops, so a multi-module design's composition is covered dynamically
  by hierarchical co-sim, not proven.  CompCert's theorem composes
  across compilation units.  Research-scale.
- [ ] **F7. Synthesis and silicon.**  Out of scope and worth stating so
  the claim is not overread: the chain ends at emitted SystemVerilog.
  Trusting the synthesis tool and the fabric is the same class of trust
  CompCert places in the assembler and the ISA — a stated boundary, not
  a defect.

Sequencing note: F2 and F3 are incremental and would meaningfully
tighten the claim.  F4 and F5 are large but bounded.  F1 and F6 are the
research items, and F1 is the one that actually decides whether the word
"CompCert-class" applies.

## G. Finding what nobody put on the list

The user asked (2026-09-10) whether a TODO list is the right instrument
for catching OMISSIONS in this work, noting that STAMP/STPA does not
transfer: Sparkle is a compiler, not an operating plant — there is no
control loop to lose, no hazard to trace, no dataflow to protect.  That
reading is right, and the honest answer is that a TODO list is a WEAK
instrument for omissions, because it only ever records what someone
already thought of.

But this project already has a working mechanism, and it is documented
in the design doc's bug inventory rather than in any process: **all 14
shipping bugs came from a proof REFUSING a shape, and from treating the
refusal as a bug report rather than as a proof limitation.**  The
inventory's own closing paragraph says it: "None of these is reachable
by testing the implementation against itself; each fell out of trying to
prove a statement and refusing to accept 'the proof is just weak here'."

Read the other way, that is a falsifiable claim about blind spots, and
the inventory names them concretely:

* bugs 2/4/7 — the co-sim gate exercises only the FIRST emission, never
  the second parse;
* bug 8 — co-sim compares two executables on the shapes the corpus
  happens to contain; the width-sensitive-consumer shapes were absent,
  and it took a formal semantics disagreeing with BOTH executables;
* bugs 9/12 — width bookkeeping wrong while every VALUE any executable
  ever produced was right;
* bugs 10/11/13 — miscompiles of shapes the corpus simply lacks;
* bug 14 — correct in the IR and in CSim, wrong only in the emitted
  TEXT, so invisible to every simulation-vs-IR check.

So the generalisable rule is: **a shape the fragment refuses is a
hypothesis about a bug, until measured otherwise.**  Bug 9 was found
exactly by pressing a width disagreement that "read like a proof
limitation"; bug 14 by pressing "why can't a zero-width net exist".
Conversely this session produced two refusals that measurement showed
were NOT bugs (the CRC16 cone size, the `Fin`-literal slot ceiling) —
which is the same rule working correctly in the negative direction.

- [x] **G1. The refusal ledger exists** — `docs/RefusalLedger.md`
  (2026-09-10).  Every checker refusal in the deep route, the cone
  level and the M4 forward fragment, each with a verdict of BUG / REAL /
  COST / UNEXAMINED and the evidence.  Pressing one UNEXAMINED row
  immediately paid: "negative const" measured as COST (the semantics
  encodes `-1` at width 8 to 255, exactly what the reifier could emit,
  so it is a one-line reifier fix, not a semantic gap; 0 occurrences in
  spiMasterHW/uartTxHW, so left refused rather than fixed blind).
  The UNEXAMINED rows are now the omission-hunting worklist:
  multi-port memories, read-address-reads-a-combinational-read,
  non-literal register inits, and symbolic-width slices (where
  `bitWidth` PANICS on `W+1` and the zero-width pass skips such
  modules — nobody has checked what that hides).
- [ ] **G1b. Keep the ledger honest.**  Today a refused shape
  lives wherever it was noticed: a `throwError` string in the
  generator, a "known boundary" paragraph, or nothing at all.  There is
  no place that lists what the checkers currently reject, so nobody can
  scan for "which refusals have never been investigated?".  Cheap
  version: have the fragment checkers' `whyNot` classifiers (they exist
  for SF4 — `sf4census`) emit a machine-readable tally over the corpus,
  and record for each class whether it was measured to be a real
  divergence, a proof limitation, or still unexamined.
- [ ] **G2. Differential-shape generation, not corpus sampling.**  The
  deepest blind spot in the inventory is "shapes the corpus lacks"
  (bugs 10/11/13, and 8 for the consumer positions).  Testing against a
  fixed corpus cannot find these by construction.  A generator that
  enumerates SHAPES — nested concat-LHS writes, bit-range writes above
  bit 31, mixed-width arithmetic under bitwise cones, zero-width
  elements — and runs formal semantics against iverilog would attack
  that class directly.  Note this is exactly how bugs 8-13 were found,
  but by hand each time.
- [ ] **G3. Three-way disagreement as a standing gate.**  Bug 8 needed
  formal-vs-SV-semantics-vs-iverilog-vs-CSim.  That comparison was run
  once, as an experiment, and is not a gate.  Making it standing would
  catch the "both executables agree and are both wrong" class.
- [ ] **G4. Cross-layer invariants nobody currently states.**  Bug 14's
  shape (right in the IR, wrong in the text) suggests a class of
  property that spans layers: every IR construct that survives to the
  emitted text must have a text-level counterpart with the same width
  and the same driver count.  The state-correspondence work of section C
  is one instance of this shape; there are probably others (port
  directions, clock/reset domains, driver uniqueness).

Not proposed: STAMP/STPA, FMEA, or a hazard analysis.  They assume a
system with a control structure and an accident to avoid.  The failure
mode here is a silent miscompile, and the instrument that has actually
caught those is an unwilling proof.
