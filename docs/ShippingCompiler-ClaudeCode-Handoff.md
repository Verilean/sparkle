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
| `dropZeroWidthModule` proved body/weOf-preserving on the certified register shape (covers the `SPARKLE_NO_REGDEDUP=1` configuration). Remaining S4: the sequential duplicate merge (`mergeDuplicatesRaw` is unvalidated; needs register bisimulation — the test checks the default configuration numerically for 12 cycles, `mergeDuplicates_seq` reduces the shipped sequential merge to the raw one, and the raw merge is regression-checked to be the identity on all five certified register modules; the rename-equivalence checker `seqOptCheck` (mux-aware normalization, register pairing under renaming) is regression-gated to accept both the sequential merge AND the optimizer's output on every certified shape, and its soundness is PROVED in Tools/ShippingSeqOptSoundness.lean — `seqOptCheck_step_sound` (one-cycle: outputs agree, register updates pair with equal width-bounded values, accepted-side env generalized to agreement on the reference domain) and `seqOptCheck_run_sound` (k-cycle runModule trace equivalence under the canonical `seedIn`, register-state coupling as the induction invariant), with the packaged `seqOptCheck_transfer` composing checker + trace endpoints so the checker-accepted optimized module observes the source stream on ALL SIX certified shapes (`regAcc`/`regHold`/`accLoop`/`regChain`/`cdoAcc`/`cdo2X` `_run_optimized`); this closes both the merge and the sequential printed-SV trust gaps; the chain further reaches the emitted-SV semantics via Tools/ShippingSeqSVSoundness.lean — `seq_run_to_sv` composes a `seqNames` width congruence with the M4 capstone under a boundedness invariant, gated (`seqCheck` + width agreement) and instantiated as `*_sv_optimized` on all six shapes; the byte-level step is closed in the PARSE direction: `seq_run_to_parsed` + `*_parsed_optimized` prove the module parsed back from the actual printed Verilog trace-equal to the checked module on all six shapes (roundtrip census + clamped-seed congruence; gates parse the real bytes); remaining trusted base for sequential text = the parser/lowering byte→AST step — a render-direction proof needs compound sensitivities in the SV AST), single-register feedback is PROVED (`Signal.loop (fun s => Signal.register initLit cone)`: `loopRegister_step_of_env`, cone evaluated at the current state — the loop binder is one more unified input bound to the pre-allocated register wire; the packaged `register_run_of_env`/`registerEnable_run_of_env`/`loopRegister_run_of_env` state the full `runModule` trace of each shape as the source register stream, instantiated against the library `.val` streams in `regAcc_run`/`regHold_run`/`accLoop_run`); zero-width cleanup is proved preserved on all three register shapes; the two-stage shift chain `Signal.register i1 (Signal.register i2 cone)` is the first certified multi-register shape (gate chain disjunct; `synthesizeMixedCertified_register2_sound` decomposes both fuel levels; `register2_step_of_env`/`trace_of_cycles2`/`register2_run_of_env`; `regChain` test with 12-cycle two-register regression and `.val`-stream trace theorem); remaining: `circuit do`/`runCircuitH` reification onto the loop form (phase A done: the macro now destructures `RegList` via `Prod` projections instead of pattern-`let` matcher constants, and `map_fst_loop_register` anchors the reduced single-slot state to the certified feedback stream; phase B landed: `canonicalCircuitDo?`/`cdoConeToLoop`/`translateCircuitDoUncachedWith` + gate disjunct compile the single-slot shape to the IDENTICAL module as the explicit loop form, with `cdoAcc_val` identifying the source streams; the endpoint chain is now stated on the cdo quote form itself (`cdoE`/`canonicalCircuitDo?` pattern recognizer/`cdoConeToLoop_quote`/`CdoPreserves` monolith/`cdo_step_of_env`/`cdo_run_of_env`, instantiated as `cdoAcc_step`/`cdoAcc_run`; two-slot compiler phase landed: `canonicalCircuitDo2?`/`cdo2ConeToLoop`/`translateCircuitDo2UncachedWith`/gate handle cross-coupled same-width cones with ascription-coerced reads, 12-cycle regression pinned; the two-slot proof chain is CLOSED for the returned-slot-0 shape (cdo2E, shallow recognizer split, cdo2ConeToLoop_quote, Cdo2Preserves monolith with doubled selves + propositional distinctness guard + chained cone contracts, cdo2_step_of_env/trace_of_cycles2_inv/cdo2_run_of_env, cdo2X endpoints; with `loopPair_val`/`cdo2X_run_val` identifying the compiled trace with the actual circuit-do output stream; open: slot-1-return mirror, differing widths, more slots, Reg-operator reads), register chains deeper than two and general register networks (cross-coupled cones), reset muxes, sequential SV text (the `optimizeModule` pass-through is now covered by the proved `seqOptCheck` + runtime gate; the remaining sequential SV-text step is the printer itself, shared with the combinational print soundness route) | Open |
| Memories, hierarchy, final composition over the whole success domain | S5–S7, active — see ShippingCompiler-Milestones.md and the S5/S6/S7 entries of CertifiedRoundtrip-TODO.md for what is closed |

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

**Measured priorities (2026-10-01).** `scripts/shipping-coverage/run.sh`
measures which front end each declaration of the repository's corpus
takes and why the rest miss the gate; the result and the ranked reasons
are in ShippingCompiler-Coverage.md ("Measured corpus coverage"). 47 of
389 real declarations passed a certified gate then; 60 after the
normaliser, the applicative arm and the slice arm, 82 with the machine
route and 111 with its hardware `let`s (2026-10-02). Do NOT read the surface
table as "unfold definitions and 165 declarations pass": a prototype
normaliser was run and none passes (pass 3 of the script). Real IP is
`circuit do` + `let` + applicative lifting + slices + structure results
behind a field-projecting wrapper, and all of these are needed together.
The order is: front-end normalisation (pure delta-beta and projection of
a constructor in `synthesizeCombinationalCoreWith`, between the read of
the constant and `synthesizeFromConst`; byte-identical to the legacy
call-site unfolding on 17 tested shapes) → general N-slot `circuit do` →
hardware `let` → applicative/slices → structure results. The list below
is the older, shape-driven plan and is subordinate to the measurement.

**Adding a `Term` constructor — the sites.** Done five times now
(`setw`, `appCompare`/`appBool`, `bitsNum`, `slice`, `concat`, `concatLitHi`/`concatLitLo`, `zextMap`, `sliceF`, `appBool2`); the checklist is:
`Tools/ShippingUnifiedSource.lean` (constructor, `WF`, `wf_pos` for a
bits result, `eval`, `denote`, `denote_val`, an `…E` builder, `quote`,
`instFVars_quote`, `quote_congr`); `ShippingUnifiedMeaning.lean` (`view`
case or a fall-through helper like `appView?`, a `view_…` lemma,
`meaning_quote_leaves`); `ShippingUnifiedRecursion.lean` (step lemma,
`…_returns`/`_shape`/`_fresh`/`_contract`, the case of
`fuel_contract_leaves`); `ShippingUnifiedProtection.lean` (`…_protect`,
`…_order`, the cases of `fuel_protects` and `fuel_orders`);
`ShippingUnifiedExecutionSoundness.lean` and
`ShippingHierTermSoundness.lean` (the case of `…_quote_accepted`, and of
`…_root_accepted` for a bits result) with the matching arm in
`unifiedGate…`/`hierGate…` of Elab; `ShippingRegisterSoundness.lean`
(`cdoConeToLoop_quote`, `cdo2ConeToLoop_quote`). When the new node lowers
exactly like an existing one, CLONE that node's lemmas by text
substitution (the applicative lemmas are the comparison lemmas at hint
`"app_arg"`). A node that needs a new IR right-hand-side shape is a
different, vertical job. Slices were the first one, concatenation the
second. The back-half sites, in build order: `Sparkle/IR/OptCheck.lean`
(`simpleRhs` clause — this alone changes which modules `checkedOptimize`
retains unoptimised, so run the golden comparison);
`Tools/SVParser/ConcreteSyntax.lean` (a grammar production per printed
form); `Tools/ShippingPrintSoundness.lean` (`renderExpr` arm,
`PrintShape` constructor, `printShape_simple`, `width_lookup`,
`emitExpr_render_all`); `ShippingSyntaxSoundness`, `ShippingNameBinding`
(`ExprBound`), `ShippingTypedExprSoundness` (`TypedExpr` constructor and
its ~10 inductions), `ShippingTypedPostSoundness`, `ShippingPostSoundness`,
`ShippingMixedBindingSoundness`. The emitted-SV semantic layer
(`EmitSem`: `SF4`, `sf4Check`) already covers slices and general
concatenation. In the front half the slice lemmas are NOT clones of an
existing node: the result wire has its own type (`hwTypeFromWidth len`,
`.bit` at length 1) and `rfl` through `getAppArgs.back!` of the builder
times out — keep `sliceE_back`, `sliceE_noMux`/`_noTop`/`_noSetWidth`,
`sliceE_top` as separate lemmas under a raised heartbeat limit.

**Lessons of the concatenation arm.** (1) A six-argument application is
ALREADY matched by the generic operator arm of the gates and of `view`
(`.const m _` applied to three types, an instance and two operands), and
the proofs of the binary case state that arm's match by `rfl` with a
VARIABLE head (`binMethod op`). A new arm with a literal head in front
of it would make those `rfl`s stuck; the concatenation therefore sits in
the FALL-THROUGH of the generic arm (`| _, _, _ => match canonicalConcat?
e with …`), and the two binary `step` statements restate that
fall-through. (2) `canonicalSignalBitVecWidth` reads the last argument of
ANY listed instance, so `gateTopWidth?` of a concatenation is its LOW
operand's width; the root gates therefore have their own concatenation
disjunct in front. (3) A `Term` constructor with a non-variable index
(`.bits (m + n)`) works with `cases`/pattern matching over a variable
sort, but `⟨ha, hb⟩` against `Term.WF … (.concat a b)` fails ("not an
inductive type"): bind the hypothesis and `obtain` it. (4) Widths the
elaborator writes as expressions are a FRONT-END matter: fold them in
the entry constant, do not teach the gates arithmetic. (5) State the
lemmas of a multi-operand node over operand ACTIONS, not over `rec e
hint`: `Child rec … e hint v` is `ActionSpec (rec e hint false false) …
v` (`Child.action`), and a non-recursive operand — a literal put on its
own wire — is then just another action with its own spec, protection
and order lemma. The literal-operand concatenations cost three short
lemmas this way. (6) Read the ARGUMENT ORDER of a library instance from
the elaborated term, not from its statement: auto-bound implicits are
ordered by first occurrence (`instHAppendBitVecSignalHAddNat` takes the
literal's width, the domain, the Signal's width). (7) Before adding a constructor, check whether the
node LOWERS like an existing one: the literal-prefix map lowers exactly
like the zero-extending `setWidth`, so its arm calls the cast's lowering
and its proofs are the cast's, with one `BitVec` identity in between.
(8) Six-argument shapes go through `sixArgShape?` (gates, roots) and
`concatView?` (view): extend those two functions, do not touch the
generic arm or its restatements again. (9) A new right-hand-side shape
the optimizer's normal form rejects must be in `isCastExpr`
(`ShippingControlOptSoundness`), or `sized_of_flat` has no case for it;
the unary NOT is there for that reason, not because it is a cast.
(10) `renderExpr` must print EXACTLY what `emitExpr` prints for every
`wof`: the NOT has three texts (`(w'(x ^ w'dM))`, `~(x)` at width 0 and
at unknown width) and the generic `sizeCast`/`binary` rendering of the
same AST differs in parentheses, so the renderer has a dedicated
operand recogniser (`xorMask?`, like `shiftOperand?`) and the grammar a
dedicated production.

**The general `circuit do`: what exists and what is decided.** Source side:
`Tools/ShippingMachineSource.lean` (`circuit_state`, generic in the slot
list; `runCircuitH_eq` is `rfl`). IR side: `Tools/ShippingMachineTrace.lean`
(`trace_of_cyclesN`, `applyNexts_map_mem`/`_not_mem`). Neither mentions the
compiler. The user decided on 2026-10-02 that the certified route may emit
text that differs from the legacy compile when the function is the same
(byte identity is not attainable: the legacy packs the state with a
zero-width `Unit` wire and shares `let`s through a MetaM heuristic).

**The machine route (landed).** The connection needs NO new monadic
compiler proof: the TRANSITION of the machine — result and next values
packed into one bit vector, over the binders plus one binder per slot —
is an ordinary declaration of the unified combinational fragment, so the
existing harness and its theorem are used as a black box, and a pure IR
function turns the slot ports into registers.
* `Sparkle/Compiler/Elab.lean`: `machineShape?` (pure; `machRun?`,
  `machSlotKinds`, `machInits`, `inlZeta`, `machChain`, `machWrites`,
  `machConv`, `machPack`), `synthesizeMachineCertified`, the third branch
  of `synthesizeFromConst`, the third disjunct of `entryConst` (which now
  takes the structure projections of the environment).
* `Sparkle/IR/Machine.lean`: `Layout`, `closeMachine`.
* `Tools/ShippingMachineClose.lean` (`closeMachine_step`),
  `Tools/ShippingMachineEntry.lean` (`transition_facts`,
  `MachinePreserves`, `synthesizeMachineCertified_sound`, `machine_trace`,
  `MachineDefines`, `synthesizeCombinationalCore_machine_sound`,
  `field_lo`/`field_hi`/`field_all`, `#def_machine_body`).
* `Tests/Compiler/ShippingMachineEntryTest.lean`: five declarations
  simulated against the source; `mThree_execution`, `lin_execution`.
Lessons. (1) `synthesizeMixedCertified_term_sound` hid its binder ids
behind an existential; composing with facts of the SAME run (the body
ends in `assign out = w`, the input ports are the binder walk's) needed
the statement AT the ids of a run (`…_term_sound_at`). When a theorem's
existential witnesses will be needed again, state the "at" form first.
(2) The harness theorem needs an admissible environment before it says
anything; facts that do not depend on values (the ports) are obtained at
the all-zero environment (`admissible_zero`) and transported
(`inputPorts_congr`). (3) Put a new dispatch test where the entry
constant is computed, not before the memo lookup: the first version
re-ran the unfolding on every sub-module reference and broke a
heartbeat-tight design that the SUITE does not contain — only the corpus
measurement found it. (4) A reflected `Lean.Expr` constant inside a
structure literal crashes the code generator: mark such definitions
`noncomputable`. (5) The per-declaration source bridge is short once the
packed value is stated by `rfl` (`mThree_packed`, `lin_packed`) and the
fields are read with `field_lo`/`field_hi`/`field_all`; slot values enter
the valuation as `BitVec.ofNat n x.toNat`, which avoids casts.
**Hardware `let`s (landed).** Do NOT unfold `let`s: `circuit do` copies
its `let` chain into every write and into the result and `let`s mention
`let`s, so the tree is exponential (86 declarations ran out of budget).
`machConv`/`machChain` read the body with an environment of what each
bound variable stands for (`MachVal`) and write the transition over
closed PLACEHOLDERS (`machIn`/`machSlot`/`machLet`, free variables with
reserved names), which `machClose` turns into bound variables once the
number of `let`s is known; a hardware `let` whose value was already met
is the same `let` (`machBindLet`). The `let` is a binder AND a field of
the packed value, so ONE run of the unchanged harness compiles
everything with sharing; `closeLets` (pure IR) then drives each `let`
port from the operand wire of its field. Its proof uses no ordering
argument: the closed body is acyclic by a runtime check
(`assignmentOrderCheck`), the transition's result — evaluated with the
`let` ports PRESET to the right values — satisfies the closed body's
equations, and an acyclic body has one solution
(`ShippingSettledSoundness.equations_eval`). The presets are right
because the caller supplies a valuation with `LetsHold` — per
declaration, the source's own `let` values (`lin_lets`, one `simp`).
Everything the IR pass cannot derive is a runtime check inside
`closeLets` (operand widths, names, order); when a check fails the run
falls back to the legacy route, and the endpoint carries the boundary
`MachineCloses`. Lessons: (6) a "let as extra input + field" encoding
turns a sharing problem into IR plumbing and reuses the harness theorem
unchanged; routing the value back through the packed wire would be a
combinational loop at wire granularity, the operand wire is not. (7)
State a per-cycle fact that needs a fixpoint as a hypothesis about a
valuation the CALLER supplies (`LetsHold`) rather than constructing the
fixpoint generically: the source already has the values. (8) Binder
types in `∀ i pa f, …` statements over `Σ`-lists must be annotated, and
`(eval … f.2 : BitVec f.1).toNat` needs the ascription.
**Structure results (landed).** `Layout.outs`, `closeMachine` with one
part-select per port, `machOuts?`/`machResults?`, `StructEnv` (the
environment's structure facts, threaded where the projections were),
`outNameOk`. The endpoints quantify over `o ∈ shape.layout.outs`; a test
picks a port by giving the `OutField` literally.
**The reference machine (landed).** `Tools/ShippingMachineRef.lean`:
`machine_ref_trace` removes every valuation hypothesis from
`machine_trace` — the emitted module implements `RefMachine`, a machine
defined by `eval` on the terms (decidable side conditions only). The
remaining per-declaration obligation is "source = reference machine".
Plan for doing it once: typed valuations (`dite` casts that reduce by K)
built from the `circuit do` state tuple, typed `let` terms, a hypothesis
`H2 : ∀ S t, valsAt … (body (mkRegList S …) (mkHolds … S)).snd t =
evalTerms nexts (typedVal … (S.val t))` that a declaration proves by
`rfl`, an agreement lemma typed-valuation ↔ store valuation
(`eval_congr` on read positions at declared widths), and the generic
field lemma for the packed core. `scoped` is a keyword — not a name.
DONE the same day: `Tools/ShippingMachineDenote.lean` (`denote_state`,
`denote_out`, `TermFacts`, `SlotsFit`, `typedVal`), instantiated as
`linHW_execution_generic`: per declaration only data, `rfl` and decided
facts remain (the state tuple's `Inhabited` instance at `tys ss` must be
supplied — instance search does not see through `List.map`). The next
step is a COMMAND that generates these per declaration: unquote
`shape.body` into typed terms (the inverse of `quote`, constructor by
constructor), emit the definitions and the theorem, and run it over the
machine-route declarations.
**The generated endpoint (landed).** `#machine_endpoint f`
(`Tools/ShippingMachineCommand.lean`) over `machine_trace_of_data`
(`Tools/ShippingMachineAuto.lean`): `MachineData` + `MachineData.ok`
(one Bool for every side condition) + five equations, each `Eq.refl`
checked by the kernel, give `f.machine_sound : MachineTrace …`. 55 of
the 55 machine-route declarations of the corpus have it
(`scripts/shipping-coverage/endpoints.sh WORK`, after a `PASSES=1` run).
How it is built, and what to keep in mind when extending it:
* The reader `unq` is unverified on purpose: add a constructor to `Term`
  (+ `quote`, `eval`, `WF`, `reads`), a case to `unq`, `termE` and
  `wfDec`, and nothing per declaration.
* Declarations are added with `addDecl` under `Elab.async := false`: the
  default checks asynchronously, so a FAILING `Eq.refl` would not throw
  and would stay in the environment as an axiom-like constant. The
  environment is restored on failure, and `collectAxioms` is audited.
* `Expr ==` is alpha-equivalence; a reflected `Lean.Expr` in a theorem
  is compared with its binder names. Use `Expr.equal` for a pre-check.
* KERNEL REDUCTION ORDER. Never leave an `ite`/`dite` on the reduction
  path of a definition that the kernel must compare with user terms:
  `TVal.set` read positions with `if q = p`, a mux is also an `ite`, the
  kernel tried the arguments, failed, and unfolded both — evaluating the
  mux condition `ule p (x + p)` in unary for a 381-bit `p`. The reads are
  `match Nat.decEq q p with` now (matchers are abbreviations: unfolded
  first, so a read resolves before anything else is touched). A check
  that does not end shows nothing (`run_cmd` output appears when the
  command ends): `SPARKLE_MACHINE_PROGRESS=<file>` makes `generate` log
  each check; bisect with a small `circuit do` at the REAL widths.
* The source check is two facts: `machine_result` (result vs terms on an
  arbitrary state signal) and `machine_source` (declaration = result of
  the body on the state loop). One `rfl` for both mixed value-level
  evaluation with the unfolding of `Signal.loop`.
* `machCanonAp` (in `machineShape?`): canonical binder names for a lift
  written directly as `Signal.ap (Signal.map f a) b`.
**Normal forms (landed).** `machNorm senv` rewrites the body of the
`circuit do` before `machChain` reads it; `StructEnv.natOf` (`kernelNat
env`: `Lean.Kernel.whnf` on a closed `Nat` term) gives the value of
computed constants, reset values (`machInit?`), slice starts. Rules, each
one node (`machNormNode`): `Signal.lit` → `Signal.pure`; `Signal.pure c`
with `c` not a literal → the literal; `m α β γ inst a b` at a mixed
Signal/`BitVec` instance (`canonicalSignalBinKinds`) → the Signal×Signal
instance with `Signal.pure` of the literal; `Signal.ap (Signal.map (fun x
y => x op y) a) b` → `a op b`; `Signal.map`/`<$>` with `fun x => x op c` →
`a op pure c`; `~~~a` → `pure allOnes ^^^ a`. To add a form: one more case
there (and nothing else, if its target is an existing `Term` form); the
generated endpoint of a declaration using it is the proof. 175 of 389 real
declarations now pass a gate, 112 on the machine route, all 112 with
`f.machine_sound`.
**To the emitted Verilog (landed).** `refineCheck` (`Sparkle/IR/RefineCheck.lean`,
pure; since the compile-time gate below the compiler calls it) + `Tools/ShippingRefineSoundness.lean`
(`refineCheck_transfer`) + `Tools/ShippingMachineShipping.lean`
(`machine_ships`, `machine_ships_full`, `MachineShips`). `generate` adds
`f.machine_ships` (no kernel work: an application of `machine_ships_full`
to `f.machine_sound`). `scripts/shipping-coverage/pipeline.sh WORK`
evaluates the gates on the corpus: 107 of 113 (the 6 `EmitSem.seqCheck`
rejections). To extend the check:
a new normal-form node needs a constructor of `RShape` and a case in
`rShape_eval`, `rShape_bound`, `rShape_congr`, `rSlice_sound`,
`rNormE_sound`; a new optimizer simplification needs a smart constructor
like `rBin`/`rMux`/`rSlice` with its soundness lemma. The prototype-first
method paid off: an unverified normaliser was run over the corpus as a
probe until it accepted the optimizer's output everywhere, and only then
was that rule set proved. Open here: the six modules `EmitSem.seqCheck`
rejects, the parsed-back text for multi-register modules, normal forms for
legacy modules (forward references need a fixpoint `rNormBody`).
DONE the same day (user decision): `mergeChecked` and the sequential
branch of `checkedOptimize` gate both steps at compile time with a
fallback, on the modules whose own normal forms exist (`refineCheck m m`;
gating every sequential module changed 70 legacy modules — see the TODO);
`machine_ships_checked` is what `f.machine_ships` is now;
`checkedOptimize` moved to `Sparkle/IR/RefineCheck.lean` (namespace
`Sparkle.IR.OptCheck` kept; proofs that `unfold checkedOptimize` without
`simpleBody` have one more branch). Corpus: against the previous compiler
every emitted RTL text is identical (198 of 199 output files
byte-identical; the one difference is the new `run_cmd` log of
`ShippingMachineCommandTest`), status identical; 60-cycle simulation
119/119 OK; 113/113 machine-route declarations have the kernel-checked
endpoint; the two CRC modules (0.5–0.75M-node normal forms) pass the gates
too now that the probe runs the check (it shares the DAG), 6 remain on
`EmitSem.seqCheck`.
THE MEASUREMENT CYCLE after any change to `Elab.lean` (about 50 minutes,
never next to a `lake build`): `PASSES=1 scripts/shipping-coverage/run.sh
NEW`; `compare_outputs.py OLD/out NEW/out` (every `DIFFERENT` file must be
explained module by module — so far always "newly on the machine route");
`diff <(sort OLD/status.txt) <(sort NEW/status.txt)`;
`scripts/shipping-coverage/endpoints.sh NEW` (the generated theorems);
`scripts/shipping-coverage/simulate.sh NEW` (every machine module against
its source, 60 cycles, every port).
Next on this route: (a) DONE — see above. (b) DONE for constants, lifts,
mixed operands, `~~~` — see "Normal forms". Formerly: Normalise in
`machConv`, on this route only: constants computed in Lean
(`BitVec.ofInt`, `2 ^ k`, …) to literals, BitVec operators lifted through
`<$>`/`<*>` or `map` with a literal to the Signal operators, reducible
user constants unfolded. (c) Sub-module calls inside the body. (d) The
post-pipeline composition. The classifier that ranks these is
`scratchpad/mach3_tail.lean.in` (its `minimalBad` reports instance
arguments as the refused node for binary operators — read the parent).

**Measuring before building.** `inlineDefs` did not descend into `let`
until the map-idiom unit, so every "residual head" statistic taken before
it over-counted user definitions and applicative forms inside
`circuit do` bodies. The classifiers (`cdo_tail`, `lift_tail` in the
session scratchpad; the committed `probe_tail`/`normalize_tail` predate
the real normaliser) must run on `userInliner env value`. Run several
probes in ONE elaboration per file and in parallel — each file is
re-elaborated with all its syntheses, which is the whole cost.

**Front-end rewrites and sharing.** A normalisation is byte-safe only if
the legacy route keys its cache on the same expression. Canonicalising
numeric literals at the front end made the certified route share index
and value constants of the AES S-box that the legacy route keeps apart
(767 vs 1022 statements) — it was removed, and the literal form became a
`Term` constructor instead. Run `compare_outputs.py` against the previous
compiler after every Elab change.

**Dispatch as data.** `translateFallback` is `match fallbackKind e with …`;
`fallbackKind` is the recogniser chain as a function to `FallbackKind`.
A shape that reaches the end of the chain is characterised by ONE fact,
`fallbackKind e = .other` (the instance step lemmas and the instance
`…Preserves` predicates take it as `hkind`, discharged by `rfl` per
declaration) instead of one `= none` fact per recogniser. Append new arms
JUST BEFORE `.other`: shapes that leave the chain earlier are untouched
and `hkind` re-checks by `rfl`.

**Real IP reached.** `nodeFilter_execution` and `oddParity_execution`
(Tests/Compiler/ShippingInlineSoundnessTest.lean) are the first theorems
about modules of the IP library. The recipe for the next combinational
IP module: a public wrapper `(ipHW …).field`, `#def_entry_value`, a
`Term`, `*_library … := rfl`, `*_peel … := rfl`,
`execution_source_of_entry`. What stops the rest is in the blocker sets,
not in the recipe.

**Entry constant (landed).** `synthesizeCombinationalCoreWith` now calls
`synthesizeFromConst` on `entryConst … ci (instancePredicate env)
(userInliner env)`. Consequences for proofs: (1)
`synthesizeCombinationalCore_reads` gives the run on the ENTRY constant;
a family lemma for a gate-accepted declaration needs
`entry_kept shape run` to get back the run on `ci`; (2) new endpoints
should take `EntryDefines` (Tools/ShippingInlineSoundness.lean), which
covers both as-read and unfolded declarations — write them once over
`synthesizeCombinationalCore_reads` + `entry … get henv` + `rw [hd] at
run`, as `execution_source_of_entry` does; (3) `#def_entry_value v of f`
names the entry constant's value for a `rfl` peel. Do not compare such a
value literal with `==` inside a `run_cmd` (it trips a code-generator
bug, "unknown join point"); compare the reflection instead
(`reflExpr`), as the inline test does. Re-run the measurement after every gate extension, and
remember that `Tests.AllTests` does not contain every regression file —
the corpus run is what found the Issue #107 regression.

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
- Latest full verification: `lake build Tests.AllTests`, **686 jobs green** (2026-10-03, merge and optimizer checked at compile time).
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
