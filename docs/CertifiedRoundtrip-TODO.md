# Certified-roundtrip — open work

Living checklist for the certified-compilation track (branch
`poc/roundtrip-proof`, PR #134).  Grouped by area; ordering within a
group is rough priority.  Update as items land.

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
  Next: (5) crc16 (32 slots, 26 wires) under the flag.
  Until then crc16 / arithmetic-size circuits remain capstone-only.

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

The sections above are coverage frontiers of THIS design.  This section
is the different question the user asked (2026-09-09): what separates
the current guarantee from a CompCert-style one?  Each entry names a
specific difference, not an aspiration, so it can be argued with.

Where Sparkle already matches or exceeds CompCert: a proven end-to-end
semantic chain (Signal ≡ emitted SystemVerilog), per-instance
kernel-checked validation, fourteen real compiler bugs found (several
silent miscompiles), and — with no CompCert analogue, since resource
duplication does not arise for a software compiler — the
state-correspondence property of section C.

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
  so a circuit outside the deep grammar has no theorem at all.  Closing
  this means a proven reifier: `∀ (c : circuit-do syntax), reify c`
  succeeds and its `Cdo` denotes the same Signal — i.e. the DSL's own
  elaboration proven correct, not replayed per instance.  Research-scale
  and the honest headline item.
- [ ] **F2. `native_decide` out of the per-instance obligations.**
  88 sites remain (52 in VerifyElab, 36 in DeepElab) riding
  `ofReduceBool`, i.e. trusting the Lean compiler's evaluation.  The
  first pass (2026-09-08) moved the list-shaped body checkers to kernel
  `decide` and cut one theorem's trusted axioms 108 → 76, so the method
  works; what remains is everything keyed on a `Std.HashMap` (USize
  hashing cannot kernel-reduce) plus the cone-inlining and
  concat-normalisation equations.  Fix: list-backed stop sets and width
  tables carrying their own lookup lemmas.  CompCert's checkers are
  kernel-reducible, so this is a real difference in kind, not degree.
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
