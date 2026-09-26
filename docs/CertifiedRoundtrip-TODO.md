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
