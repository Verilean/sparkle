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
- [ ] Memories / sub-instances (`.inst`) in the deep grammar.
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
  Remaining: `memoryComboRead` (combinational read — synthesizable and
  used by Regfile/KVCache; needs read slots in the deep context and a
  "seeded read is a no-op" seam lemma for the replay), `memoryWithInit`
  (no synth support today), multi-port memories, sub-instances
  (`.inst`).
- [ ] Bridge v1 limits: register inputs / memory ports that aren't
  `.ref` wires (the replay is skipped with a message; the capstone is
  still emitted).

## D. Trust base

- [ ] **`native_decide` → `decide` hardening** where feasible.  Many
  checker/equation discharges ride `ofReduceBool`.  HashMap paths
  can't kernel-reduce (USize hashing); list-shaped stop sets / width
  tables could.
- [ ] Closed hierarchical semantics (`.inst` as state trees /
  flattening proof).  Research boundary; hier co-sim covers it
  dynamically today.

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
