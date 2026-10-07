# The shared route's guarantee chain — link by link

What `set_option sparkle.deepShare true in #verify_elab_deep f` proves
about a `circuit do` definition `f`, from the `Signal` value to the
Verilog text that `#synthesizeVerilog` prints; what each link trusts;
what is not connected.  Read from the code and theorems of
`Tools/DeepElab.lean` (shared route), `Tools/ConeFoldMem.lean`,
`Tools/ConeFoldOpt.lean`, `Tools/ConeFoldRT.lean`,
`Tools/SVParser/EmitSem.lean` on 2026-09-14.  Names below are the
generated declarations, `{f}_sdeep_*`.

Trust vocabulary.  **kernel**: checked by Lean's kernel with the
standard axioms (`propext`, `Classical.choice`, `Quot.sound`).
**native_decide**: a closed Boolean evaluated by the compiled program
(`Lean.ofReduceBool`, one auxiliary axiom per site) — trusts the Lean
compiler's evaluation of the named checker on the named constant.
**bv_decide**: the SAT route; its LRAT certificate is checked by
kernel-reducible code, and each call leaves one `bv_decide.ax_*`
auxiliary.  The generator audits every theorem below: it must exist,
carry no `sorryAx`, and depend on nothing beyond the standard axioms
and these auxiliaries (`_native.native_decide.ax_N` /
`_native.bv_decide.ax_N`, recognised by name STRUCTURE); anything else
is an error.

## 1. Signal ≡ CdoW — `{f}_sdeep_trace`

* Statement: for every cycle `t`, `(f inputs).val t` equals the `CdoW`
  reification's denotation at `t` (`CdoW.elab_general`, root namespace
  in `Tools/DeepElab.lean`, a closed general theorem; the per-circuit
  part is the reification `{f}_sdeep` and the Signal-side bridge).
* Proof: readers `_sdeep_rd*`, wire equations `_rw*_eq` (`rfl`), the
  linear `signal_lets` recipe, `bv_decide` per step.
* Trust: kernel + `bv_decide` auxiliaries (2 on shareX4).  The
  name-table side condition handed to `CdoW.elab_general` is kernel
  `decide` since 2026-09-16, so the trace theorem carries no
  `native_decide` auxiliary.
* Reification is a meta-program (F1 in the TODO): a circuit outside the
  deep grammar gets NO theorem and a named refusal.

## 2. CdoW ≡ the elaborator's IR body — `{f}_sdeep_signal_run`

* Statement: `runModule weM body seed K st0 = some envs`, and for every
  `t < K`, `(f inputs).val t` is the output port's value in `envs[t]`.
  `body := {f}_sdeep_body = deepOrderBody m.body`, a stable topological
  PERMUTATION of the module the elaborator produced (`woCheck` proves
  the well-ordering the fold semantics needs; the printed module is
  bridged in its own raw order in §3).
* Proof: G1 glue `g1_shared` (compiled CdoW cones = `concatNorm` of the
  inlined IR cones), `shared_cone_agrees_at_settled` per slot,
  `evalAssigns_bounded`, `regstep` / `state_trace` / `signal_fold`.
* Trust: kernel for all structural lemmas; kernel `decide` for
  `woCheck`, `memFreeCheck`, `noSelfReadCheck`; `native_decide` for the
  `Std.HashMap`-keyed checkers (`hwfCheck`, `hwt_of_assoc`), the
  cone-inlining equations (`inlineConeT … = .ok cone`) and the G1
  equations (44 auxiliaries on shareX4, 127 on crc16 as of 2026-09-16).
  KERNEL `decide`, not `native_decide`, for every list-shaped kind:
  `woCheck`, `memFreeCheck`, `noSelfReadCheck`, the width table
  (`{f}_sdeep_hwt`), the name table's injectivity (`{f}_sdeep_hinj`,
  also `CdoW.elab_general`'s side condition in §1), the slot widths
  (`{f}_sdeep_hagK`), `{f}_sdeep_hag`, `{f}_sdeep_nm_mem_stop`,
  `bodyWidthOk` and `bodyEvalOk`.  Since 2026-09-17 the `hwfCheck`
  statement walk is kernel-checked too, on a LIST stop set
  (`{f}_sdeep_hwfL_*`, via `hwfCheckL_to_hwfCheck`); what stays trusted
  there is only a lookup-agreement fact between the list and the
  `Std.HashMap` the cone functions take.  The kernel cannot reduce a
  `Std.HashMap` lookup at all — and, measured 2026-09-17, not even when
  the map is BUILT from a literal list, so the obstacle is the lookup
  itself, not the table's provenance.  Kernelising the cone equations
  (`hinl`) therefore needs the lookups moved off the map — which is now
  DONE and proven (`buildDefMap_get?_eq`, `stopOfL_contains_elem`, both
  from the HashMap's own lemmas, no `native_decide`; `inlineConeG` is
  the walk with its reads as arguments, `inlineConeT_of_list` composes
  them).  The second blocker — the walk was compiled by WELL-FOUNDED recursion,
  so the kernel could not compute with it — is also cleared: splitting
  the fuel recursion from the expression recursion (`stepE` +
  `inlineConeS`, agreement proven including fuel accounting) gives a
  structural walk the kernel runs.  Since 2026-09-18 EVERY cone equation of this
  route is discharged that way, on all three bodies: the generator emits
  one `{f}_sdeep_hinl_*` theorem per distinct (stop set, root) pair and
  reuses it, with no `native_decide` fallback.  Since 2026-09-19 the
  refs-membership facts too: `resolveSlicesT` has a structural twin
  (`resolveSlicesS`, proven equal via `resolveSlicesT_list`), and each
  slot's `{f}_sdeep_hsub_*` is one kernel theorem shared by the three
  replays (crc16: 108 → 90 replay auxiliaries, 162 → 144 per bridge).
  Since 2026-09-20 the G1 glue too: its four per-slot facts are
  `rfl`, the reused cone equation, and two kernel `decide`s through the
  structural resolver (crc16 replay: 90 → 18 auxiliaries).  Since
  2026-09-20 (step 10) the `hwfCheck` lookup-agreement facts are
  instances of `stopOfL_contains_elem` too, so §2's replay theorem
  carries NO `native_decide` auxiliary any more — only the trace's
  `bv_decide` ones (crc16 replay: 1).  Since 2026-09-20 (step 11) the
  mask equations and the two `widthOk` side conditions per slot are
  kernel `decide`s too, through `stripMaskK` (§3), so the Opt and RT
  replay theorems carry exactly the trace's `bv_decide` auxiliaries
  (crc16: 55 → 1 each).  What is still `native_decide` on this route,
  by name: the parse oracle `{f}_sdeep_text_parses._native.
  native_decide.ax_1` (§4b) and, in the SV-semantics theorem only, the
  M4 fragment check `seqCheck` (`{f}_sdeep_signal_svOpt._native.
  native_decide.ax_1`, §4a).
  See TODO F2 step 7.  TODO F2 carries the inventory by kind,
  the per-kind kernel times, and the remaining HashMap-keyed block.

## 3. IR body ≡ the OPTIMIZED body — `{f}_sdeep_signal_runOpt`

The module that is printed is `optimizeModule m`, not `m`.  The chain
is CARRIED ACROSS the optimizer per instance (translation validation),
not by proving the optimizer:

* `{f}_sdeep_bodyOpt := (optimizeModule m).body` (raw order).  Per slot
  (register input, shared wire, output) the optimized body's cone,
  stopping at the same slots, is re-inlined and slice-resolved; the
  theorem `{f}_sdeep_maskEqOpt_*` states
  `rtNorm weM (stripMaskK wofM coneOpt) = rtNorm weM coneOrig` — a
  kernel `decide` after rewriting both cones to their structural
  resolutions (`{f}_sdeep_hresL_*`); `stripMaskK` is `stripMask` with
  the structural guard `widthOk` in place of the well-founded
  `sfragCheck`, which the kernel cannot reduce (measured 2026-09-20).
  `rtBridgeK_eval` (Tools/ConeFoldRT.lean, kernel, via
  `stripMaskK_eval` — bound from `evalExpr_bounded` — and `rtNorm_eval`
  on the bounded settled environment, with the two `widthOk` side
  conditions `{f}_sdeep_wokX_*` / `_wokO_*` also kernel `decide`s)
  then makes the two cones evaluate alike, and §2's chain
  is replayed verbatim over the optimized body
  (`_hb1_ofOpt`, `_settledOpt_*`, `_wireOpt_*`, `_stepOpt_*`,
  `_regstepOpt`, `_state_traceOpt`, `_signal_foldOpt`,
  `_signal_runModuleOpt`, `_signal_runOpt`).
* Preconditions checked in the generator BEFORE emitting (a body that
  fails one is reported as `Opt bridge SKIPPED — <reason>` and is absent
  from the PROVEN line): same registers by name with equal initial
  values, register inputs are wire references, reset wires are not
  slots, `woCheck` / `memFreeCheck` / `noSelfReadCheck` / `bodyEvalOk` /
  `bodyWidthOk` / `hwfCheck` (at every stop set), every slot wire still
  assigned, every cone normalises to the original's, `widthOk` on both
  normalised cones.
* Measured: every shared wire of shareX4/shareX8 and crc16CcittHW
  survives the optimizer under its own name; the optimizer's only
  change to the shared-granularity cones is the identity-mask
  re-insertion `stripMask` removes.
* Trust: kernel + `native_decide` (the mask equations and the §2
  checkers on the optimized body).

## 4. Optimized body ≡ printed Verilog — two links

### 4a. Forward: `{f}_sdeep_signal_svOpt` (proven emitter semantics)

* Statement: the M4 emitter applied to `bodyOpt` yields a
  combinational program, register block and memory program whose
  Verilog-subset trace `runModuleSV` (Tools/SVParser/SVSemantics.lean,
  context-width evaluation) equals the Signal value at every cycle.
* Proof: `certified_forward_trace_module` (Tools/SVParser/EmitSem.lean,
  kernel; `emit_sem` on the `SF4` fragment, context immunity, bias
  encoding) with `seqCheck wofM (weOf wofM) bodyOpt` by `native_decide`
  and `{f}_sdeep_envSt_bounded` as the seeding discipline.
* What it does NOT cover: the theorem is about the certified TWIN
  emitter (`emitAssigns` / `emitRegs` / `emitMemWrites` producing an SV
  AST), not the shipping printer `toVerilog`.  The twin ↔ shipping
  agreement is `#guard`-tied and corpus-validated (design doc "verified
  core / validated shell", TODO F4), not proven per instance.  4b
  closes that gap from the other side.
* Fragment limit: `seqCheck` refuses statements outside `SF4`.  When it
  does, the generator names the statement (`Opt SV-semantics theorem
  SKIPPED — statement `x` … outside the M4 sequential fragment`) and the
  PROVEN line omits `_signal_svOpt`.  crc16CcittHW hits this: its
  `(byte << 8)` is a 16-bit shift whose value does not fit
  (`widthOf x + k ≤ max (widthOf x) kw` fails: 16 + 8 > 16), the
  `bitwiseShl` rule's fit condition — the "shl width rule" row of the
  refusal ledger (REAL, bookkeeping: values agree, the width invariant
  does not).  The relaxation that would admit it — a shift under an
  `and` with the node-width mask is context-immune — is a new `SF4`
  rule and `emit_sem` case, out of scope here and tracked in the TODO.

### 4b. Roundtrip: `{f}_sdeep_text_parses` + `{f}_sdeep_signal_runRT`

* `{f}_sdeep_text := toVerilog (optimizeModule m)` — the string that
  is written to the `.sv` file, as a constant.
* `{f}_sdeep_text_parses`: the shipping parser+lowerer
  (`Tools.SVParser.Lower.parseAndLowerHierarchical`) maps that string
  to `{f}_sdeep_bodyRT` (`native_decide`: the parser is an EVALUATED
  ORACLE on this text; nothing is proven about the parser — TODO F3).
* `{f}_sdeep_signal_runRT`: §3's replay over `bodyRT`, with
  `{f}_sdeep_maskEqRT_*` — here `rtNorm` does real work: the printer
  writes a 1-bit `not x` as `1'(x ^ 1'd1)` and the lowerer reads the
  cast back as `slice (concat [const 0 1, xor [x, const 1 1]]) 0 0`;
  `rtNorm` maps both to `not [x]` (`rtNorm_eval`, kernel, needs the
  one-bit bound from `evalExpr_bounded`).  Measured on crc16: without it
  8 of 16 wire cones differ; with it all cones agree.
* Also measured: the lowerer copy-propagates alias assigns, so a wire
  whose right-hand side is a bare name (or the elaborator's full-width
  slice of a slot, printed as a bare name) does not exist in `bodyRT`.
  The shared-wire selection therefore treats a full-width slice of a
  slot as an ALIAS (not a slot); crc16 has one such wire.
* Trust: kernel + `native_decide` (parse oracle, mask equations,
  checkers on `bodyRT`).

## 5. Failure is never reported as success

* Every refusal is `throwError` with a named reason (memories,
  multi-port, Bool output, nested loops, cone shapes, non-reference
  register inputs); the command fails, `lake build` exits non-zero.
* Every generated theorem is elaborated SYNCHRONOUSLY (`Elab.async
  false`) and audited right after: missing (a heartbeat timeout leaves
  no constant) ⇒ the audit's lookup throws; present with `sorryAx` (an
  error recovered inside a proof) ⇒ `throwError`; an axiom outside the
  allowed set ⇒ `throwError`.  This covers the trace, the replay and
  each bridge theorem (`_signal_runOpt`, `_signal_svOpt`,
  `_signal_runRT`, `_text_parses`).
* A bridge whose preconditions fail is SKIPPED with a `logWarning`
  naming the reason and does not appear in the PROVEN line, which lists
  exactly the theorems that hold.  CI (`bench/xiangshan/ci_check.sh`)
  greps the PROVEN line for every expected clause AND for the absence
  of `SKIPPED`, so a silently narrowed chain fails CI.
* Heartbeats: every generated declaration runs under
  `maxHeartbeats 1600000`; exceeding it is an error, not a skip.
* The one gap the audit cannot see: an error raised AFTER a proof's
  goals are closed (a trailing tactic) leaves a complete, sorry-free
  term — the audit passes, the message is logged at the command's
  position, and `lake build` still fails.  Under `SPARKLE_DEEP_TRACE`
  the generator attributes each error message to the generated
  declaration that produced it (measured 2026-09-14 on crc16: a bare
  `have` after the output goal had closed).

## 6. Status per circuit (2026-09-20, after F2 steps 1-10)

crc16CcittHW's guarantee to the printed text is the ROUNDTRIP link
(§4b: the shipping parser trusted as an evaluated oracle on this text);
the forward emitter-semantics theorem (§4a) is a separate, open item
for it (the M4 shl fit rule).  Keep the two apart when quoting it.

| circuit | §1 trace | §2 replay | §3 Opt | §4a SV | §4b RT | wall |
|---|---|---|---|---|---|---|
| shareX4 (1 reg, 1 in, 4 wires) | PROVEN (std + 2 bv) | PROVEN (+2, the trace's bv) | PROVEN (+2, the trace's bv) | PROVEN (+3: trace's bv + seqCheck) | PROVEN (+2; parse +1) | 25 s for both shareX* |
| shareX8 (8 wires) | PROVEN | PROVEN (+2) | PROVEN (+2) | PROVEN (+3) | PROVEN (+2) | (same run) |
| crc16CcittHW (1 reg, 3 in, 16 wires) | PROVEN | PROVEN (+1, the trace's bv) | PROVEN (+1, the trace's bv) | SKIPPED (shl fit rule, statement named) | PROVEN (+1; parse +1) | 93 s, peak 1.98 GB |

`+N` = decision-procedure auxiliaries beyond the standard axioms
(2026-09-20, F2 step 11).  By name: the replay/Opt/RT theorems depend
on `{f}_sdeep_trace._native.bv_decide.ax_*` only; `_text_parses` on
`{f}_sdeep_text_parses._native.native_decide.ax_1`; `_signal_svOpt`
additionally on `{f}_sdeep_signal_svOpt._native.native_decide.ax_1`
(the M4 `seqCheck`).
Conditions: `lake build`, MemoryMax 24G, 1.6 M heartbeats per generated
declaration.  Permanent tests: `Tests/Verification/ConeSharingGen.lean`
(shareX4/8, every clause CI-gated), `Tests/Verification/ConeSharingCrc16.lean`.

## 7. Not connected / remaining trust, in order of weight

As of 2026-09-22 (F2 closed for this route, steps 1–11).  Every
per-instance checker obligation is kernel-checked; what remains is
listed here and each item names its next-milestone entry.

1. **The trace theorem's `bv_decide`** (§1, 1–2 auxiliaries per
   circuit).  The SAT route's LRAT certificate is verified by
   kernel-reducible code, but the verification is run by the compiled
   program, leaving one `bv_decide.ax_*` per call.  This is the only
   remaining trust in the replay / optimizer / re-parse theorems
   (§2/§3/§4b) — they inherit it and add nothing.
2. **The parse oracle** (§4b, 1 auxiliary).  `_text_parses` evaluates
   the shipping `parseAndLowerHierarchical` on the printed text; nothing
   is proven about the parser (F3).  The printer is bridged by
   re-parsing, not by a printer proof; the proven emitter (§4a) is a
   twin of `toVerilog`, not `toVerilog` itself (F3/F4).
3. **`seqCheck` in the forward SV theorem** (§4a, 1 auxiliary,
   shareX* only).  The M4 fragment check handed to
   `certified_forward_trace_module`; a bare `decide` on it does not
   reduce (stuck in 3 ms), so it needs the structural-twin treatment
   the other checkers got.
4. §4a is unavailable for circuits with a truncating literal-amount
   shift — crc16's one documented SKIP (the `bitwiseShl` fit rule).
5. Per-instance instantiation rather than universal quantification over
   the language (F1); and the v1 scope of this route, which REFUSES
   with a named error rather than skipping silently: memories,
   multi-port outputs, Bool-typed outputs, nested loops.
6. Synthesis and silicon are outside the chain (F7).

Performance, for the record (not a guarantee).  Final regression,
clean rebuild of each test, `lake build`, MemoryMax 24G, cgroup
`memory.peak`, one run each (2026-09-22):

| test | wall | peak |
|---|---|---|
| `ConeSharingGen.lean` (shareX4 + shareX8) | 25 s | 0.90 GB |
| `ConeSharingCrc16.lean` (crc16CcittHW) | 93 s | 1.98 GB |
| `ConeKernelSlotShareX` / `Crc16` | 1 s each | — |

crc16 began this PR at 880 s / 2.80 GB.  The remaining hot spots are
kernel `String` matching in `woCheck` and the width-table walk (TODO
C3d — measured; the fix needs shorter IR wire names, which changes
generated RTL, so it belongs to the next milestone).
