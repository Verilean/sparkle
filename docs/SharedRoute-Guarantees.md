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
  reuses it, with no `native_decide` fallback.  Measured: crc16's replay
  auxiliaries 126 → 108 and each body bridge 180 → 162, for +16 s on an
  880 s run.  What is still `native_decide` here: the G1 glue equations,
  the refs-membership facts, and `hwfCheck`'s lookup-agreement fact.
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
  `rtNorm weM (stripMask wofM coneOpt) = rtNorm weM coneOrig`
  (`native_decide`).  `rtBridge_eval` (Tools/ConeFoldRT.lean, kernel,
  via `stripMask_eval` and `rtNorm_eval` on the bounded settled
  environment) then makes the two cones evaluate alike, and §2's chain
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

## 6. Status per circuit (2026-09-19, after F2 steps 1-7 and the reader fix)

crc16CcittHW's guarantee to the printed text is the ROUNDTRIP link
(§4b: the shipping parser trusted as an evaluated oracle on this text);
the forward emitter-semantics theorem (§4a) is a separate, open item
for it (the M4 shl fit rule).  Keep the two apart when quoting it.

| circuit | §1 trace | §2 replay | §3 Opt | §4a SV | §4b RT | wall |
|---|---|---|---|---|---|---|
| shareX4 (1 reg, 1 in, 4 wires) | PROVEN (std + 2 bv) | PROVEN (+37) | PROVEN (+55) | PROVEN (+56) | PROVEN (+55; parse +1) | 65 s for both shareX* |
| shareX8 (8 wires) | PROVEN | PROVEN (+61) | PROVEN (+91) | PROVEN (+92) | PROVEN (+91) | (same run) |
| crc16CcittHW (1 reg, 3 in, 16 wires) | PROVEN | PROVEN (+108) | PROVEN (+162) | SKIPPED (shl fit rule, statement named) | PROVEN (+162; parse +1) | 343 s, peak 2.82 GB |

`+N` = decision-procedure auxiliaries beyond the standard axioms.
Conditions: `lake build`, MemoryMax 24G, 1.6 M heartbeats per generated
declaration.  Permanent tests: `Tests/Verification/ConeSharingGen.lean`
(shareX4/8, every clause CI-gated), `Tests/Verification/ConeSharingCrc16.lean`.

## 7. Not connected / remaining trust, in order of weight

1. `native_decide` in the obligations (F2): checkers keyed on
   `Std.HashMap`, cone-inlining and G1 equations, the mask equations,
   `seqCheck`, the parse oracle.  Method exists (first pass moved the
   list-shaped body checkers to kernel `decide`).
2. The shipping printer is bridged by re-parsing (4b), not by a
   printer proof; the proven emitter (4a) is the twin, not `toVerilog`
   (F3/F4).
3. 4a is unavailable for circuits with a truncating literal-amount
   shift (crc16).
4. Per-instance instantiation of the whole chain (F1); v1 scope
   (memories, multi-port outputs, Bool outputs, nested loops refused).
5. Synthesis and silicon are outside the chain (F7).
