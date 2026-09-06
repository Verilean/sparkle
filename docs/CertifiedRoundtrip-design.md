# Certified roundtrip: design and current state

Branch: `poc/roundtrip-proof`.  Status as of 2026-08-31.

## Goal

A CompCert-style statement for Sparkle's emit/parse/lower pipeline:

> Re-ingesting Sparkle's own emitted SystemVerilog produces a circuit
> with the **same cycle-by-cycle trace** as the original IR — proven in
> Lean, not just tested.

and, in the forward direction (M4):

> The emitted SystemVerilog, read by a mathematical semantics of the
> language subset, computes **the same cycle-by-cycle trace** as the
> IR it was emitted from — which removes the PARSER from the trusted
> base for that direction.

`parse (emit x) = x` is FALSE syntactically (lowering normalizes
bit-selects, size casts, signed compares; emission normalizes `~`,
slice-of-op, concat elements), so the target is the **semantic**
statement.

## Architecture: verified core / validated shell

The shipping pipeline is ~73 `partial def`s (no unfolding equations →
nothing is provable about it directly).  The split:

* **Verified core** — total *twins* whose equations mirror the shipping
  code arm for arm: `emitAstExpr`/`emitAstStmt`/`emitAstModule`
  (`Tools/SVParser/EmitAst.lean`), `lowerT`/`lowerTItem`/`memImage`
  (`Tools/SVParser/RoundtripProof.lean`), plus a total mathematical
  semantics (`Sparkle/IR/Semantics.lean`).  All theorems are about the
  twins.
* **Validated shell** — the twins are tied to the shipping functions by
  compile-time `#guard`s that run the REAL emit→parse→lower on probe
  modules, and by corpus-wide executable tests (ParserTest 64–72) over
  the XiangShan CI corpus.  A divergence breaks `lake build`.

The trusted base is therefore: twin↔shipping agreement (executable, not
proven), the string-level printer/parser (M3, tested TCB), and the
optimizer (out of scope by design — `#verify_emit` translation
validation covers it per instance).  M4 additionally removes the
PARSER from the forward direction's trusted base, leaving only the
printer and the SV-subset semantics itself.

## The semantics (M1)

`Sparkle/IR/Semantics.lean`: total, two-state, `Nat` values with
explicit width masking (`mask w v = v % 2^w`).

* `evalExpr` — scalar expressions; **failure is shape-only** (arity,
  `sliceDim`, `index`), never environmental — a load-bearing fact.
* One cycle = `stepModule` = `evalAssigns` (combinational fold, in
  order; topological order is a WF assumption matching the shipping
  `topoSortBody` guarantee) → `regNexts` (registers + sync-read
  latches; reset KIND deliberately ignored — both kinds sample per
  cycle) → `memNexts` (write ports in order, last enabled port wins).
* Memories follow the `Stmt.memory` contract: read-old, shared clock.
* `runModule` — k cycles under an arbitrary input-seeding discipline.
* **Open-module semantics**: instances are combinational no-ops whose
  outputs are free inputs; the trace theorems quantify over any
  instance behavior, and the actual composition is covered dynamically
  by the hierarchical co-sim.
* `Bounded we env` (every value fits its width) is an invariant of the
  fragment: every semantic write is masked at an agreeing width.

## The theorem stack (M2)

Expression layer (`roundtrip_sem`): for the fragment `SFrag`, the
emit∘lower image has the same width and value as the source, for every
bounded environment.  Non-1:1 normalizations are handled by encode
lemmas (`notEncode_sem`, `castEncode_sem`, `sliceEncode_sem`, signed
compares via the bias form).  `sfrag_eval_bounded` shows fragment
values fit their widths.

Statement/module layer:

* `step_roundtrip` — one cycle of the image body equals one cycle of
  the source: final env, register updates, memory state.
* `trace_roundtrip` — k cycles, any seeding, by induction.
* Reorder invariance (`Sparkle/IR/ReorderInvariance.lean`) — the
  shipping module lowering re-sorts the body; `runModule_perm` proves
  any two well-ordered arrangements produce identical traces
  (adjacent-swap/bubble for the fold; contribution multisets +
  unique-key `applyNexts` for the tick; frame/slice determinism for
  memory writes).
* `body_trace_roundtrip` — the composition: if the shipping output
  passes `bodyReorderCheck` (a SOUND decidable bundle: permutation +
  well-ordering + name/key uniqueness) against the statement-wise
  image, its trace equals the source's.
* `certified_body_trace` — the capstone: `semFragCheck m = true` (a
  sound decidable census of the fragment) plus the reorder check imply
  trace equality.  **Every hypothesis is decidable** and is exactly
  what Test 68 evaluates corpus-wide.

## The forward direction (M4)

`Tools/SVParser/SVSemantics.lean` gives the emitted SystemVerilog
SUBSET a semantics: every expression evaluates at a CONTEXT width
`W = max ctx (widthSV e)`, context-determined operands inherit `W`,
and the self-determined boundaries reset it (size-cast arguments,
comparison operands, shift amounts, concat elements, ternary
conditions).  `Tools/SVParser/EmitSem.lean` then proves the emitter
right against it, in four rungs:

* `emit_sem` — for the fragment `SF4`,
  `evalSV wof env (widthOf we e) (emitAstExpr wof e) = evalExpr we env e`,
  carrying `widthSV (emission) = widthOf (IR)` as the induction's
  invariant.  `sf4_emit_isSome` makes the emitter TOTAL on the
  fragment, so the statement is "it emits, and is right".
* `emit_sem_assigns` — the whole combinational phase: Verilog's
  assignment fold (each RHS at its LHS's width, truncated into the
  target) lands in the same environment as `evalAssigns`.  Memory read
  ports are part of this phase (`emit_sem_comboReads`).
* `emit_sem_regs` / `emit_sem_memNexts` — the sequential phase: the
  always-block reset mux and width truncation agree with `regNexts`,
  and the guarded stores agree with `memNexts`.
* `certified_forward_trace` — the capstone: for any width-respecting
  seeding discipline and any cycle count,
  `runModule = runModuleSV`.

Two load-bearing lemmas make the fragment as wide as it is:

* **Context immunity** (`immuneSV`/`evalAt_immune_all`): emissions that
  carry their own mask (casts, slices, fitting literals, 0/1-valued
  compares), are bounded by declaration (idents), or are built
  carry-free from such (bitwise ops, concats, ternaries) evaluate the
  SAME at every width ≥ their own.  This is what makes up-sizing safe
  at the self-determined boundaries, and it unlocks the cast encode,
  width-mismatched compares, and the pervasive firtool idiom
  `(x ^ w'ones) == 32'd0`.
* **Bias encoding** (`xor_top_bit`/`biased_lt`/`biased_le`): the
  emitter's signed compare `((x&m)^sb) OP ((y&m)^sb)` is PROVEN equal
  to two's-complement comparison — unsigned comparison of biased
  values IS signed comparison.

`sf4Check`/`assignsCheck`/`seqCheck` are decidable mirrors with
soundness proofs (`sf4Check_sound` by functional induction), so the
census below is theorem-backed per item, not a heuristic tally.

## Coverage (XiangShan CI corpus, 52 modules)

Roundtrip direction (Test 68):

* **49 theorem-checked** (shipping output = well-ordered permutation of
  the image), of which **47 fully inside the proven semantic fragment**
  — `certified_body_trace` applies end to end.
* 3 behind the optimizer (their reparse differs only by optimizer
  rewrites; equivalence is `#verify_emit`'s translation validation).
* **0 outside.**

Forward direction (Test 72):

* **1026 of 1026 assign RHSs** carry `emit_sem`.
* **52 of 52 modules** have their entire combinational phase certified.
* **52 of 52 modules** have a full certified cycle trace
  (`certified_forward_trace` applies) — TOTAL COVERAGE on this corpus.
  The byte-strobe RMW arrays entered when write ports moved to
  `payloadCheckC` and the memory layer was reproven for payloads that
  read their own array; the CVT32 cone entered when bug #13 fell.

Additional roundtrip quality: emit∘parse is an **IR fixpoint** from the
second generation (Test 67) — three amplifier classes were found and
fixed to get there.

### The honest boundary

Nothing on this corpus remains outside.  The section used to carry two
characterized exclusions, and both are worth remembering for what they
turned out to be:

* The two byte-strobe RMW arrays ("the `shl` width artifact, both
  repairs closed") — shipping bug #9, a hardcoded shift-amount width in
  the strobe lowering.
* One expression in CVT32ModuleS0 ("a 7-bit cone containing
  `sub 0'7 x`, xored against a 32-bit constant … a real divergence") —
  shipping bug #13, a `~` whose narrowed mask silently kept its 32-bit
  fallback because the width inference did not know the arithmetic
  inside a lowered replication.  The "32-bit constant" in the exclusion
  story WAS the defect, verbatim.

Every permanent-exclusion narrative this document has carried was a
defect wearing a boundary's clothes.  The operational lesson: when the
proof refuses something the specification says must hold, establish
which side is wrong before writing the story down.

## Shipping bugs found by the proof work

1. `logic` declarations with unpacked array dims were unparseable —
   Sparkle couldn't re-parse its own emitted memories.
2. wireDecl initializers of procedurally-assigned names became
   competing constant drivers — registers folded away on self-reparse
   (the IR metric had been silently measuring miscompiled reparses).
3. `evalOp` missed `.neg` (semantics gap exposed by the fragment).
4. Sync-read memories broke on self-reparse: the read was claimed AND
   register-lowered with a garbage bit-select of the array.
5. CSim ignored the register reset field per cycle — correct only while
   the reset mux was redundantly baked into the input expression.
6. Over-wide slice elision dropped the zero-extension and shifted
   concat siblings — a miscompile of the FIRST emission.
7. Byte-strobe RMW write data lost its array reads on self-reparse
   (the isArrayName heuristic misses names like "Memory"); fixed by
   extracting the scan's OWN array reads before lowering
   (`lowerMemPayload`), no heuristic.

8. CSim applied masks only at assignment, so unmasked intermediates
   reached width-sensitive CONSUMERS with their carry intact:
   `((x+y) == 4'h0)` compared 16 rather than 0, mux conditions took the
   wrong arm, `(x+y) >> 1` shifted a phantom carry into live bits, and
   an unmasked index walked past the C array.  Found by the M4 3-way
   experiment (formal semantics vs the SV semantics vs iverilog vs
   CSim); fixed with `maskOperandExact` at the consumer sites, and
   `exprIsMasked` split into store/operand positions.  The CUDA
   backends inherit the fix — device code IS CSim.

9. The byte-strobe lowering declared every shift amount at 32 bits.
   A shift's IR width is the max of its operands, so the assembled
   write value for a 10-bit memory measured 32 bits — width bookkeeping
   only (Verilog treats shift counts as self-determined), which is why
   no executable ever disagreed.  Found because the M4 fragment
   REFUSED the payload and the width disagreement was pressed as a bug
   rather than accepted as a proof limitation.
10. A blocking write to a bit range inside `always @(posedge)` —
   `q[35] = d; q[3] = d;` — lowered to `assign q = d`: the scatter
   gone, a 1-bit driver on a 40-bit target, and the CLOCK gone.
   `exprToName` answers `q` for `q[35]`.  Fixed by refusing bit-range
   LHSs in the whole-signal collectors and merging them as a
   read-modify-write at the target's declared width (iverilog-pinned,
   Test 73).
11. A concat-LHS write with fields above bit 31 —
   `{q[103:96], q[7:0]} <= {a, b}` — pinned its scatter at 32 bits, so
   the high field was shifted out entirely; the multi-variable path had
   the same defect one size up (a 64-bit inverse mask CLEARING
   everything above bit 63 on a 128-bit signal).  Both concat-LHS
   paths now work at a width covering the highest bit written
   (iverilog-pinned, Test 74).
12. The REFERENCE SEMANTICS itself: `evalPayload` resolved a payload's
   own-array reads into invented `__memread_*` placeholders and then
   evaluated them under the caller's plain `we`, where undeclared
   names default to width 0.  An arithmetic read-modify-write
   `Mem[a] <= Mem[a] + Mem[a]` on a 10-bit memory computed 0 where
   Verilog computes 10 — the sum masked by `2^0`.  Every green signal
   (census, co-sim, 41 equivalence proofs) sat on top of it, because
   the corpus's byte-strobe shapes are dominated by full-width masks.
   Both payload evaluators now declare the widths of the names they
   invent (Test 75).
13. `~` lowers to `x ^ 32'(-1)` with a post-pass narrowing the mask to
   the operand's inferred width — and the inference did not know
   arithmetic, which the replication lowering `{n{bit}}` =
   `(0 - bit) & mask` contains.  So the mask under `~({7{b}})` silently
   stayed 32 bits: `{3'h5, ~({7{x[0]}})}` computed 1023 where iverilog
   computes 767, the NOT's phantom high ones landing where the concat
   prefix belongs.  XiangShan's CVT32 has this exact shape with prefix
   `3'h7` — all-ones — hiding the value error behind a width
   disagreement that read like a proof limitation (Test 76).

14. The elaborator materializes an HList `Unit`/`PUnit` loop-state
   terminator as a zero-width wire (`_tmp_b = const 0 0`) and packs it
   into the loop-state concat.  In the IR that is inert — a width-0
   element contributes no bits, and CSim agrees — but SystemVerilog has
   no zero-width nets: the backend declared it `logic [0:0]` and emitted
   it as a REAL bit, so the pack concat was one bit too wide and the
   implicit assignment truncation shifted every register left each
   cycle.  An 8-bit `circuit do` counter counted 2, 6, 14, 30, 62 under
   iverilog.  EVERY `circuit do` design's emitted Verilog was affected;
   the IR/CSim paths were always correct, so no simulation-vs-IR test
   saw it — it surfaced only when the M4 fragment checker flagged the
   `const 0 0` shape as outside the SystemVerilog subset and the "why
   can't a zero-width net exist" question was pressed.  Fixed by a total
   IR pass (`Sparkle/IR/ZeroWidth.lean`) at the end of synthesis that
   drops width-0 concat elements, assigns, and wire decls; it skips
   symbolic-width modules (`bitWidth` panics on `W+1`).

Bugs 2/4/7 share a blind spot: the co-sim gate only exercises the FIRST
emission, never the second parse; only the IR metric (and now the
roundtrip checks) see reparse fidelity.  Bug 8 is a different blind
spot: co-sim compares CSim against iverilog on the SAME shapes the
corpus happens to contain, and the width-sensitive-consumer shapes were
simply absent — it took a formal semantics disagreeing with both
executables to surface it.  Bugs 9–13 sharpen the pattern: 9 and 12
are width-bookkeeping errors whose VALUES were right on every shape
any executable ever ran, and 10 and 11 are miscompiles of shapes the
corpus simply lacks.  (#13 combines both: a value error on shapes the corpus lacks, hidden
on the shapes it has by an all-ones prefix.)  #14 is a further case: correct in the IR and CSim, wrong only in the
emitted TEXT, so invisible to every simulation-vs-IR check.  None of
these is reachable by testing the implementation against itself; each fell out
of trying to prove a statement and refusing to accept "the proof
doesn't cover this" until it was established WHICH side was wrong.

Two IR width rules were also corrected, in `widthOf` and its CSim twin
`inferExprWidth` together: a right shift is as wide as its VALUE (the
amount's width used to leak in through the generic max, so
`_GEN >> (idx * 32'd4)` measured 32 bits), which moved the forward
census from 1008 to 1025 expressions and 41 to 44 traces.

## Composition — Signal ≡ emitted-SystemVerilog semantics

The two arcs above are stated over different objects (Arc 1 over
`evalExpr` of inlined cones, Arc 2 over `stepModule`/`runModule`
folds).  `Tools/ConeFold.lean` + `Tools/ConeFoldSlices.lean`
(sorry-free) close that seam, and the `#verify_elab` generator now
composes the whole chain per circuit.

* **The seam** (`cone_agrees_with_fold`,
  `cone_resolved_agrees_with_fold`): total twins `inlineConeT` /
  `resolveSlicesT` of the shipping cone passes, `#guard`-tied to them,
  with width- and eval-preservation proofs.  On a well-ordered,
  memory-free, self-loop-free body with the assignment-width discipline
  (literally `BFrag.assign`'s condition — where the two arcs' hypotheses
  meet), a fully inlined, slice-resolved cone evaluates in the fold's
  environment to the original.  The goal generators call the twins, so
  the spliced cones ARE the theorems' functions.
* **Per-circuit corollaries**, hypotheses discharged by `native_decide`
  on the emitted body constant: `regstep` (`regNexts` = the recurrence's
  next state — the mask killed by the generated `irTrace_bound`, the
  reset wire read 0 because the fold never writes it), `state_trace`
  (the `stepModule` iteration's register state IS `irTrace`),
  `signal_runModule` and its unconditional form `signal_run` (Signal
  value = the `runModule` trace's output wire, every cycle — the run
  success discharged internally via `evalOk`), and `signal_sv` (the
  same against `runModuleSV`, the M4 subset semantics of the certified
  twin emission).  So per circuit, one kernel-checked chain:
  Signal ≡ IR ≡ stepModule ≡ runModule ≡ emitted-Verilog
  semantics.
* **`evalOk`** (`Tools/ConeFoldSlices.lean`): a decidable checker
  certifying that a memory-free body whose assignment RHSs are all in
  the total fragment folds to `some` for ANY seed — `evalExpr` fails
  only on shape, never on the environment (the reorder work's gift), so
  the fold-success hypotheses become `native_decide` obligations rather
  than caller-supplied.
* **Deep-side glue** (`{f}_deep_coneEval_*`): the general-theorem
  route's `Cdo.irState` cone terms rewrite to `evalExpr weM (resolved
  cone)`, the seam's language, via fidelity ∘ `concatNorm_eval` ∘ a
  width-environment congruence; holds on `crc32Engine`.  Replaying the
  full bridge stack over `Cdo.irState` is the remaining deep step.

## Compile cost

The two proof files (`RoundtripProof.lean` ~3.6 kloc,
`EmitSem.lean` ~3.2 kloc) elaborate in ~41 s together, the bulk of it
`roundtrip_sem`; both are leaves, so incremental `lake build`s replay
the oleans at no cost.

## Future work

* A width-indexed `emit_sem` (`∀ W ≥ widthOf, evalAt W = mask W ∘
  evalExpr`) remains the principled generalization of the immunity
  machinery, though nothing currently outside the fragment needs it.
* Closed hierarchical semantics (state trees or a verified flatten) —
  today instances are open-module no-ops and composition is covered
  dynamically by the hierarchical co-sim.
* M3: the string layer — today a tested TCB (parse-equality on every
  corpus expression); a verified printer/parser inverse is the
  classical hard next step, and the last piece between the current
  state and an end-to-end statement about TEXT rather than ASTs.
* Swapping the twins in as the shipping emitter/lowerer, which would
  collapse the twin↔shipping half of the trusted base.  (The cone
  passes are already the twins on the `#verify_elab` path; the file-
  level gap with the shipping emitter now reduces exactly to optimizer
  preservation — every elaborator module classifies `.optRewritten`,
  none `.bad`.)
* Replaying the `regstep`/`state_trace`/`signal_run`/`signal_sv` stack
  over `Cdo.irState` for the general-theorem (deep) route — the G1
  glue lands its cone terms on the seam's language already.

See `docs/CertifiedRoundtrip-TODO.md` for the tracked open-work list.
