# Certified roundtrip: design and current state

Branch: `poc/roundtrip-proof`.  Status as of 2026-08-30.

## Goal

A CompCert-style statement for Sparkle's emit/parse/lower pipeline:

> Re-ingesting Sparkle's own emitted SystemVerilog produces a circuit
> with the **same cycle-by-cycle trace** as the original IR — proven in
> Lean, not just tested.

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
  modules, and by corpus-wide executable tests (ParserTest 64–70) over
  the XiangShan CI corpus.  A divergence breaks `lake build`.

The trusted base is therefore: twin↔shipping agreement (executable, not
proven), the string-level printer/parser (M3, tested TCB), and the
optimizer (out of scope by design — `#verify_emit` translation
validation covers it per instance).

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

## Coverage (XiangShan CI corpus, 52 modules)

* **47 theorem-checked** (shipping output = well-ordered permutation of
  the image), of which **46 fully inside the proven semantic fragment**
  — `certified_body_trace` applies end to end.
* 3 behind the optimizer (their reparse differs only by optimizer
  rewrites; equivalence is `#verify_emit`'s translation validation).
* 2 byte-strobe SRAM arrays: write payloads read the array
  (`Memory[addr]`, IR `.index`) — full coverage needs an
  `evalExpr`-with-memory-state semantics (helpers are already in
  place; see Future work).

Additional roundtrip quality: emit∘parse is an **IR fixpoint** from the
second generation (Test 67) — three amplifier classes were found and
fixed to get there.

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

Bugs 2/4/7 share a blind spot: the co-sim gate only exercises the FIRST
emission, never the second parse; only the IR metric (and now the
roundtrip checks) see reparse fidelity.

## Compile cost

The whole proof stack elaborates in ~34 s, ~29 s of which is the single
`roundtrip_sem` theorem; the file is a leaf, so incremental `lake
build`s replay the olean at no cost.

## Future work

* `.index`/memory-state expression semantics to cover the two SRAM
  arrays (the `extractArrayReads`/`substArrayReads` helpers are total
  and twin-reusable).
* Closed hierarchical semantics (state trees or a verified flatten).
* M3: the string layer — today a tested TCB (parse-equality on every
  corpus expression); a verified printer/parser inverse is the
  classical hard next step.
* M4: a semantics for the emitted SystemVerilog SUBSET and a direct
  emit-correctness theorem (`⟦e⟧_IR = ⟦emit e⟧_SV`), which would remove
  the parser from the trusted base for the forward direction — the
  NLnet Task 2/3-scale research item.
