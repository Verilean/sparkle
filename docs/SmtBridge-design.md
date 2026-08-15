# Design: SMT bridge — untrusted finder, Lean-verified certifier

Status: **M1 in progress** (emitter + BMC + counterexample replay).
Context: NLnet Task 2; discussion history in `docs/CudaIntraSim-design.md`'s
sibling thread. Related work: IOHK Lean-blaster (no BitVec yet — upstream
contribution planned; `admit`-based, so its trust model is not ours).

## 1. Trust architecture

The solver is a *search engine*, never a *trusted authority*:

```
Sparkle IR ──① SMT-LIB2 emitter──▶ .smt2 ──subprocess──▶ z3 (/bitwuzla/cvc5)
    │
    ├─ sat  ─▶ model → per-cycle input assignments
    │          └▶ ② REPLAY on the CSim C reference (gcc, no GPU/nvcc)
    │             a counterexample must actually violate the assertion in
    │             simulation — false positives from solver OR emitter bugs
    │             are caught here.  (VCD rendering: M1.5.)
    └─ unsat ─▶ bounded proof (BMC) / inductive proof (k-ind, M2)
               └▶ ③ invariants from Spacer re-certified by bv_decide (M4)
```

`sat` needs zero trust (self-validating by replay); `unsat` is trusted only
up to bound k in M1 — the certification story lands in M4.

## 2. Encoding (M1)

Transition-system frames, one set of symbols per cycle `c` (all symbols
`|quoted|` to dodge SMT keywords):

- **Inputs**: `(declare-const |in_c<c>| (_ BitVec w))` per frame (clk
  excluded; rst is an ordinary input — see semantics note).
- **Registers**: frame 0 = `initValue`; frame c+1 = the register's input
  expression evaluated over frame c (a `define-fun`). This mirrors CSim,
  which computes `_next` in eval and latches unconditionally in tick.
- **Memories** (`.memory`) → **SMT arrays** (the capability `bv_decide`
  cannot offer): `mem_0 = ((as const …) 0)`;
  `mem_{c+1} = ite(we_c ≠ 0, store(mem_c, wa_c, wd_c), mem_c)`.
  comboRead: `rd_c = select(mem_c, ra_c)` (reads pre-write, like CSim's
  eval). Sync read: `rd` is a state var, `rd_{c+1} = select(mem_{c+1},
  ra_c)` (write-then-read, mirroring CSim's tick order).
- **Wires**: `define-fun` per assign, in body order (already topological —
  CSim relies on the same property).
- **Properties**: `Module.assertions` (1-bit exprs; violated when = 0).
  BMC: `(assert (or (= A_c0 #b0) … (= A_ck #b0))) (check-sat)` +
  `(get-value …)` over all inputs of all frames.

**Width discipline** (must match CSim's C-promotion+mask semantics):
`emitW e w` emits `e` coerced to exactly `w` bits. Ring ops
(add/sub/mul/and/or/xor/shl, mux, not/neg) commute with truncation → emit
operands directly at `w`. Non-ring ops evaluate at *natural* width
(`CSim.inferExprWidth`) first, then coerce: comparisons (→ 1 bit,
`bvult`/`bvslt`/… at max operand width), `shr`/`asr` (high bits matter),
`slice`, `concat` (first arg = MSB, matching Verilog/SMT conventions).

**Semantics note — reset**: CSim ignores the `rst` port at runtime (reset is
the `reset()` entry point); frame 0 *is* the post-reset state. BMC mirrors
CSim exactly because CSim is the replay reference. (The Verilog backend
honours `rst` in `always` blocks — that divergence predates this work.)

## 3. v1 scope (named error for each exclusion)

- Flat modules only (no `.inst`) — the elaborator inlines by default;
  hierarchical designs must be flattened first.
- `.index` only on memories; array-typed wires unsupported.
- Undriven wires are an error (a free variable would over-approximate and
  invite spurious cex; replay would catch them, but loudly failing is
  better).
- Replay requires ≤ 64-bit input ports (wide state inside the design is
  fine — replay only pokes inputs).

## 4. Testing (same three-layer pattern as the CUDA backends)

1. **Shape** (LSpec, `Tests/TestSmt.lean`): emitted `.smt2` structure on
   fixtures — declare/define frames, `store`/`select` for memories, the
   violation disjunction; rejection errors (`.inst`, undriven wire).
2. **Solver run** (`lake exe smt-bmc-test`, skips without z3):
   - `goodCounter` (saturates at 5, assert `count ≤ 5`) → **unsat** at k=20;
   - `buggyCounter` (wrapping bv4, assert `count < 12`) → **sat** at k=14,
     replay **confirms** the violation cycle;
   - `memGood` (write x, read back, compare with registered x) → **unsat**
     — the QF_ABV demo bv_decide cannot express;
   - `memBuggy` (assert `rd = x` current-cycle) → **sat** + replay confirm.
3. **Replay** is layer 2's second half: generated C main (assertions
   exported as extra outputs so they are struct fields), gcc, run.

## 5. Milestones

M1 emitter+BMC+replay (this) → M1.5 VCD cex rendering → M2 incremental
session + k-induction → M3 CHC/Spacer + invariant import → M4 invariant
reflection + bv_decide certification (the hard, novel part) → M5
solver-agnostic + tutorial chapter. Lean-blaster BitVec upstream
contribution runs parallel to M2/M3.
