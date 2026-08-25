# XiangShan production-scale validation

Goal: prove Sparkle's SVParser → IR → backends pipeline at production scale,
using XiangShan (OpenXiangShan's out-of-order RISC-V) — the largest open
Chisel-generated RTL available.

## The two questions (in the user's words)

1. **Roundtrip fidelity**: XiangShan Verilog → Sparkle IR → Verilog again.
   Does the same RTL come back?  Any redundant logic introduced?
2. **Simulation competitiveness**: Sparkle CSim JIT vs Verilator on the
   same design — speed and correctness.

## Method

### Phase 1 — bring-up (MinimalConfig)
- `make verilog CONFIG=MinimalConfig` in the XiangShan checkout
  (needs JDK+mill: `nix shell nixpkgs#jdk17 nixpkgs#mill`).
- Feed each `build/rtl/*.sv` through `parseAndLowerFlat`; **catalog every
  parse/lower failure** with the construct that caused it.  This catalog IS
  the deliverable of phase 1 — it becomes the SVParser work list.

### Phase 2 — roundtrip metrics (objective, not eyeball)
For each module that parses:
- structural stats before/after: module/instance/register/wire/memory
  counts (Sparkle IR side vs original, via yosys `stat` on both);
- **redundancy metric**: `yosys -p "read_verilog; synth; stat"` cell counts
  original vs roundtripped — equal-ish cells = no redundancy introduced;
- per-module iverilog co-sim (the existing `iverilog-roundtrip-test`
  machinery) for behavioural equivalence on random vectors.

### Phase 3 — the big one (DefaultConfig / KunminghuV2)
Same pipeline at full scale; memory/time profiling of parse+lower+emit
(SPARKLE_PROFILE=1); fix scaling bottlenecks as found.

### Phase 4 — simulation shootout
`make emu` (Verilator) vs Sparkle CSim JIT on the same workloads
(ready-to-run/coremark), cyc/s and correctness vs NEMU difftest.

## Known-in-advance parser gaps to expect (Chisel/FIRRTL emission)
- SRAM blackboxes (`array_*_ext`) — need behavioural models or blackbox
  handling; DPI-C difftest imports — must be excluded at generation or
  stripped; `$fwrite`/assertion blocks; `always_ff`-style SV constructs.

## Phase 1 findings (2026-08-15, MinimalConfig, firtool-1.149.0)

Generated: 1,943 .sv files, 1.1 GB. Survey (`lake exe sv-roundtrip`):

- **74% parse+lower+emit OK** (1,438/1,940 excl. 3 giants), including
  files up to 3.5 MB.
- **502 parse failures**, construct histogram (the work list, priority
  order):
  1. **`N'(expr)` size casts** — `64'({33'h0, a} + b)` — the dominant
     class by far; firtool emits width casts everywhere.
  2. **Packed multi-dim arrays** — `wire [3:0][1:0] _GEN = {...}` +
     `'{...}` assignment patterns + dynamic element indexing
     (`_GEN[state]`); firtool's case-mux lowering idiom.
  3. Reduction operators in some positions (`{~(^(x))}` in dataCheck).
  4. A small instance-connection class (IntRFWBCollideChecker style).
- **Throughput**: linear ~4.6 MB/s/core on regular files; harness runs
  24-way parallel (round-robin over size-sorted files, incremental
  part-file catalogs).
- **Two construct-driven superlinear walls** (NOT byte-size-driven):
  PMP.sv (203 KB, deep nested compare/ternary chains) takes 22 s parse +
  22 s lower, vs 1.6 s + 1.9 s for a 3× larger regular file. Suspects:
  operator-precedence backtracking (`attempt`) in the parser, and a
  matching recursion in Lower. Emit is always ~0 ms.

Phase-1 work list, in order: (1) size casts, (2) packed dims + `'{}` +
dynamic element select, (3) parser/lower complexity on deep nesting,
(4) the long-tail classes. Then re-survey to 100%, then Phase 2 metrics.

## Phase 1 progress log

| step | OK rate | notes |
|---|---|---|
| baseline | 74.1% (1438/1940) | 502 parse failures; 3 giants never finished |
| + `N'(expr)` size casts | — | 502 → 275 failures |
| + packed multi-dim arrays (`[A:B][C:D]`, `'{…}`, dynamic elem select via `+:`) | — | 275 → ~120 |
| + **O(file²) `fail()` fix** | **93.7% (1818/1941)** | full 1.1 GB corpus in **139 s wall** (24 workers); ICacheWayLookup 352 s → **355 ms (992×)** |

The `fail()` bug: the lexer's error path built its "near" context with
`chars.toList.drop pos` — O(file) — and `attempt` uses failure as control
flow on every operator probe, giving O(file²) with a huge constant.
`Array.extract` (O(30)) fixed parse AND lower (which re-parses).

Remaining 123 failures (long tail): `^(…)` reduction-xor in expressions,
`$signed(…)` arithmetic forms, a few instance-connection shapes
(IntRFWBCollideChecker / DelayN / SRAMTemplate / skidBufferConnect classes),
Rob.sv's class. TLFIFOFixer (3.5 MB) still takes 120 s — a second-order
hotspot for later.

## Long-tail fixes (same day)

| fix | effect |
|---|---|
| signed literals `N'sh…` + `$signed` marker retention | the `$signed(x) > -7'sh1` family — and closed a latent **miscompile**: the old parser DROPPED `$signed` on plain wire refs, silently turning signed comparisons unsigned. Comparisons now pick `lt_s`/`gt_s`/… whenever either side carries the marker (stripped, native-width compare — firtool emits same-width operands). |
| empty instance connections `.port (/* unused */)` | the IntRFWBCollideChecker / DelayN / SRAMTemplate / skidBuffer classes |
| reduction XOR `^(…)` | expanded to an explicit bit-fold when the operand width is static (all firtool uses are slices — CHI dataCheck parity bytes); unknown width fails loudly via an undeclared wire, never guesses |

**Result: 1,940 / 1,941 = 99.95% roundtrip OK** (150 s wall, full corpus).
The one exclusion is `ClockGate.sv` (`always_latch` — a latch-based ICG
cell, a physical-design primitive outside Sparkle's single-clock register
model; blackbox territory, as for Verilator's `--conv` style flows).

Second-order hotspot noted: TLFIFOFixer.sv (3.5 MB) takes 123 s.
Regressions: svparser-test 44/44, LiteX all phases PASS.

## Phase 2 — roundtrip fidelity: yosys cell metric + 3-way co-sim

Harness (`feat/xiangshan-validation`, uncommitted until Phase-2 sign-off):

* `bench/xiangshan/compare_stat.sh <orig> <rt> <out.tsv> <jobs>` — per-file
  `yosys synth -run coarse; stat` cell counts (needs `read_verilog -sv` for
  Sparkle output; yosys 0.62 prints "N cells", awk `$2=="cells"`).
* `lake exe sv-cosim <orig-dir> <rt-dir> [--jobs N] [--cycles K]` — 3-way
  co-sim per LEAF module (no sub-instances, ports ≤64 bit, has a clock):
  same LCG stimulus into (1) iverilog on the original = GOLDEN,
  (2) iverilog on the re-emitted Verilog, (3) the CSim C JIT.
  Golden X/Z cycles are skipped; verdicts: OK / RT✗ / JIT✗ / tool-fail.
* Both harnesses use `parseAndLowerHierarchical` — **the flat lowering
  silently DROPS instantiations of modules not defined in the same file**
  (RNLinkMonitor lost its 3 LCredit2Decoupled instances; yosys 20 vs 7
  cells). Worth an upstream issue on `parseAndLowerFlat`.

### Fidelity bugs the first co-sim round caught (all fixed same day)

First round: OK 258 / RT✗ 277 / JIT✗ 29 / tool-fail 26 / skipped 1329.
Every failure class traced to a real front-end/optimizer bug:

1. **Phantom `rst` on reset-less registers** (most "iverilog(rt) does not
   compile"). `always @(posedge clock)` with enable-only updates got
   `(rst, asynchronous)` with a hardcoded name that exists in no such
   module → "Unable to bind wire/reg/memory `rst'". Now: shared `_no_rst`
   wire driven by `1'd0`, `synchronous` kind (clock-only sensitivity).
   Surfaced a 4-layer chain of "register reset is a STRING field, so no
   Expr walker sees it" bugs — reachabilityDCE roots, `countAllUses`,
   single-use inlining, and Phase-4.5 liveness all dropped the reset
   wire's driving assign; each layer needed the reset name counted as a
   use (`Lower.lean` reachabilityDCE, `Optimize.lean` countAllUses /
   resetNames guard / regResets edge).
2. **32-bit NOT mask poisoning ternary conditions** (the value-mismatch
   RT✗ class, e.g. Mhpmcounter*: `w_wen=1` write ignored). `~x` lowers to
   `x ^ 32'hffffffff`; the mask-narrowing pass treated *declared scalar*
   (range-less) wires as unknown width and left the 32-bit constant, and
   Verilog context-determined sizing then makes `~w_wen` = `32'hfffffffe`
   — TRUE as a ternary condition even when `w_wen` is 1. Fix:
   `exprWidthForNarrow` now knows a range-less declaration IS 1 bit (and
   comparison ops are 1 bit). Same root cause as every JIT✗ (`0xff` vs
   `1`): the unmasked 32-bit XOR landing in a narrow C struct field.
3. **Optimizer Phase-4.5 fuel exhaustion silently pruning LIVE registers**
   (the huge "rt has FEWER cells" yosys deltas: RenameTable 15018→1140
   cells, 323→83 registers, SSIT 9334→96…). The register-liveness BFS
   charged fuel per worklist POP (revisits included) with a
   `body.length * 8` budget; XiangShan modules have few statements but
   enormous mux expressions, so the walk stopped early, live registers
   (`spec_table_0..2`, whole arch/difftest tables) were pruned, Phase 5
   then dropped their refs from concats, and `declareOrphanRefs` patched
   the orphans with `assign x = 32'd0` — structurally valid, functionally
   wrong, and the `allOutputsDriven` fail-safe can't see it. Fix: fuel =
   seeds + TOTAL ref count (the exact push bound), here and in the
   memory-cone protect walk (same pattern).
4. **`begin : ` named-block strip eating identifiers** — `io_in_begin :
   8'h0` inside a ternary matched the substring split and the rest of the
   line vanished (ByteMaskTailGen, the 1940-vs-1939 mystery file). Now
   token-boundary-checked.

Verification after fixes: probe trio (Mhpmcounter11Module,
Hstateen2Module, WBArbiter) all 3-way OK; RenameTable re-emits all 323
registers with the full 32-element `_GEN` concat; svparser-test 44/44,
LiteX all phases, `lake test` exit 0.

**Moral for the pitch: the 3-way co-sim + cell-count metric found FIVE
distinct silent-miscompile classes in one afternoon — exactly the
production-validation loop the NLnet Task 3 budget funds.**

### Round 2 (same day): the remaining clusters, root-caused and fixed

Second co-sim round (after the round-1 fixes): OK 435 / RT✗ 1 / JIT✗ 1 from
~497 runnable leaves. The clusters in between, each a distinct backend bug:

5. **Reduction-AND on non-32-bit operands** (the AgeDetector✗ ×9 class):
   `&x` lowers to `(x ^ 32'hffffffff) == 32'd0`, constantly false for a
   5-bit operand. `exprWidthForNarrow` now recurses through bitwise ops
   (max), `concat` (sum of member widths) and mux arms, so the mask
   narrows to `5'h1f` etc. — the follow-up issue #41 deferred, done.
6. **CSim `exprIsMasked` believed every constant** (`.const _ _ => true`),
   so `x ^ 32'hffffffff` feeding a 1-bit output skipped the store mask —
   every remaining JIT `0xff`-vs-`1` (ICacheMshr ×14, PMPChecker, Debug,
   RRArbiter…). Now a constant is masked only if its declared width fits.
7. **Signed comparisons read the sign bit of the CONTAINER, not the
   value** — in BOTH backends. Verilog: `$signed(expr)` takes expr's
   self-determined width, and a lowered size cast like
   `(({6'd0, x} >> 0) & 6'h3f)` is a 12-bit container whose bit 11 is
   padding (FIFOReg's FIFO-wrap flag was constantly true). CSim:
   `(int8_t)x` puts a 6-bit value's sign on bit 5, not bit 7. Both now
   emit a bias comparison — `((A & m) ^ s) OP ((B & m) ^ s)` with
   `s = 2^(w-1)` — unsigned and container-width-independent; Verilog
   falls back to `$signed()` only when no operand width is derivable.
8. **CSim wide-source slice dropped the third word**: a 33..64-bit slice
   at a non-zero offset spans up to 3 source words (`ram[88:25]`), but
   the emitter combined only two — Queue1_RegMapperInput lost the top
   half of its 64-bit payload. Now the general OR over words lo/32..hi/32.
9. **Register declarations now carry the IR initial value**
   (`logic [3:0] r = 4'h0;`): a reset-less register started as X in
   iverilog while the golden randomizes it in an `ifdef ENABLE_INITIAL_REG_`
   initial block (CounterFilter✗). The IR register model HAS an initial
   value — CSim's `reset()` always applied it; the Verilog emitter now
   says it too.

Harness hardening from the same session: sv-cosim gained `--max-kb`
(default 512) and `--skip`/`--limit` slicing (the Lean allocator's
high-water retention peaked at 52 GB over one long run), plus a
pre-`toCDesign` **emission-cost guard**: CSim's wide (>32-bit) emitters
re-emit operand trees once per 32-bit word, so cost multiplies down the
tree — VpnTable (widest wire only 40 bits!) produced a 23 MB single-line
C expression and >50 GB of transient allocation. The guard mirrors the
emitter's recursion with saturating arithmetic and skips such modules
(`bench/xiangshan` runs use `/tmp/cosim_sliced.sh`-style fresh-process
slices). Root fix for the emitter (hoist shared wide subtrees into
temporaries) is future work — it also affects big SVParser-lowered
designs on the normal JIT path.

### Final Phase-2 numbers (MinimalConfig, 1,941 files)

3-way co-sim over every ≤64-bit-port, single-clock LEAF module
(497 runnable; 1,371 skipped as hierarchical/wide/no-clock, 51 as >512 KB,
60 golden-side tool failures — original files iverilog can't elaborate
standalone):

| verdict | count |
|---|---|
| OK — orig-iverilog ≡ rt-iverilog ≡ CSim JIT, 20 cycles | **436** |
| RT mismatch (re-emitted Verilog wrong) | **0** |
| JIT mismatch | **1** (Phr.sv — open; IR→Verilog is correct, CSim cone diverges post-enable) |

For calibration, the FIRST run of the same harness scored OK 258 /
RT✗ 277 / JIT✗ 29 — everything in between was a real, now-regression-
tested bug in the SVParser lowering, the IR optimizer, or the two
backends. Regressions all green: svparser-test 48/48 (tests 45-48 pin the
new classes), LiteX all phases, `lake test` exit 0.

### Redundancy metric (yosys `synth -run coarse` cell counts, orig vs rt)

1,604 modules comparable (336 excluded: yosys can't elaborate one side
standalone — `ifdef`-dependent originals, mostly):

| bucket | modules | cells Δ |
|---|---|---|
| identical count | 394 | 0 |
| rt MORE cells (roundtrip redundancy) | 1,173 | +143,247 |
| rt FEWER cells (Sparkle folded orig redundancy) | 37 | −24,722 |
| total | orig 912,289 → rt 1,030,814 | **ratio 1.13** |

Reading the two tails:

* **rt-fewer** is now dominated by legitimate folding — AheadBtb
  (21,098→7,848) keeps all 1,153 registers; the drop is the IR CSE
  merging firtool's duplicated compare/mux cones (issue-#107 machinery).
  That's an actual answer to "does XiangShan's generated RTL carry
  redundancy": yes, and Sparkle's optimizer finds some of it. (Before the
  fuel fix this bucket was 96 modules / −197k cells of silently DELETED
  logic — the metric only became meaningful once co-sim forced
  correctness.)
* **rt-more (+13%)** is emission-style redundancy, not logic: per-register
  mux chains duplicate shared condition cones (RenameTable ×1.9) and each
  register's data expression still carries a dead `reset ? init : …` arm
  inside the `else` branch of an `if (reset)`. Both are Phase-3 emitter
  improvements (share condition wires; strip the duplicated reset arm).

Phase-2 verdict: **re-emission is functionally faithful (RT✗ = 0 on every
runnable leaf), the JIT agrees except one open module, and the cell
metric now measures style, not correctness.** Next: Phase 3 = KunminghuV2
(big config) + hierarchical co-sim (iverilog -y over the whole tree);
Phase 4 = Verilator-vs-CSim performance shootout (`make emu` workloads).
