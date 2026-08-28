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
* **rt-more (+13%)** — diagnosis CORRECTED by measuring at the right
  synthesis stage. `synth -run coarse` is too early to tell: it reports
  the same totals whether or not shared cones are hoisted, because its own
  CSE folds them. After a FULL `synth; opt -full` the gap survives
  (FreeList_4 8,426 → 10,392 = 1.23×), so this IS real gate cost.

  Where it goes: flip-flops are IDENTICAL (252/156/60/4/21 by type) and so
  is `$_MUX_` (1,641 both sides). The entire excess is the boolean gate
  layer, dominated by `$_ANDNOT_` 557 → 1,022.

  The cause is not duplicated *cones* but the fused-expression shape
  itself. firtool emits a register as separate guarded statements
  (`if (…) r <= C; else r <= T;`); Sparkle collapses each register into ONE
  mux expression and so rebuilds the whole guard chain per register —
  FreeList_4 carries 168 copies of a single guard term. yosys shares some
  but not all of them.

  Two things were tried and MEASURED:
  - Folding the dead `reset ? init : …` arm (a general complementary-
    condition mux rule, ParserTest 56): correct and kept, but worth only
    3 cells corpus-wide. The arm was already nearly free.
  - Hoisting repeated subexpressions into wires (whole-wire CSE cannot
    reach inside expressions): shrank emitted source 8% and hoisted 681
    wires in FreeList_4, but cell count went 10,392 → 10,408 — slightly
    WORSE, because each hoisted wire is then used both plain and negated
    (168 `$_NOT_`s that the un-hoisted form let yosys share). Reverted.

  The real fix is emitter-architectural: emit guarded `if` statements per
  register instead of one fused mux expression. Not attempted here.

Phase-2 verdict: **re-emission is functionally faithful (RT✗ = 0 on every
runnable leaf), the JIT agrees except one open module, and the cell
metric now measures style, not correctness.** Next: Phase 3 = KunminghuV2
(big config) + hierarchical co-sim (iverilog -y over the whole tree);
Phase 4 = Verilator-vs-CSim performance shootout (`make emu` workloads).

## Phase 3 — the full config (DefaultConfig = Kunminghu core)

The repo (branch `kunminghu-v3`) has no "KunminghuV2" config class; the
full-size build is `CONFIG=DefaultConfig`.  Generation:
`PATH=$HOME/bin-mill:$PATH NOOP_HOME=$PWD nix shell nixpkgs#jdk17 -c make
verilog CONFIG=DefaultConfig` — mill wrapper resolves `.mill-version`
0.12.17 from ~/.cache/mill/download.  219 s elaboration, 2,050 build/rtl
files / 1.5 GB (MinimalConfig outputs archived at build/rtl_min[_rt]).

Roundtrip survey: **2,047 / 2,048 OK (99.95%)** in 2,281 s (16 workers);
the sole exclusion is ClockGate.sv (`always_latch` ICG), same as
MinimalConfig.  ZERO new failure classes — the Phase-1/2 front-end work
generalizes to the full core unchanged.

Phr postscript (fixed before Phase 3 started, commit 65a54d7): the last
Phase-2 JIT mismatch was CSim's `constAmt` treating every NON-CONSTANT
wide-shift amount as 0 — Phr rotates its 52-bit path history with the
doubled-vector idiom `{phr, phr} >> ptr` (104 bits), so every folded
history read the unshifted vector.  Dynamic amounts now emit a runtime
word loop (Test 49).  Leaf co-sim on MinimalConfig is now clean:
RT✗ 0 / JIT✗ 0.

DefaultConfig leaf co-sim (same harness, sliced, --max-kb 512):

| verdict | count |
|---|---|
| OK (orig-iverilog ≡ rt-iverilog ≡ CSim JIT) | **450** |
| RT mismatch | **0** |
| JIT mismatch | **0** |
| golden-side tool failures | 54 |
| skipped (hierarchical / wide ports / no clock) | 1,444 (+78 files > 512 KB) |

Clean on the FIRST run — every miscompile class found on MinimalConfig
was fixed at the right layer, so the 2× bigger config added nothing.
Remaining Phase-3/4 work: hierarchical co-sim (iverilog -y over the whole
tree vs a multi-file CSim design), and the Verilator performance
shootout (`make emu` workloads vs the CSim JIT).

## Phase 3.5 — DefaultConfig leaf/hier co-sim hardening (post-reboot rounds)

SRAM macros (`array_*`/`ram_*`/`dt_*`, 93 files) now LOWER correctly:
masked partial-word writes (`Memory[addr][k +: w] <=`) via a linear RMW
(the old builder doubled the expression tree PER MASK BIT — 2^38 nodes on
array_128x38, the likely cause of the machine-freezing OOMs), the writing
block's real clock, priority-mux composition of multiple guarded writes,
first read claims the Stmt.memory port with extra reads as `Memory[addr]`
assigns.  **Resolved**: `Stmt.memory` now carries extra read/write PORTS
(`extraWrites` / `extraReads`), so multi-port macros keep every port.
XiangShan's memory macros are 61x 1R1W, 31x single read-write, and one
8R8W (dt_352x1, the Difftest array) — all 93 now round-trip and
co-simulate cleanly (RT 0 / JIT 0 over the 31 harness-runnable ones).
Semantics: all ports share the clock, reads see pre-write state, and
simultaneous same-address writes resolve last-port-wins (the Verilog
`always_ff` rule).  Dual-port and two-port memories need no new IR —
they are simply two read and/or two write ports.

The fix touched 9 further sites that REBUILD a `.memory` statement (four
in the lowering's refinement passes and sub-module flattening, five in
the IR optimizer): each dropped the new fields and silently degraded a
multi-port memory back to port 0.  Regression test: `svparser-test`
Test 50 checks both the IR port counts and the emitted Verilog.

Determinism: both iverilog sides now compile with
`-DRANDOMIZE_REG_INIT -DRANDOM=32'h0` (firtool leaves reset-less
registers X by default; X-optimism in guards legitimately diverges from
the IR's defined init=0), and stimulus is splitmix64-mixed (a raw LCG's
bit 0 alternates every draw — paired 1-bit enables sat in antiphase and
memories stayed X forever), with addresses shaped into [0,3] and write
masks all-ones so reads hit written entries.

Wide (>64-bit) ports: sv-cosim drives and samples them as one 64-bit word
per slot (`port#k`), so nothing is skipped for width up to 4096 bits.
Getting there required matching the two sides exactly at the top word:
the TB slices it to the RESIDUAL width (on a 138-bit port `[128 +: 64]`
reads 54 bits past the end and Verilog returns X, so the all-X check
rejected runs whose every real bit was defined — that alone was the whole
"X/Z in golden" skip class), and the C side masks the same bits.  Wide
write masks are shaped all-ones like narrow ones, because firtool emits
PER-BIT write enables (array_128x76 has a 76-bit wmask) and a random one
leaves most bits never written.  The emission-cost guard also had to stop
multiplying word count at every NODE — that compounded as words^depth and
scored a 25 KB masked-RMW memory at 3e11.  Result on the 93 SRAM macros:
93/93 three-way, 0 skipped (was 22 executed / 62 skipped for wide port).
The skip counter now breaks down by reason, so "the harness cannot drive
it" is distinguishable from "the golden run is all-X".

CSim fixes found by the sweeps: dynamic scalar shifts ≥ container width
(C UB wraps mod 32/64; Verilog says 0 — BusyTable's random read indexes),
`sparkle_wide_shr64` helper for wide dynamic shifts nested in scalar
contexts (packed-array dynamic select), narrow/compound operand BOXING
for wide add/sub/concat (FMA's borrow chains), and the instance-merge CSE
no longer treats an input fed by another instance's output as this
instance's output (MulModuleS0's 16 PPGens all shared booth4_31's code).

**Final leaf sweep: OK 994 / RT✗ 1 (dt_352x1 multi-write-port, known) /
JIT✗ 0** out of ~1,970 candidates (937 skipped: hierarchical-only shapes,
78 >512 KB, 16 golden tool failures).

Hier sweep (pre-fix round: OK 248 / RT✗ 12 / JIT✗ 51) — the remaining
work list, classified:
* TwoLevelRRArbiter class (~15): bidirectional combinational handshake
  THROUGH instances = a cycle at instance granularity; needs K-round
  relaxation (or per-port scheduling) in CSim eval — the NLnet Task-1
  "Mealy boundaries" item.
* Wide-arithmetic internals (Mul/FMA family): RESOLVED.  sv-cosim now
  drives and samples >64-bit ports (one 64-bit word per slot), which made
  the bisect possible.  The CSA-tree divergence was a short `memcpy`, not
  the arithmetic: a wide concat NARROWER than its destination (Booth
  partial products are 96-bit sign-extended concats assigned to 128-bit
  wires) was copied with `sizeof(dst)`, reading past the compound literal
  so the top word held adjacent memory instead of the zero fill.  Two
  further bugs found building the reproduction stopped these modules from
  compiling at all: the top-level wide `shl`/`shr` arms subscripted an
  un-materialised operand, and `wideAddSubExpr` / the wide-mul arm cast to
  `uint64_t` BEFORE subscripting.  Pinned by ParserTest 51-53.
* RenameTable_3-class: iverilog's vvp hits its 512-flag codegen limit on
  our single-expression register muxes — an emitter-style item (share
  condition subexpressions), same root as the cell-count redundancy.
* NCBUpstreamRXREQ: one real RT logic diff, untriaged.

## CI gate

`bench/xiangshan/ci_check.sh` (workflow: xiangshan-roundtrip.yml) runs on
every SVParser/IR/backend PR against a 52-file corpus that is NOT
committed — it is third-party generated code (XiangShan, MulanPSL-2.0)
hosted as the release asset `xiangshan-corpus-v1` and downloaded +
sha256-verified by the script (NOTICE inside the tarball;
instantiation-closed): compile-
speed budget, yosys formal equivalence (38 proven; unproven = induction
limit, gated only against baseline regressions), 3-way co-sim (RT and
CSim-JIT both vs iverilog golden), and the Sparkle-native IR node-count
metric vs `ci_baseline.tsv` (the fast redundancy signal; yosys cell
counts stay offline in compare_stat.sh).

`#verify_emit f` (Tools/SVParser/VerifyEmit.lean) covers the OTHER
direction — Sparkle-authored circuits: emitted SystemVerilog is reparsed
and each register/output cone is PROVEN (bv_decide, kernel-checked)
equal to the source IR under rst = 0.  Demo:
Tests/Verification/VerifyEmitDemo.lean.

Known emitter-quality debt this exposed: RenameTable's emission is
306 MB of text (29M IR nodes — the per-register mux forests share
nothing).  Excluded from the CI corpus; the subexpression-sharing
emitter work tracks it.

## verilog → IR → lean₄ → IR → proof (the other round trip)

`lake exe sv-to-dsl <rtl-dir> [--emit out]` prints ingested RTL back as
Sparkle circuit-DSL source (`Tools/SVParser/DslEmit.lean`), and
`#verify_dsl_roundtrip` proves the printed source re-synthesizes to an
equivalent design (per-register / per-output cone equality, `bv_decide`,
under rst = 0).  Together with the Verilog-side round trip this closes
both loops through the IR.

Survey on DefaultConfig (1,847 files ≤ 128 KB): **216 print as
circuit-DSL today** — and "printable" now means "elaborates": shapes
whose printed form would not typecheck are declined with a named error
rather than counted (the earlier 228 included eight-in-twelve sampled
modules that printed but failed to elaborate).  What blocks the rest, in order:

| blocker | files | note |
|---|---|---|
| sub-instances | 644 | needs hierarchical DSL printing (`@[hardware_module]` children) |
| more than one output | 880 | multi-output DSL returns are the elaborator's known tuple-output gap |
| memories | 93 | `Stmt.memory` has no DSL surface yet |
| operators outside the v1 subset | 1 | `neg` |

Proven end-to-end on real XiangShan RTL
(`Tests/Verification/XiangShanDslRoundtrip.lean`, machine-generated
source pasted verbatim): `AddWModule` (combinational, 1 cone),
`PipelineStallReason` (6 registers, 7 cones), `VtypeModule` (the CSR
vtype register file, 5 registers, 6 cones).

Decompiler details worth knowing: register-bundle reads
(`concat[r0,r1,…][hi:lo]`) are folded back to plain register references,
firtool's in-expression reset arm (`mux(¬rst & c, v, mux(rst, init,
hold))`) is folded away because the DSL keeps reset in `Signal.reg`, and
every register READ is printed with an explicit `Signal` ascription (a
`Reg` binder does not coerce where `.map` / `++` / `Signal.ult` expect a
`Signal`).  Purely combinational modules print without `circuit do`,
which requires at least one register.

### CI phase 4 — the lean₄ round trip is gated

`Tests/Verification/XiangShanDslRoundtrip.lean` holds machine-generated
circuit-DSL source for twelve real XiangShan modules (register counts
0..32: AMOALU, ClockCrossingReg, DelayN, AsyncResetSynchronizer,
Iprio0Module, DelayNWithValid, ClmulModule, CaptureChain, AddWModule,
PipelineStallReason, VtypeModule) and proves all 85 register/output
cones with `bv_decide` in 6.3 s.  `ci_check.sh` phase 4 runs it and
reports the decompiler's printable count.

Elaboration fixes this required (each a case where the printed source
looked fine but would not typecheck):

* slices print as `.map (fun x => BitVec.extractLsb' lo w x)` — the
  `x[hi, lo]` form has the syntactically unreduced width
  `BitVec (hi - lo + 1)`, which the DSL's arithmetic instances reject
  and the synth elaborator cannot inline;
* mixed-width binary ops and comparisons (IR inherits Verilog's context
  sizing, e.g. `BitVec 4 * BitVec 32`) are normalized to the wider
  operand;
* shapes where that normalization would build absurd terms — a dynamic
  shift of a 4096-bit packed-array value, giving `0#4092 ++ …` — are
  declined instead of printed;
* generated files carry `set_option maxRecDepth 8192`, since decompiled
  cones are deep single expressions.

Still out of reach: modules above ~66 registers hit `HListWireable`
instance-synthesis limits in `circuit do` (AgeDetector_27, 120
registers), plus the structural blockers above (sub-instances,
multi-output, memories).
