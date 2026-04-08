# Known Issues

## Issue 1: pcpi_mul Standalone JIT Tests (Test 21-21e) FAIL — **RESOLVED (2026-04-08)**

**Status**: Resolved. Tests 21, 21b, 21c, 21d now PASS. Test 21e (wrapper) tracked as Issue 7.

### Root cause

Two independent bugs in `Sparkle/Backend/CppSim.lean` were both corrupting Verilog
non-blocking (`<=`) semantics in the generated C++ `evalTick()`:

- **Bug A — `_waiting` false-positive in generic conditional-guard detection.**
  `wrapConditionalGuards` treated `_waiting` like enable signals (`_valid`/`_trigger`/
  `_enable`) and wrapped every line containing the prefix `mul_` in `if (mul_waiting) {...}`.
  That incorrectly gated the combinational wire `mul_start = pcpi_wait && !pcpi_wait_q;`,
  freezing the FSM once `mul_waiting` went to 0. Fixed by removing `_waiting` from
  `enablePatterns`: it is FSM state, not an enable gate.

- **Bug B — Self-ref register in-place optimization violated `<=` semantics.**
  The "self-ref register" optimization rewrote `reg_next` → `reg` via string replacement,
  turning non-blocking into blocking assignment. When one register's condition read a
  second self-ref register that had already been in-place written earlier in the same
  `evalTick()`, the condition saw the NEW value (e.g. `mul_waiting` blocking-assigned
  before `mul_finish`'s condition read it), so `mul_finish` never pulsed.

### Fix

1. Drop `_waiting` from `enablePatterns` in `wrapConditionalGuards`.
2. Remove the self-ref `_next` → `reg` string-replacement optimization entirely.
3. Initialize every evalTick-local `_next` to the current register value:
   `{cppType} reg_next = reg;`. This preserves `<=` semantics and lets Clang -O2
   elide redundant default stores, recovering the performance.

### Verification

Before: 28 passed / 6 failed (Tests 21, 21b, 21c, 21d, 21e, plus Test 11 stuck at
0 UART words because the CPU itself was frozen). After: 32 passed / 2 failed.
Test 11 now runs the C firmware for the full 200000 cycles (up from 0 words),
exposing a separate pre-existing UART bug tracked as Issue 6. Test 21e's first
multiply now succeeds (42 ✓); the wrapper-level 2nd-multiply failure is tracked
as Issue 7.

---

## Issue 1 (historical): pcpi_mul Standalone JIT Tests (Test 21-21e) FAIL

**Status**: Pre-existing bug, unrelated to recent reachabilityDCE / reverse synthesis changes.

**Affected tests** (`Tests/SVParser/ParserTest.lean`):
- Test 21: pcpi_mul JIT (7*6=42)
- Test 21b: pcpi_mul JIT (100*100=10000)
- Test 21c: pcpi_mul JIT (12345*6789)
- Test 21d: pcpi_mul consecutive MUL
- Test 21e: pcpi_mul SoC-like wrapper

All 28 other SVParser tests pass (Tests 1-20, 22-29). Test 11 (C firmware) SKIPs because hex files aren't present.

### Symptom

Direct JIT of PicoRV32 `picorv32_pcpi_mul` standalone module (without flattening):

```
Test 21: pcpi_mul JIT (7*6=42)... FAIL: ready=false result=0x0 expected=42 cycles=100
  cyc 0: wr=0 rd=0x0 wait=0 ready=0
  cyc 1: wr=0 rd=0x0 wait=0 ready=0
  cyc 2: wr=0 rd=0x0 wait=1 ready=0
  cyc 3: wr=0 rd=0x0 wait=1 ready=0
  ...
  cyc 99: wr=0 rd=0x0 wait=1 ready=0
```

The FSM enters `wait` state but never transitions to computing:
- `mul_waiting` stays 1 forever
- `mul_counter` doesn't decrement
- `rd` stays 0

### Why LiteX PicoRV32 works but standalone fails

- **LiteX SoC** (Test 10, LiteXTest): pcpi_mul is flattened into `picorv32` top module. Works correctly. Full LiteX firmware executes.
- **Standalone pcpi_mul** (Test 21): pcpi_mul is the top module itself, no flattening. FAILS.

This suggests the bug is in how SVParser lowers **unflattened** modules with complex always-block / for-loop structure.

### Suspicious code paths

1. **`Tools/SVParser/Lower.lean`** — `parseAndLower` (no flatten, no optimize)
   - Used directly by Test 21 via `let pcpiMulIR := parseAndLower pcpiMulVerilog`
   - `parseAndLowerFlat` (flatten + DCE + optimize) works correctly for LiteX

2. **`Tools/SVParser/Lower.lean:820-1200`** — `emitSequentialSSA` for `always @*` blocks
   - Handles nested for-loops (CARRY_CHAIN=4, 16 unrolled iterations)
   - Handles concat-LHS part-select writes (`{next_rdt[j+3], next_rd[j+:4]} = ...`)
   - Uses `__RMW_BASE__` placeholder for read-modify-write resolution

3. **`Sparkle/Backend/CppSim.lean:460-469`** — `collectTickRefWires`
   - Now includes register input refs (fixed today)
   - Previously only included memory refs → wires wrongly localized as 0-init locals

4. **`Sparkle/Backend/CppSim.lean:753-790`** — evalTick wire localization + self-ref optimization
   - Self-ref registers get `reg_next` replaced with `reg` directly
   - Default case generates `reg = reg;` (identity)

### Today's partial fixes (all merged)

1. **`inlineAssigns` infinite loop** (`Tools/SVParser/Verify.lean`): Register output names appeared as both registers AND assigns, causing infinite self-referencing expansion in `verilog!` macro. Fixed by filtering register assigns before inlining.
2. **reachabilityDCE register roots** (`Tools/SVParser/Lower.lean`): Registers are now unconditional roots in reachability DCE, preventing wire elimination when they feed FSM state.
3. **tickRefs from register inputs** (`Sparkle/Backend/CppSim.lean`): `collectTickRefWires` now includes wires referenced by register input expressions, preventing them from being localized as 0-init local variables in evalTick.
4. **Identity assign removal** (`Sparkle/IR/Optimize.lean` + `Sparkle/Backend/CppSim.lean`): Assigns of the form `x = ref x` (generated by SSA lowering of `output reg`) are now filtered before code emission.
5. **protectedWires** (`Sparkle/IR/Optimize.lean`): Wires directly referenced by register inputs are excluded from single-use inlining.

After all fixes: symptom changed from "garbage values (ready=127, wr=127)" to "FSM frozen (ready=0, never advances)". The last step (FSM frozen) is the remaining bug.

### Next steps for investigation

1. **Compare IR between standalone and LiteX flattened**
   - Does standalone pcpi_mul have all the same statements?
   - Is `mul_start` computed correctly? (`mul_start = pcpi_valid & instr_any_mul & ...`)
   - Are the wire ordering dependencies correct in the flat vs hierarchical lowering?

2. **Diff generated C++** between a working minimal counter and pcpi_mul
   - Look for wire localization that shouldn't happen
   - Check evalTick ordering (assigns before register updates?)

3. **Check `emitSequentialSSA` for edge cases**
   - Does it handle `mul_start = ...` at the top level correctly?
   - Are the SSA wire deps propagated through `always @*` properly?

---

## Issue 2: `verilog!` macro auto-assert proofs use `sorry`

**Status**: Intentional workaround for `bv_decide` compilation-mode hang.

**Location**: `Tools/SVParser/Macro.lean:92`

```lean
elabStr s!"theorem {assertName} ... := by sorry"
```

**Why**: `bv_decide` and `native_decide` work in interpreter mode (`lake env lean`) but hang indefinitely in compilation mode (`lake build`). This was observed with Lean 4.28.0-rc1.

**Impact**: Users must manually prove assertions in separate theorem files. The `verilog!` macro still provides the State/Input/nextState definitions for manual proofs.

**Workaround**: Use `lake env lean` for rapid iteration with auto-proved assertions, or write manual proofs.

---

## Issue 3: High-level multi-domain simulation — **RESOLVED (2026-04-08)**

**Status**: Resolved. A typed, auto-dispatching `runSim` function now lives
in `Sparkle/Core/SimParallel.lean` and wraps both the single-threaded
`evalTick` loop and `JIT.runCDC`. The `sim!` macro and `generateSimWrappers`
emit `outputPortIndexByName` / `inputPortIndexByName` / `toEndpoint` so that
`runSim` can resolve connections by string name.

**Usage**:
```lean
sim! "module producer (...) ..."
sim! "module consumer (...) ..."

let p ← producer.Sim.load; p.reset
let c ← consumer.Sim.load; c.reset
let stats ← runSim
  [p.toEndpoint, c.toEndpoint]
  (connections := [("data_out", "data_in")])
  (cycles := 1000000)
```

See `docs/Tutorial.md` Step 6 for full walkthrough and
`Tests/Sim/SimRunnerTest.lean` for the 27-test regression suite.

### Residual limitations (separately tracked)

**Issue 3.1 — Multi-connection between the same pair of endpoints.**
`JIT.runCDC` currently transfers one output→input pair at a time. Passing
`connections := [("a", "b"), ("c", "d")]` to `runSim` is rejected at the
Lean layer. Resolving this requires extending the C++ runtime's CDC runner
to accept arrays of `(outPort, inPort)` pairs and N SPSC queues.

**Issue 3.2 — 3+ endpoints / arbitrary topologies.** Passing more than two
endpoints to `runSim` is rejected. The current runner assumes exactly two
domains (one producer, one consumer). A topology-aware scheduler is future
work.

---

## Issue 4: `CounterProps.lean` has `sorry` in auto-generated assert theorems

**Status**: Direct consequence of Issue 2.

**Location**: `Sparkle/Verification/CounterProps.lean`

The `verilog!` macro generates:
```lean
theorem auto_assert_0 (s : State) (i : Input) : ... := by sorry
```

Users should replace these with manual proofs using `simp [nextState]` + `decide` / `bv_decide` in a separate file (via `lake env lean`).

---

## Issue 5: M-ext SoC standalone test (`MExtRv32iTest.lean`) broken

**Status**: Pre-existing bug (confirmed via `git stash` test before recent changes).

**Affected**: `Tests/SVParser/MExtRv32iTest.lean` — runs M-extension firmware on standalone PicoRV32 SoC.

**Symptom**: Firmware runs 200000 cycles with 0 UART output.

**Likely related to**: Issue 1 (standalone pcpi_mul FSM frozen). MExtRv32iTest uses a standalone SoC wrapper that instantiates pcpi_mul, which is affected by the same FSM lowering bug.

**LiteX M-extension**: Works correctly via LiteX SoC wrapper (LiteXTest).

---

## Issue 6: UART output stuck / garbage — **RESOLVED (2026-04-08)**

**Status**: Resolved. Tests 10 and 11 now PASS (Test 10 prints "Hello", Test 11
runs the full C firmware test suite — fib, sum, sort, gcd — all OK).

### Root cause

`wrapConditionalGuards` in `Sparkle/Backend/CppSim.lean` was applying an unsound
"subsystem gating" heuristic to eval body lines:

1. Detect enable-like signals (`_valid`, `_trigger`, `_enable`).
2. Find the longest shared prefix of that enable signal that appears in ≥20 lines.
3. Wrap those lines in `if (enable) { ... }` to skip computation when the
   subsystem is idle.
4. A "lookahead" kept the block open across non-matching gap lines.

The heuristic was wrong on two axes:

- **Overbroad prefix match**: For picorv32, the detected enable was
  `cpu_decoder_trigger` with prefix `cpu_`. That matched not just the decoder
  body but also the memory interface state machine
  (`cpu__reg_mem_valid_next`, `cpu__reg_mem_wstrb_next`, etc.). Those lines
  MUST run every cycle or the memory interface freezes whenever the decoder is
  between instructions. Result: the CPU never completed memory transactions,
  so the UART handler never saw `mem_valid & !mem_ready`.
- **Lookahead traps unrelated lines**: The gap-filling kept the block open
  across lines like `uart_valid = uart_valid_reg;` and
  `uart_data = uart_data_reg;`, which have nothing to do with the decoder.
  Those output-wire assignments got gated by `cpu_decoder_trigger`, so the
  UART output wire stopped reflecting the register's value.

When combined, the firmware could neither execute instructions nor observe
UART output, and the test read stale/garbage values (`0x3A3A3A3A`, `0x20202020`)
from the output port every cycle.

### Fix

Disabled `wrapConditionalGuards` entirely in `emitModule`. The eval body is
now emitted without any gating. Performance is recovered by Clang -O2's
dead-store elimination: assignments whose results are not read before the next
overwrite are removed automatically.

### Verification

- Test 10: 0 UART events → **5 UART bytes: "Hello"** (firmware is the hex-encoded
  `sb` loop that writes H, e, l, l, o to 0x10000000).
- Test 11: 0 words → **26 words, ALL C TESTS OK** (Fibonacci + sum + sort + GCD).

Total: 33 passed / 1 failed (only Test 21e — wrapper consecutive MUL — remains,
tracked as Issue 7).

### Historical observation

This optimization was originally added for I-cache locality. The intent was
reasonable but the heuristic was never correctness-safe: any line that sits
near "enable-like" code got gated by an unrelated signal. If this optimization
is ever revived, it must work from the IR (analyzing which wires genuinely
feed an enable-gated cone of logic) rather than by string pattern matching on
generated C++.

---

## Issue 6 (historical): UART output is a 4-byte replication of a single ASCII byte

**Status**: Investigating. Pre-existing bug, newly exposed after Issue 1 fix.

**Affected tests**:
- Test 10 (PicoRV32 SoC with Verilog firmware): 2000 UART bytes, all `0x20` (space)
- Test 11 (C firmware RV32I): 200000 UART words, all `0x20202020`

**Symptom**: Every UART word read via `JIT.getOutput handle 0` is the same value — a
single ASCII byte replicated across all 4 bytes of the 32-bit word
(`0x20202020` after fix, `0x3A3A3A3A` before). The firmware completes its full run
(cycle count reaches the loop limit) and `uart_valid` does pulse, but every sample
is the same.

**Diagnosis**: The byte value looks like the first byte of the firmware's `.rodata`
initialization string. Combined with the 4-way byte-replication, this smells like
the same family of bug as the historical `{4{mem_la_write}}` → 1-bit lowering bug
documented in Test 27: byte-enable (`wstrb`) not being honored, so 32-bit word
writes clobber adjacent bytes. The UART memory-mapped write path is the likely
location.

**Why newly visible**: Before the Issue 1 fix, Test 11 produced 0 UART words because
the entire CPU was frozen by the `mul_waiting` guard (even without multiplies, the
false-positive `_waiting` guard poisoned evalTick's wire computation). Now the CPU
runs the full firmware, exposing this underlying UART bug.

**Next steps**: Inspect SoC Verilog UART mmio write and compare generated C++
`wstrb` handling against Test 27's known-good fix.

---

## Issue 7: pcpi_mul SoC-like wrapper consecutive MUL (Test 21e) — **RESOLVED (2026-04-08)**

**Status**: Resolved. Test 21e now PASSes; total ParserTest score is 34/34.

### Root cause

NOT a wrapper bug. The bug was in `Sparkle/IR/Optimize.lean`'s constant-folding
rule for AND with all-ones:

```lean
| .op .and [x, .const v w] =>
  if v != 0 && v == (2 ^ w - 1 : Int) then x
```

This rule rewrites `x & all-ones-of-width-w → x`. The rewrite is sound only when
`x` itself has width `w`, but the IR Expr type does not carry per-node widths,
so the optimizer fired the rule whenever the constant happened to look like
an all-ones mask of *its own* width — regardless of `x`'s width.

In the carry-save adder of `picorv32_pcpi_mul`, the SSA lowering produces
nibble-wise masks like `(slice(rd) >> 40) & 0xF` where the slice is 64-bit
and the mask `0xF` is encoded as a 4-bit constant. Because `0xF == 2^4 - 1`,
the rewrite kicked in and dropped the mask, leaving `slice(rd) >> 40` — a
full 64-bit value — as one operand of the carry-save 4-bit add. The add then
included high bits that should have been masked off, corrupting the carry
chain and producing wrong multiplication results for any non-trivial operand.

### Why standalone (Test 21d) passed but flat-wrapped (Test 21e) failed

`Test 21d` uses `parseAndLower pcpiMulVerilog` (no optimize), so the masks
were preserved in the generated C++ (visible as `& (uint8_t)15U`).

`Test 21e` uses `parseAndLowerFlat mulWrapperVerilog`, which runs the full
optimize pipeline including `foldConstants`. Inspecting the generated C++:

- Standalone: `((next_rd_seq28 >> 40) & 0xF) + ((next_rdx_seq1 >> 40) & 0xF) + ...`
- Flat-wrapped: `(next_rd_seq28 >> 40) + (mul0_rdx >> 40) + ...`  ← masks dropped

The standalone test only happened to pass because the optimizer wasn't run,
not because pcpi_mul was correct. Test 21e exposed the latent bug because the
wrapper module forces flat optimization. The "first 7*6 PASS, second 12345*6789
FAIL" pattern was a red herring: small operands (7, 6, 100) happen to be
correct anyway because their high bits are zero, so the missing mask doesn't
matter. Larger operands like 12345 (15 bits set) overflow the unmasked nibble
add and propagate spurious carries.

### Fix

Tightened the AND-identity rule in `Sparkle/IR/Optimize.lean` to only fire
when both operands are constants (where the rewrite is unconditionally sound
because we collapse to a single constant). For the `and(non-const, all-ones)`
case, we conservatively leave the AND in place rather than risk dropping a
necessary truncation. The cost is a few extra `& 0xF...F` ops in generated
C++ that Clang -O2 would constant-fold anyway.

Note: this also explains why Test 21e was misclassified as a "wrapper FSM"
bug at first — the `0x82008ad` value looked like consecutive-state corruption
but it was actually the deterministic miscalculation of `12345 * 6789` whenever
optimization was enabled. The fix is in `Optimize.lean`, not the wrapper.

---

## Issue 7 (historical): pcpi_mul SoC-like wrapper consecutive MUL (Test 21e) 2nd result wrong

**Status**: Investigating.

Initial (incorrect) hypothesis: wrapper FSM hazard. Actual root cause is the
`Optimize.lean` mask-removal bug above.

---

## Test Status Summary (2026-04-08, post Issue 1 fix)

| Test Suite | Pass | Fail | Notes |
|-----------|------|------|-------|
| OptimizeTest | 10/10 | 0 | All IR optimizer tests |
| ParserTest | **34/34** | **0** | All tests passing |
| LiteXTest (Phase 1-3) | 3/3 | 0 | Phase 4 requires JIT FFI |
| BitNet tests | ✓ build | - | `#eval`-based, verified at build time |
| AXI4-Lite tests | ✓ build | - | `#eval`-based |
| IP builds (RV32/BitNet/YOLOv8/Arbiter/Video/Bus) | ✓ | - | All build clean |
| Proofs (MulProps/MulOracleProof/ArbiterProps/Basic) | ✓ | - | Zero sorry, zero axiom |
| CounterProps | ✓ | - | 1.4s build (was 10+min) |
| MExtRv32iTest | 0/3 | 3 | Pre-existing, related to Issue 1 |

## Verified Benchmark Results (unchanged)

| Benchmark | Sparkle JIT | Verilator | Ratio |
|-----------|------------|-----------|-------|
| LiteX 1-core | **18.1M cyc/s** | 10.5M | **1.72x** |
| LiteX + reverse synthesis | **18.1M cyc/s** | 8.4M baseline | **2.14x** |
| 8-core parallel | **12.7M per-core** | 1.1M | **11.9x** |
| Timer oracle (proof skip) | **49 GHz effective** | — | **9,900x** |
