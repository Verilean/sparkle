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

## Issue 3: `sim_parallel!` macro not implemented

**Status**: Planned (TODO in `docs/STATUS.md` Phase 5.6).

**Current state**: Multi-domain simulation uses low-level `JIT.runCDC handle1 handle2 cycles outPort inPort`:
- Ports are indexed (not type-safe)
- Only 2 domains supported
- No integration with `sim!` / `#sim` macros

**Desired state**:
```lean
sim! "module producer (...) ..."
sim! "module consumer (...) ..."

let result ← simParallel
  (producer := producer.Sim)
  (consumer := consumer.Sim)
  (connections := [("data_out", "data_in")])
  (cycles := 1000000)
```

See `docs/Tutorial.md` Step 6 for current API documentation.

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

## Issue 6: UART output is a 4-byte replication of a single ASCII byte

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

## Issue 7: pcpi_mul SoC-like wrapper consecutive MUL (Test 21e) 2nd result wrong

**Status**: Investigating.

**Affected test**: Test 21e (`mul_wrapper` driving `picorv32_pcpi_mul`).

**Symptom**: First multiply `7*6` returns `0x2a = 42` ✓. Second multiply `12345*6789`
returns `0x82008ad` instead of expected `0x4fe4a1d = 83810205`.

**Diagnosis**: `pcpi_mul` standalone consecutive multiply (Test 21d, 7*6 then
12345*6789) PASSes, so the core is fine. The bug is wrapper-specific — likely the
`mul_wrapper` state machine (`pcpi_valid_r` / `done_r` / `result_r`) doesn't fully
clear between transactions, so the 2nd `start` latches partial state from the
1st multiply.

**Wrapper Verilog** (`Tests/SVParser/ParserTest.lean` Test 21e): drives `pcpi_valid_r`
on `start && !pcpi_wait`, deasserts on `pcpi_valid_r && pcpi_ready`. Suspect a
single-cycle window where the deassert and next assert race.

---

## Test Status Summary (2026-04-08, post Issue 1 fix)

| Test Suite | Pass | Fail | Notes |
|-----------|------|------|-------|
| OptimizeTest | 10/10 | 0 | All IR optimizer tests |
| ParserTest | 32/34 | 2 | Test 11 (UART wstrb bug — Issue 6), Test 21e (wrapper 2nd MUL — Issue 7) |
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
