# Sparkle TODO

Collected post-merge ideas, ordered roughly by (impact × confidence) / effort.
This is a **wish list**, not a commitment. `docs/STATUS.md` tracks the active
phase plan; this file captures the "next up" ideas as they come up in
design discussions so they are not lost.

Each entry has:

- **Impact** ★–★★★★★
- **Effort** ★–★★★★★ (S / M / L / XL)
- **Confidence** we know how to do it (★–★★★★★)
- **Status** (idea / researched / planned / in-progress / done)
- **Depends on** any prerequisite work

---

## Verification

### V1. `lake exe verify-pr` — auto-run `#verify_eq_git` for every touched function

- Impact ★★★★★ — turns the current ad-hoc `#verify_eq_git` workflow into
  something a PR checker bot can run automatically on every open pull
  request.
- Effort M
- Confidence ★★★★☆
- Status: idea

**Idea**: a new binary that:

1. Diffs `main` vs `HEAD` (or a user-supplied base) to find touched
   `.lean` files.
2. Parses each file to enumerate top-level `def`s whose type is
   `BitVec … → BitVec …` (the v1 domain of `#verify_eq_git`).
3. For each such def, writes a temporary scratch Lean file that
   imports the current module and invokes
   `#verify_eq_git <base> <def>` at each name.
4. Runs `lake env lean scratch.lean` and aggregates
   `✅ / ❌ / skipped (type out of scope)` counts.
5. Fails the job if any ❌ is found; otherwise prints a per-function
   summary.

**Why it matters**: `#verify_eq_git` is powerful but invisible unless
someone remembers to run it. Make it automatic and the Sparkle PR
review story becomes: "CI says the refactor is bit-equivalent to
main — merge with confidence". This is the SPECIFIC UX improvement
that would change how people refactor hardware IP in this project.

**Depends on**: nothing. `#verify_eq_git` already works end-to-end.

---

### V2. Layer 3 — `Signal.loop` / feedback circuit equivalence

- Impact ★★★★☆ (narrow but deep — CPU / FSM designers absolutely need it)
- Effort L
- Confidence ★★☆☆☆ (two viable paths, neither tried)
- Status: idea

**Problem**: `Signal.loop` is `@[implemented_by loopImpl]` with an opaque
IO-backed fixed-point. `#verify_eq_at` cannot unfold it, so any
circuit that uses feedback (counters, state machines, accumulators) is
out of reach.

**Option A**: replace `opaque` with a pure recursive definition that
`simp` can unfold. Hard because the pure version may not terminate
and Lean's `partial` keyword loses evaluation semantics.

**Option B**: provide a dedicated tactic `unfold_loop n` that rewrites
`(Signal.loop f).val t` into `(f^n default).val t` for a concrete `n`,
then hand the result to `bv_decide`. This is essentially bounded
model checking. Works for finite unroll depths.

**Option C**: compile the IR to SMT (z3) and skip `bv_decide` entirely
for feedback circuits. Most heavyweight but most general.

Recommendation: prototype Option B first on a 4-bit counter.

---

### V3. `#verify_eq_at_git` — pipelined time travel

- Impact ★★★☆☆
- Effort S (if V1 and `#verify_eq_at` already exist, as they do)
- Confidence ★★★★★
- Status: idea

Combine `#verify_eq_at` and `#verify_eq_git`: prove that the pipelined
version of a circuit at `HEAD` is equivalent to the single-cycle
reference at `main` modulo latency. Useful for "I pipelined this
module in my PR; prove the reference is preserved".

API sketch:

```lean
#verify_eq_at_git main (cycles := 4) (latency := 2) macPipe macSingle
```

Essentially a combination of the two existing commands; should be
~30 lines of elaborator glue.

---

### V4. Counterexample bisect — find the commit that introduced divergence

- Impact ★★★☆☆ (rare but golden when it hits)
- Effort M
- Confidence ★★★☆☆
- Status: idea

When `#verify_eq_git main foo` returns ❌ with a concrete BitVec
counterexample, we know `foo` diverged between some commit on
`main..HEAD` and the current one. Automatically `git bisect run` the
commit range with a probe that re-evaluates the counterexample on
each commit until the first failing one is found. Reports:
`foo(a=15, b=7) first diverged at <sha>`.

---

### V5. Auto `runSim` backend selection for 3+ domains

- Impact ★★☆☆☆
- Effort L
- Confidence ★★☆☆☆
- Status: idea

Today `runSim` caps at 2 endpoints + 1 connection. The C++ CDC runner
(`JIT.runCDC`) needs to be extended to accept an array of
`(fromHandle, toHandle, outIdx, inIdx)` quadruples and an N-thread
scheduler. Once that lands, `runSim` can dispatch to it for
arbitrary DAG topologies.

Tracked in `docs/KnownIssues.md` Issue 3.2. No user has asked for it
yet, so it's parked.

---

### V6. Type-level latency annotation

- Impact ★★☆☆☆ (nice-to-have ergonomics)
- Effort M
- Confidence ★★★☆☆
- Status: idea

Let users write:

```lean
@[latency 2]
def macPipe (a b c : Signal dom (BitVec 4)) : Signal dom (BitVec 4) := ...

#verify_eq_at (cycles := 4) macPipe macSingle
-- latency := 2 is read from macPipe's attribute; no explicit arg needed
```

Makes the latency a first-class part of the module's interface
contract. Catches mismatched expectations at elab time.

---

## Simulation / runtime

### S0. RV32 Signal-DSL SoC JIT boots to PC=0 forever

- Impact ★★★★★ — blocks every end-to-end firmware-on-Signal-DSL-CPU test
- Effort M
- Confidence ★★☆☆☆ (need to diagnose)
- Status: **confirmed**, pre-existing, independent of BitNet

**Symptom**: `lake exe rv32-jit-loop-test` loads `firmware/firmware.hex`
into memory index 0 (IMEM) via `JIT.setMem`, runs `rv32iSoCJITRun` for
1000+ cycles, and every sample of `_gen_pcReg` is `0x00000000`. The CPU
never fetches a single instruction. Confirmed by `git stash`-ing the
BitNet wiring back to clean `main` HEAD — still stuck at PC=0.

**Why it matters**: `Tests/Integration/BitNetSoCTest.lean` (Level-1a
BitNet integration) would ideally run `firmware/bitnet_smoke/firmware.hex`
end-to-end through the SoC to prove the full CPU → MMIO → BitNet → CPU
loop. That path is blocked by this pre-existing regression; for now the
test checks the peripheral in isolation and the generated Verilog
structure separately.

**Suspect areas**:
- `rv32iSoCSynth`'s IMEM is `Signal.memoryComboRead` with explicit
  `imem_wr_en` / `imem_wr_addr` / `imem_wr_data` write ports. The JIT
  generated C++ maps `jit_set_mem mem_idx=0` to the backing array, but
  the combinational read path may not observe that array the way
  `setMem` expects.
- The SoC may need a specific initial reset sequence or `imem_wr_en`
  strobe that `rv32iSoCJITRun` isn't providing.
- Recent Phase-55 changes to `Sparkle/Backend/CppSim.lean`
  (`wrapConditionalGuards` removal, self-ref in-place elimination)
  might have altered memory initialization timing.

**Next step**: bisect by running `rv32-jit-loop-test` at older commits
until the failure disappears, then inspect the diff.

### S1. `runSim` selects 8-core multicore runner automatically

- Impact ★★★☆☆ (the 11.9× 8-core benchmark is already possible but
  users have to call `multicore_run` directly)
- Effort M
- Confidence ★★★★☆
- Status: idea

Currently `multicore_run` lives in `c_src/cdc/` and is invoked only
by bench scripts. Lift it behind `runSim` so that passing N copies
of the same endpoint + an explicit parallelism hint auto-selects
the lock-free multi-core runner. Preserves the "runSim picks the
fastest backend" UX contract.

---

### S2. CI benchmark regression alerts with %-delta thresholds

- Impact ★★★☆☆
- Effort S
- Confidence ★★★★★
- Status: done for 3 bench suites; could be extended

The `rv32-bench`, `litex-bench`, `multicore-bench` CI steps already
publish via `benchmark-action/github-action-benchmark`. Dashboard
exists under `gh-pages` branch. Extend thresholds per-metric and
add a weekly email digest. Low priority.

---

## Compiler / IR

### C1. Move `String.toName` / hierarchical name construction into a helper

- Impact ★☆☆☆☆
- Effort XS
- Confidence ★★★★★
- Status: idea

`#verify_eq_git` builds a hierarchical Name from a dotted string
manually (fold `Name.mkStr` over `splitOn "."`). Wrap this as a
reusable helper in `Sparkle.Verification.Equivalence` or somewhere
more generic.

---

### C2. Re-enable wstrb on the SoC mmap write path

- Impact ★★★★☆
- Effort M
- Confidence ★★★☆☆
- Status: investigating

Test 10 / 11 (pre-Issue-1-fix legacy observation): picorv32's `sb`
(store-byte) instruction emits `mem_wdata = {4{byte}}` with
`mem_wstrb = 4'b0001`. The current UART model reads the full 32-bit
`mem_wdata` and ignores `wstrb`, so the test sees `0x20202020`
("all-spaces") instead of the actual character. The LiteX SoC path
handles this correctly; the standalone SoC model doesn't.

Not blocking any active feature; the CI firmware tests already pass
because both Test 10 and Test 11 accept the "1 char repeated"
output as a smoke signal. Worth fixing for newcomers writing their
own SoC bring-up tests.

---

### C3. Eliminate the remaining `String.trimLeft` / `dropRight` deprecations

- Impact ★☆☆☆☆
- Effort XS
- Confidence ★★★★★
- Status: idea

`CppSim.lean` and a few other files still trigger deprecation
warnings on `String.trimLeft`, `String.dropRight`, `String.get`.
Straightforward find-and-replace to `trimAsciiStart`, `dropEnd`,
`String.Pos.Raw.get`.

---

## Docs / UX

### D1. Short "recipe" page for common verification patterns

- Impact ★★★☆☆
- Effort S
- Confidence ★★★★★
- Status: idea

A new `docs/VerificationRecipes.md` that shows, for each common
design task, the minimal `#verify_eq` / `_at` / `_git` invocation:

- "I refactored my ALU" → `#verify_eq old new`
- "I pipelined my multiplier" → `#verify_eq_at (cycles := N) (latency := L) impl spec`
- "I need to prove my PR doesn't regress `foo`" → `#verify_eq_git main foo`
- "I'm bisecting a bug" → `#verify_eq_git HEAD~{1..10}` sweep
- "I want latency auto-inference" → use the ❌/💡 hint path

Cross-link from the Tutorial.

---

### D2. Troubleshooting table for `bv_decide` timeouts

- Impact ★★☆☆☆
- Effort XS
- Confidence ★★★★★
- Status: idea

When `bv_decide` times out, the user currently sees only the
terse "SAT solver timed out" message. Add a table to
`KnownIssues.md` listing common causes (wide multiplies,
deep MUX chains, too many forall-quantified inputs) and the
corresponding workarounds (reduce BitVec width, split the
function, try `native_decide` as a last resort).
