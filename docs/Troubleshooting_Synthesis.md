# Known Limitations and Troubleshooting — Sparkle Synthesis

## Imperative Syntax NOT Supported

**The `<~` feedback operator and imperative do-notation shown in some older documentation DO NOT WORK:**

```lean
-- ❌ WRONG: This syntax doesn't exist yet!
def counter : Signal Domain (BitVec 8) := do
  let count ← Signal.register 0
  count <~ count + 1  -- ❌ The <~ operator is not implemented!
  return count

-- ❌ WRONG: This won't work either
def fir4 (coeffs : Array (BitVec 16)) (input : BitVec 16) := do
  let d1 ← Signal.register 0  -- ❌ Missing input signal argument!
  d1 <~ input                 -- ❌ <~ doesn't exist!
  ...
```

**Why these don't work:**
1. **`<~` operator**: Not defined in the codebase - this is aspirational future syntax
2. **`do`-notation for feedback**: Signal Monad doesn't support imperative assignment
3. **Runtime values**: `Array`, single `BitVec` values can't be synthesized to hardware
4. **Wrong mental model**: Signals are dataflow, not imperative assignments

**Correct approaches:**

```lean
-- For simple feedback: use let rec
def counter {dom : DomainConfig} : Signal dom (BitVec 8) :=
  let rec count := Signal.register 0#8 (count.map (· + 1))
  count

-- For feed-forward: direct dataflow
def registerChain (input : Signal Domain (BitVec 16)) : Signal Domain (BitVec 16) :=
  let d1 := Signal.register 0#16 input
  let d2 := Signal.register 0#16 d1
  d2

-- For complex feedback: manual IR construction
-- See Examples/LoopSynthesis.lean and Examples/Sparkle16/
```

**Key differences:**
- Signals are **wire streams**, not variables you assign to
- Use `Signal.register init input` with both arguments
- Coefficients/constants must be Signal inputs, not runtime values
- Operations use applicative style: `(· + ·) <$> sig1 <*> sig2`

See `test.lean` for a working FIR filter example.

---

## Pattern Matching on Tuples

**unbundle2 and pattern matching DO NOT WORK in synthesis:**

```lean
-- ❌ WRONG: This will fail with "Unbound variable" errors
def example_WRONG (input : Signal Domain (BitVec 8 × BitVec 8)) : Signal Domain (BitVec 8) :=
  let (a, b) := unbundle2 input  -- ❌ FAILS!
  (· + ·) <$> a <*> b

-- ✓ RIGHT: Use .fst and .snd projection methods
def example_RIGHT (input : Signal Domain (BitVec 8 × BitVec 8)) : Signal Domain (BitVec 8) :=
  let a := input.fst  -- ✓ Works!
  let b := input.snd  -- ✓ Works!
  (· + ·) <$> a <*> b
```

**Why this happens:**
- `unbundle2` returns a Lean-level tuple `(Signal α × Signal β)`
- Lean compiles pattern matches into intermediate forms during elaboration
- By the time synthesis runs, these patterns are compiled away
- The synthesis compiler cannot track the destructured variables

**Solution:** Use projection methods instead:
- For 2-tuples: `.fst` and `.snd`
- For 3-tuples: `.proj3_1`, `.proj3_2`, `.proj3_3`
- For 4-tuples: `.proj4_1`, `.proj4_2`, `.proj4_3`, `.proj4_4`
- For 5-8 tuples: `unbundle5` through `unbundle8` (but access via tuple projections, not pattern matching)

See [Tests/TestUnbundle2.lean](../Tests/TestUnbundle2.lean) for detailed examples.

---

## If-Then-Else in Signal Contexts

**Standard if-then-else gets compiled to match expressions and doesn't work:**

```lean
-- ❌ WRONG: if-then-else in Signal contexts
def example_WRONG (cond : Bool) (a b : Signal Domain (BitVec 8)) : Signal Domain (BitVec 8) :=
  if cond then a else b  -- ❌ Error: Cannot instantiate Decidable.rec

-- ✓ RIGHT: Use Signal.mux instead
def example_RIGHT (cond : Signal Domain Bool) (a b : Signal Domain (BitVec 8)) : Signal Domain (BitVec 8) :=
  Signal.mux cond a b  -- ✓ Works!
```

**Why this happens:**
- Lean compiles `if-then-else` into `ite` which becomes `Decidable.rec`
- The synthesis compiler cannot handle general recursors
- This is a fundamental limitation of how conditionals are compiled

**Solution:** Always use `Signal.mux` for hardware multiplexers, which generates proper Verilog.

---

## Feedback Loops (Circular Dependencies)

**Simple feedback with `let rec` works:**

```lean
-- ✓ RIGHT: Simple counter with let rec
def counter {dom : DomainConfig} : Signal dom (BitVec 8) :=
  let rec count := Signal.register 0#8 (count.map (· + 1))
  count

#synthesizeVerilog counter  -- ✓ Works!
```

**Complex feedback with multiple signals — use `Signal.loop`:**

```lean
-- ❌ WRONG: Multiple interdependent signals
def stateMachine : Signal Domain State :=
  let next := computeNext state input
  let state := Signal.register Idle next  -- ❌ Forward reference
  state

-- ✓ RIGHT: Use Signal.loop for multi-register state machines
def stateMachine (input : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  Signal.loop fun state =>
    -- state is the previous cycle's output (right-nested tuple)
    let next := computeNext state input
    next
-- See Examples/RV32/SoC.lean for a 117-register Signal.loop example
```

**Why this limitation exists:**
- Lean evaluates let-bindings sequentially (no forward references)
- `let rec` works for single self-referential definitions
- Multiple circular bindings use `Signal.loop` which provides the previous state

**Workarounds:**
- **Simple loops**: Use `let rec` (counters, single-register state)
- **Complex feedback**: Use `Signal.loop` for multi-register state machines
- See `Examples/LoopSynthesis.lean` and `Examples/RV32/SoC.lean` for working patterns

---

## Signal.loop vs Signal.loopMemo

**`Signal.loop`** uses recursive stream evaluation. For simulations beyond ~10,000 cycles,
this causes stack overflow because Lean builds a chain of thunks proportional to the cycle count.

**`Signal.loopMemo`** caches the loop output per timestep using C FFI barriers, giving O(1) lookups.
This is required for state machines that run for thousands of cycles (e.g., the RV32I SoC runs
millions of cycles for Linux boot).

**Rule of thumb:**
- Use `Signal.loop` for synthesis (Verilog generation) and short simulations (<1000 cycles)
- Use `Signal.loopMemo` for long simulations (>1000 cycles)
- Both produce identical results; `loopMemo` just avoids stack overflow

**Pattern:**

```lean
-- For synthesis: use Signal.loop
def myCircuit (input : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  Signal.loop fun state =>
    let next := computeNext state input
    next

-- For long simulation: use Signal.loopMemo
def mySimulate (input : Signal dom (BitVec 32)) : IO (Signal dom (BitVec 32)) := do
  let s ← Signal.loopMemo fun state =>
    let next := computeNext state input
    next
  return s
```

**Body extraction pattern** (share the loop body between both):

```lean
-- 1. Define the loop body as a standalone function
private def myBody (input : Signal dom (BitVec 32))
    (state : Signal dom MyState) : Signal dom MyState :=
  let prev := Signal.register initState state
  -- ... compute next state ...
  next

-- 2. Use Signal.loop for synthesis
def myCircuit (input : Signal dom (BitVec 32)) :=
  Signal.loop fun state => myBody input state

-- 3. Use Signal.loopMemo for simulation
def mySimulate (input : Signal dom (BitVec 32)) : IO ... := do
  let s ← Signal.loopMemo (myBody input)
  return ...
```

---

## What's Supported

**Fully supported in synthesis:**
- Basic arithmetic: `+`, `-`, `*`, `&&&`, `|||`, `^^^`
- Comparisons: `==`, `!=`, `<`, `<=`, `>`, `>=`
- Bitwise operations: shifts, rotations
- Signal operations: `map`, `pure`, `<*>` (applicative)
- Registers: `Signal.register`
- Mux: `Signal.mux`
- Tuples: `bundle2`/`bundle3` and `.fst`/`.snd`/`.proj*` projections
- **Arrays/Vectors**: `HWVector α n` with `.get` indexing
- **Memory primitives**: `Signal.memory` for SRAM/BRAM with synchronous read/write
- **Correct overflow**: All bit widths preserve wrap-around semantics
- Hierarchical modules: function calls generate module instantiations
- **Co-simulation**: Verilator integration for validation

**Current Limitations:**
- **No `<~` feedback operator** - Use `let rec` or `Signal.loop`
- **No imperative do-notation** - Use dataflow style with applicative operators
- **No runtime constants** - Arrays, single BitVec values can't be synthesized
- Pattern matching on Signal tuples (use `.fst`/`.snd` instead)
- Recursive let-bindings for complex feedback (use manual IR construction)
- Higher-order functions beyond `map`, `<*>`, and basic combinators
- General match expressions on Signals
- Array writes (only indexing reads supported currently)

---

## Synthesis Compiler Patterns

The `#synthesizeVerilog` compiler can only handle specific Lean expression patterns:

### Supported patterns
- **Binary ops**: `(· op ·) <$> a <*> b` — all primitives in registry + `(· ++ ·)` for concat
- **Unary map**: `(fun x => !x) <$> a`, `.map (BitVec.extractLsb' n m ·)`, `(fun x => ~~~ x) <$> a`
- **Mux**: `Signal.mux cond trueVal falseVal` (NOT if-then-else)
- **Constants**: `Signal.pure val`
- **Register**: `Signal.register initVal input`
- **Memory**: `Signal.memory writeAddr writeData writeEnable readAddr`
- **MemoryComboRead**: `Signal.memoryComboRead writeAddr writeData writeEnable readAddr`
- **Loop**: `Signal.loop fun state => ...` (nested loops become sub-modules)
- **Tuple ops**: `projN! state n i`, `bundleAll! [...]`

### NOT supported (causes "Unbound variable" errors)
- Multi-arg lambdas: `(fun a b => ...) <$> x <*> y` — only `(· op ·)` binary syntax works
- Complex single-arg lambdas: `(fun x => !(x == 0#5))` — must split into two steps
- if-then-else in map: `(fun x => if x then a else b)` — use `Signal.mux` instead
- Multi-step concat in lambda: `(fun v => (0#20 ++ v ++ 0#2))` — break into chained `(· ++ ·)`

### Fix patterns

```lean
-- BAD:  (fun x => !(x == 0#5)) <$> sig
-- GOOD: let isZero := (· == ·) <$> sig <*> Signal.pure 0#5
--       let result := (fun x => !x) <$> isZero

-- BAD:  (fun x => if x then 1#32 else 0#32) <$> sig
-- GOOD: Signal.mux sig (Signal.pure 1#32) (Signal.pure 0#32)

-- BAD:  (fun d => (0#24 ++ d : BitVec 32)) <$> sig
-- GOOD: (· ++ ·) <$> Signal.pure 0#24 <*> sig

-- BAD:  (fun v => (0#20 ++ v ++ 0#2 : BitVec 32)) <$> sig
-- GOOD: let step1 := (· ++ ·) <$> sig <*> Signal.pure 0#2
--       let step2 := (· ++ ·) <$> Signal.pure 0#20 <*> step1
```
