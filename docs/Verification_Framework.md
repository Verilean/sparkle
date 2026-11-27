# Verification-Driven Design Framework

A guide to proving hardware properties alongside implementation in Sparkle.

---

## 1. Why Verify Hardware?

Traditional hardware verification relies on simulation: run millions of test
vectors and hope to hit corner cases.  Formal verification proves properties
hold for **all** inputs and **all** reachable states — no simulation gaps.

Sparkle embeds hardware design in Lean 4, giving us access to its dependent
type system and tactic prover.  This means we can:

- Define a pure state-machine **spec** (no Signal DSL, no synthesis)
- Prove safety/liveness/fairness on the spec
- Implement the spec in synthesizable Signal DSL
- (Optionally) prove refinement: implementation ≈ spec

---

## 2. Bug Classification

### Safety — "bad things never happen"

| Property | Example | Hardware Impact |
|----------|---------|-----------------|
| Mutual exclusion | Two masters granted bus simultaneously | Data corruption |
| No buffer overflow | FIFO write when full | Silent data loss |
| Protocol compliance | AXI handshake rules | Deadlock / hang |
| Memory safety | Out-of-bounds address decode | Bus error |

### Liveness — "good things eventually happen"

| Property | Example | Hardware Impact |
|----------|---------|-----------------|
| Starvation-freedom | Low-priority master never served | Pipeline hang |
| Responsiveness | Cache miss resolved in bounded cycles | Performance bug |
| Deadlock-freedom | Circular lock dependency | System hang |
| Progress | Pipeline always retires instructions | Silent stall |

---

## 3. Efficiency / Performance Bounds

Beyond safety ("bad things never happen") and liveness ("good things eventually
happen"), hardware designs must also satisfy **efficiency** properties — proving
the design is "not bad" (doesn't waste cycles, guarantees strict timing bounds,
uses no more resources than necessary).

### Bounded Latency (Bounded Wait)

> **Template**: `¬granted(t) → granted(t+1)`

Upgrades "eventually responds" to "responds within strictly K cycles."
While liveness says a client is *eventually* served, bounded latency proves a
**hard real-time guarantee**: the worst-case wait is exactly K cycles.

**Hardware motivation**: Real-time bus arbiters, interrupt controllers, and
pipeline hazard units must guarantee bounded response times.  An arbiter that
"eventually" grants access is useless if the bound is unbounded — bounded
latency closes this gap.

**Sparkle example** — Arbiter bounded wait (K=1):

```lean
-- ArbiterProps.lean
theorem bounded_wait_A (s : ArbiterState) (reqB reqB' : Bool) :
    ¬grantA (nextState s true reqB) →
    grantA (nextState (nextState s true reqB) true reqB') := by
  cases s <;> cases reqB <;> cases reqB' <;> simp [nextState, grantA, grantB]
```

If A requests but is not granted this cycle, A **will** be granted next cycle —
regardless of what B does.

### Work-Conserving

> **Template**: `(reqA ∨ reqB) → (grantA ∨ grantB)`

Proves the arbiter never wastes a clock cycle when work is pending.  If at
least one client has a pending request, at least one grant is issued.  Zero
idle cycles under load.

**Hardware motivation**: A non-work-conserving arbiter can leave the bus idle
while requests are queued, wasting bandwidth.  This property guarantees 100%
utilization under load — critical for high-throughput interconnects.

**Sparkle example** — Arbiter work-conserving:

```lean
-- ArbiterProps.lean
theorem work_conserving (s : ArbiterState) (reqA reqB : Bool) :
    (reqA ∨ reqB) →
    (grantA (nextState s reqA reqB) ∨ grantB (nextState s reqA reqB)) := by
  cases s <;> cases reqA <;> cases reqB <;> simp [nextState, grantA, grantB]
```

### Resource Optimality (Bounded Resource)

> **Template**: `∀ reachable s, bufferSize(s) ≤ N`

Proves a queue or buffer never exceeds N elements under defined constraints.
This ensures hardware is not over-provisioned — the allocated area is
exactly what is needed, no more.

**Hardware motivation**: FIFO depths, register file entries, and TLB slots
are expensive in silicon area.  Proving a bound of N means the designer can
allocate exactly N entries without risk of overflow, saving area without
sacrificing correctness.

**Sparkle example** — This pattern applies to FIFO-based designs.  For the
arbiter (which is stateless w.r.t. buffering), the analogous property is that
the FSM has exactly 3 reachable states — no hidden state bloat.

---

## 4. Four Proof Patterns

### Pattern 1: Invariant Proof

> **Template**: `∀ reachable state s, Property(s)`

Proves a property holds in every reachable state.  The key technique is
**induction on the transition function**: show the property holds initially,
then show that if it holds in state `s`, it holds in `nextState s inputs`.

**Sparkle example** — Arbiter mutual exclusion:

```lean
-- ArbiterProps.lean
theorem mutual_exclusion (s : ArbiterState) (reqA reqB : Bool) :
    ¬(grantA (nextState s reqA reqB) ∧ grantB (nextState s reqA reqB)) := by
  cases s <;> cases reqA <;> cases reqB <;> simp [nextState, grantA, grantB]
```

**Tactic**: Enumerate all (state × input) combinations with `cases`, then
let `simp` discharge each obligation.

### Pattern 2: Round-trip / Encode-Decode

> **Template**: `decode(encode(x)) = x`

Proves an encoding is lossless.  Used for ISA encode/decode, protocol
serialization, bus transaction packing.

**Sparkle example** — ISA opcode round-trip:

```lean
-- ISAProps.lean
theorem opcode_encode_decode (opc : Opcode) :
    Opcode.fromBitVec (Opcode.toBitVec opc) = some opc := by
  cases opc <;> rfl
```

**Tactic**: `cases` on the datatype, `rfl` when both sides reduce.

### Pattern 3: Responsiveness (Bounded Liveness)

> **Template**: `request(t) → grant(t') ∧ t' - t ≤ bound`

Proves that a request is served within a bounded number of cycles.
For finite-state machines, this reduces to showing the property holds
within `k` applications of `nextState`.

**Sparkle example** — Arbiter starvation-freedom:

```lean
-- ArbiterProps.lean
theorem starvation_free_A (s : ArbiterState) (reqB : Bool) :
    grantA (nextState s true reqB) ∨
    grantA (nextState (nextState s true reqB) true reqB) := by
  cases s <;> cases reqB <;> simp [nextState, grantA]
```

**Tactic**: Unfold `nextState` for 1–2 steps, enumerate states.

### Pattern 4: Refinement

> **Template**: `output(impl(x)) = output(spec(x))`

Proves the synthesizable implementation matches the specification.
The spec is a pure function; the impl uses Signal DSL.

**Sparkle example** — ALU correctness:

```lean
-- ALUProps.lean
theorem add_correct (a b : BitVec 32) :
    aluCompute .Add a b = a + b := by rfl
```

**Tactic**: `rfl` when implementation directly computes the spec,
or `simp` with unfolding for more complex cases.

---

## 5. Sparkle Verification Infrastructure

### File Organization

```
Sparkle/Verification/
  Basic.lean          -- Foundation: reachability, traces
  Temporal.lean       -- LTL-style temporal operators
  ISAProps.lean       -- ISA encode/decode proofs
  ALUProps.lean       -- ALU correctness
  ArbiterProps.lean   -- Arbiter safety/liveness/fairness
```

Each file is **self-contained**: it defines its own types and functions,
then proves properties.  No cross-file dependencies within Verification/.

### Naming Convention

- `*Props.lean` — Properties and proofs for a specific module
- Types are defined locally (not imported from the DSL implementation)
- Proofs are grouped by category: Safety, Liveness, Fairness

---

## 6. Worked Example: Round-Robin Arbiter

### Specification (`Sparkle/Verification/ArbiterProps.lean`)

A 2-client round-robin arbiter with three states:

```
     reqA ∧ ¬reqB     reqA ∧ reqB
  ┌──────────────┐   ┌──────────┐
  │              ▼   ▼          │
  │           GrantA ──────► GrantB
  │              │              │
  │   ¬reqA ∧    │  ¬reqA ∧    │
  │   ¬reqB      │  ¬reqB      │
  │              ▼              │
  │            Idle             │
  │              │              │
  └──────────────┘              │
  reqB ∧ ¬reqA                  │
         ◄──────────────────────┘
```

### Proven Properties

| # | Theorem | Category | Statement |
|---|---------|----------|-----------|
| 1 | `mutual_exclusion` | Safety | Never both granted after transition |
| 2 | `mutual_exclusion_current` | Safety | Never both granted in any state |
| 3 | `no_spurious_grant` | Safety | No grant without request |
| 4 | `progress_A` | Liveness | A requesting → A granted or B holds |
| 5 | `progress_B` | Liveness | B requesting → B granted or A holds |
| 6 | `starvation_free_A` | Liveness | A granted within 2 cycles |
| 7 | `starvation_free_B` | Liveness | B granted within 2 cycles |
| 8 | `round_robin_A_to_B` | Fairness | GrantA + contention → GrantB |
| 9 | `round_robin_B_to_A` | Fairness | GrantB + contention → GrantA |
| 10 | `idle_tiebreak` | Fairness | Idle + contention → GrantA |
| 11 | `work_conserving` | Efficiency | Request pending → grant issued |
| 12 | `bounded_wait_A` | Efficiency | A not granted → A granted next cycle |
| 13 | `bounded_wait_B` | Efficiency | B not granted → B granted next cycle |

All 13 theorems close via:
```lean
cases s <;> cases reqA <;> cases reqB <;> simp [nextState, grantA, grantB]
```

### Implementation (`Examples/Arbiter/RoundRobin.lean`)

The Signal DSL implementation encodes the same FSM using `BitVec 2`:
- `0#2` = Idle, `1#2` = GrantA, `2#2` = GrantB
- Uses `Signal.loop` + `Signal.register` for state feedback
- Uses `hw_cond` for next-state priority mux
- Verified with `#synthesizeVerilog` (compiles to SystemVerilog)

---

## 7. Tactic Quick-Reference

| Tactic | Use Case | Example |
|--------|----------|---------|
| `cases x` | Enumerate constructors of `x` | `cases s` for 3 arbiter states |
| `<;> tac` | Apply `tac` to all goals | `cases s <;> simp` |
| `simp [f, g]` | Simplify with definitions | `simp [nextState, grantA]` |
| `rfl` | Both sides are definitionally equal | `nextState Idle true true = GrantA` |
| `omega` | Linear arithmetic over `Nat`/`Int` | Bound checks |
| `decide` | Decidable propositions (small) | `(3 : Fin 8) ≠ 5` |
| `contradiction` | Close impossible goals | After `cases` eliminates branches |
| `constructor` | Split `∧` or build `∃` | `⟨left_proof, right_proof⟩` |
| `left` / `right` | Choose `∨` disjunct | `left; exact h` |

### Common Proof Skeleton for Hardware FSMs

```lean
theorem my_property (s : MyState) (input : Bool) :
    SomeProperty (nextState s input) := by
  -- 1. Enumerate all states
  cases s
  -- 2. For each state, enumerate all inputs
  all_goals cases input
  -- 3. Simplify each (state, input) case
  all_goals simp [nextState, outputFn]
```

For `n` states and `m` boolean inputs, this generates `n × 2^m` goals,
each discharged by `simp`.

---

## 8. Getting Started

1. **Define a pure state machine** in `Sparkle/Verification/MyModuleProps.lean`
   - Inductive type for states
   - `nextState` transition function
   - Output functions

2. **Prove properties** using the patterns above

3. **Implement in Signal DSL** in `Examples/MyModule/`
   - Encode states as `BitVec`
   - Mirror the transition table with `hw_cond`
   - Verify synthesis with `#synthesizeVerilog`

4. **Build and verify**:
   ```bash
   lake build Sparkle.Verification.MyModuleProps  # proofs compile = QED
   lake build Examples.MyModule                    # synthesis works
   ```
