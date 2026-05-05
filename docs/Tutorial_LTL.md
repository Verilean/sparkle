# Sparkle Tutorial — LTL (Temporal Logic)

A walkthrough of **temporal-logic verification** in Sparkle:
how to state ∀N-quantified properties as Lean theorems, prove them
from per-cycle recurrences, and use them to localize runtime bugs
to specific layers of a SoC.

This tutorial is the natural follow-up to `docs/Tutorial_Extended.md`
(module composition + named record I/O). It uses the same project
structure (`tutorial-extended/TutorialExtended/Step{5,6,7}_*.lean`).

All code in this tutorial **builds and runs**:

```bash
lake build TutorialExtended
lake exe tutorial-extended-run
```

---

## 1. Why LTL works in Sparkle for free

A Sparkle Signal is `Signal dom α = { val : Nat → α }`. Every
property over a `Signal dom α` is a function from cycles to a
predicate, so:

| LTL operator | In Lean | Meaning |
|--------------|---------|---------|
| `□ P`        | `∀ t, P t` | always |
| `P → ◯ Q`    | `∀ t, P t → Q (t+1)` | next |
| `P → ◯^k Q`  | `∀ t, P t → Q (t+k)` | next-K |
| `□ (P → ◯ Q)` | `∀ t, P t → Q (t+1)` | always-implies-next |
| `P U Q`      | (case-split: `∃ k ≤ K, ...`) | bounded until |

**No new logic is needed.** Lean's `∀` quantifier IS LTL's `□`,
applied to the cycle-index argument of `.val`.

This is what made the BitNet bug-localization investigation
possible — see `docs/BitNet_LTL_Investigation.md` for a worked
case study.

---

## Step 5: LTL basics — invariants and K-cycle preservation

File: `tutorial-extended/TutorialExtended/Step5_LTL_Basics.lean`.

We use a **saturating up-counter** as the example: counts +1 on
each enable, but stops at `0xFF`.

### 5.1 The pure spec

```lean
def satCounterNextPure (en : Bool) (curr : BitVec 8) : BitVec 8 :=
  if en then
    if curr == 0xFF#8 then 0xFF#8
    else curr + 1#8
  else
    curr
```

### 5.2 Single-cycle invariants (□ P)

```lean
-- "Globally, the counter is bounded by 0xFF."
theorem satCounterNext_bounded :
    ∀ (en : Bool) (curr : BitVec 8),
      satCounterNextPure en curr ≤ 0xFF#8 := by
  intro en curr
  unfold satCounterNextPure
  cases en <;> bv_decide
```

The pure version is decidable for all 2 ⨯ 256 = 512 inputs, so
`bv_decide` closes it after splitting on `en`.

### 5.3 Cycle-N+1 properties (P → ◯ Q)

```lean
-- "Globally, en=false → count unchanged in the next cycle."
theorem satCounterNext_disabled :
    ∀ (curr : BitVec 8),
      satCounterNextPure false curr = curr := by
  intro curr; rfl

-- "Globally, count = 0xFF → count stays 0xFF (saturation)."
theorem satCounterNext_saturated :
    ∀ (en : Bool),
      satCounterNextPure en 0xFF#8 = 0xFF#8 := by
  intro en; cases en <;> rfl
```

### 5.4 K-cycle preservation (P → ◯^k Q) — induction on K

```lean
theorem satCounter_preserved_K_cycles_disabled {dom : DomainConfig}
    (regSig : Signal dom (BitVec 8))
    (en : Signal dom Bool)
    (h_recurrence :
      ∀ s, regSig.val (s + 1) =
        satCounterNextPure (en.val s) (regSig.val s)) :
    ∀ (t k : Nat),
      (∀ i, i < k → en.val (t + i) = false) →
      regSig.val (t + k) = regSig.val t := by
  intro t k
  induction k with
  | zero => intro _; show regSig.val (t + 0) = regSig.val t; simp
  | succ k ih =>
    intro h_no_en
    -- ... step from t+k to t+(k+1), reuse IH ...
```

This is the canonical K-step induction. The hypothesis
`h_recurrence` says "the register satisfies the canonical
if-then-else recurrence" — the caller wires the `Signal.register`
self-loop and proves this once, then K-step preservation comes
for free.

The `IP/RV32/Verification/InductionScaffold.lean` file generalizes
this pattern: `nstep_preserve_when_no_event` is α-generic and
ready to apply to any single-event register.

---

## Step 6: bug-localization framework (multi-premise + contrapositive)

File: `tutorial-extended/TutorialExtended/Step6_LTL_BugLocalization.lean`.

### 6.1 The 3-layer write→hold→read contract

For a memory-like register, define one premise per layer:

```lean
-- P1: write at t commits at t+1.
def writeCommitsContract {dom : DomainConfig}
    (writeEn : Signal dom Bool) (data reg : Signal dom (BitVec 8)) : Prop :=
  ∀ t, writeEn.val t = true → reg.val (t + 1) = data.val t

-- P2: no-write preserves the register.
def noWritePreservesContract {dom : DomainConfig}
    (writeEn : Signal dom Bool) (reg : Signal dom (BitVec 8)) : Prop :=
  ∀ t, writeEn.val t = false → reg.val (t + 1) = reg.val t

-- P3: read returns the current register value.
def readObservesContract {dom : DomainConfig}
    (readReady : Signal dom Bool) (reg observed : Signal dom (BitVec 8)) : Prop :=
  ∀ t, readReady.val t = true → observed.val t = reg.val t
```

### 6.2 The composite "everything works" theorem

```lean
theorem write_then_read_returns_data
    (h_p1 : writeCommitsContract writeEn data reg)
    (h_p2 : noWritePreservesContract writeEn reg)
    (h_p3 : readObservesContract readReady reg observed)
    (T K : Nat)
    (h_we : writeEn.val T = true)
    (h_no_we : ∀ i, i < K → writeEn.val (T + 1 + i) = false)
    (h_rr : readReady.val (T + 1 + K) = true) :
    observed.val (T + 1 + K) = data.val T := by
  -- 3-step proof: P1 → reg.val (T+1) = data.val T,
  -- then K-cycle preservation via P2,
  -- then P3 reads the current reg.
  ...
```

### 6.3 The contrapositive — bug-localization theorem

```lean
theorem bug_localization
    (T K : Nat) (Y : BitVec 8)
    (h_we : writeEn.val T = true)
    (h_no_we : ∀ i, i < K → writeEn.val (T + 1 + i) = false)
    (h_rr : readReady.val (T + 1 + K) = true)
    (h_obs : observed.val (T + 1 + K) = Y)
    (h_neq : Y ≠ data.val T) :
    ¬ (writeCommitsContract writeEn data reg ∧
       noWritePreservesContract writeEn reg ∧
       readObservesContract readReady reg observed) := by
  rintro ⟨h_p1, h_p2, h_p3⟩
  apply h_neq
  rw [← h_obs]
  exact write_then_read_returns_data ... h_p1 h_p2 h_p3 ...
```

This is the punchline: **observed value ≠ expected ⇒ at least one
premise is false in the runtime trace.**

### 6.4 Localizing to a specific layer

The composite says "at least one Pi failed" but doesn't say
which. To localize, falsify each Pi separately:

```lean
theorem P1_violation_witness
    (h_we : writeEn.val t = true)
    (h_neq : reg.val (t + 1) ≠ data.val t) :
    ¬ writeCommitsContract writeEn data reg
```

A runtime debugger that observes `(writeEn.val 5, reg.val 6, data.val 5)`
can decide which premise to violate. Combined with
`bug_localization`, this gives a 3-way classification:

  - reg.val 6 ≠ data.val 5 ⇒ P1 broken (write didn't commit)
  - reg.val (T+1+K) ≠ reg.val (T+1) ⇒ P2 broken (corruption)
  - observed.val (T+1+K) ≠ reg.val (T+1+K) ⇒ P3 broken (read-side)

---

## Step 7: production scale — the RV32 LTL catalog

File: `tutorial-extended/TutorialExtended/Step7_LTL_RV32_Pointers.lean`.

The same patterns scale up to the RV32 SoC verification. The
production catalog has:

### 7.1 Cycle-N+1 LTL forms (~100 theorems)

For every state-bearing register, a theorem of the form
`∀ t, P t → reg.val (t+1) = ...`. Example:

```lean
#check @Sparkle.IP.RV32.Pipeline.trap_clears_exwb_regW_LTL
-- ∀ {dom} (trap_taken … idex_regWrite : Signal dom Bool),
--   ∀ t, trap_taken.atTime t = true →
--        (Signal.register false ... idex_regWrite).val (t + 1) = false
```

Locations: `IP/RV32/Pipeline/SideEffectsTrapInv.lean`,
`IP/RV32/Pipeline/FlushSquash.lean`,
`IP/RV32/Pipeline/IDEXRegInput.lean`,
`IP/RV32/CSR/Commit.lean`, `IP/RV32/MMU/Fill.lean`, etc.

### 7.2 N-step register preservation scaffold

`IP/RV32/Verification/InductionScaffold.lean` generalizes Step 5's
K-cycle preservation to α-generic and supports multi-event
registers (mstatus 5-way, AMO reservation 3-way, etc.):

```lean
#check @Sparkle.IP.RV32.Verification.nstep_preserve_when_no_event
-- ∀ {α} (r : Nat → α) (we : Nat → Bool) (update : Nat → α),
--   (∀ s, r (s + 1) = if we s then update s else r s) →
--   ∀ t k, (∀ i, i < k → we (t + i) = false) →
--          r (t + k) = r t
```

### 7.3 Multi-premise composite — BitNet sw→lw

`IP/RV32/Verification/BitNetTimingLTL.lean` is the production
analog of Step 6, scaled to 4 premises:

```lean
#check @Sparkle.IP.RV32.Verification.sw_then_lw_observes_ffn_input
-- 4-premise composite: P1 (cycle-N+1 update) ∧ P2 (K-cycle preservation)
-- ∧ P3 (combinational FFN) ∧ P4 (lw decode)
-- ⇒ lw observation = ffn(input)

#check @Sparkle.IP.RV32.Verification.bug_localization_via_LTL
-- contrapositive — observed Y ≠ ffn(X) ⇒ ¬(P1 ∧ P2 ∧ P3 ∧ P4)
```

This was used to localize the BitNet "out = input" symptom from
commit `9d0704e`. The full investigation (and the lessons learned)
are in `docs/BitNet_LTL_Investigation.md`. **Outcome**: all 4
premises HOLD in the runtime once the relevant wires are
exposed via `SoCOutput.wireNames`. The original symptom was a
probe-side observation artifact, not a Sparkle bug.

### 7.4 Concrete-vector regression theorems

For ground-truth pinning of specific bug fixes, `decide`-closed
concrete-vector theorems serve as machine-checked alarms:

```lean
#check @Sparkle.IP.RV32.MMU.dPhysAddrMega_kernel_first_fetch_concrete
-- dPhysAddrPure true 0x080400#22 0xc0000098#32 = 0x80400098#32
```

These pin the exact behavior at specific input vectors. Used
heavily in `IP/RV32/Verification/LinuxBootRegression.lean` (28
theorems covering the bf6d873 megapage PA fix, the 5a3fdfb
C-extension/DTB fixes, and bus-decoder routing for all
Linux-critical PAs).

### 7.5 Layered architecture

```
   concrete-vector regression theorems      (decide-closed)
                  ↓
       cycle-N+1 LTL forms (~100)            (unfold + cases + rfl)
                  ↓
      N-step preservation scaffold           (induction on K)
                  ↓
   composite contracts (e.g., 4-premise)     (compose smaller LTLs)
                  ↓
   contrapositive bug localization           (apply contrapositive)
```

Each layer takes the layer below as discharged premises. The user
only writes the TOP layer for the property they want; everything
below is reusable infrastructure.

---

## Recap: when to use each pattern

| Want to prove | Pattern | Closed by |
|---------------|---------|-----------|
| `∀ inputs, F(inputs) = expected` | pure-spec lemma | `decide` / `bv_decide` / `rfl` |
| `∀ t, P (signal.val t)` | global invariant | induction or unfold per `Signal.register` |
| `∀ t, P t → Q (t+1)` | cycle-N+1 LTL form | `Signal.register` + `Signal.mux` semantics + `cases` |
| `∀ t k, no-event in [t,t+k) → preserved` | K-cycle preservation | induction on K, IH + recurrence |
| `runtime obs ≠ expected ⇒ bug` | composite + contrapositive | compose LTLs, apply by `rintro` + `rw` |
| `at cycle 80, observation = X` | concrete-vector regression | `decide` / `bv_decide` |

---

## Cross-references

  - `tutorial-extended/TutorialExtended/Step5_LTL_Basics.lean` —
    saturating counter, single-cycle invariants, K-step preservation.
  - `tutorial-extended/TutorialExtended/Step6_LTL_BugLocalization.lean` —
    write→hold→read with composite + contrapositive + localization
    witnesses for each layer.
  - `tutorial-extended/TutorialExtended/Step7_LTL_RV32_Pointers.lean` —
    pointers to the production RV32 LTL theorem catalog.
  - `IP/RV32/Verification/InductionScaffold.lean` — α-generic
    N-step preservation primitives.
  - `IP/RV32/Verification/BitNetTimingLTL.lean` — 4-premise BitNet
    sw→lw framework (production analog of Step 6).
  - `IP/RV32/Verification/LinuxBootRegression.lean` — 28
    concrete-vector regression-pinning theorems for Linux boot.
  - `docs/BitNet_LTL_Investigation.md` — full debugging postmortem
    where the LTL framework was applied to a real symptom.
  - `docs/RV32_Architecture_Status.md` §2.2 — broader catalog of
    sequential invariants A-E and the multi-cycle composites.
  - `docs/Verification_Framework.md` — the layer above this
    tutorial: how Sparkle composes formal verification primitives
    (oracle reduction, bv_decide, simp normalization).
