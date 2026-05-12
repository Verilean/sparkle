
# Chapter 6 — Proofs: LTL Invariants

Sparkle's `Signal dom α` is **literally** `Nat → α` — a
function from cycle index to value.  That means a temporal
property like "globally, count is at most 0xFF" is just a
Lean ∀-statement: `∀ t, count.val t ≤ 0xFF`.

We don't need a separate temporal-logic library.  All of LTL's
core operators map onto plain Lean quantification:

| LTL                | Lean equivalent                        |
|--------------------|----------------------------------------|
| □ P  (always)      | `∀ t, P t`                             |
| ◯ P  (next)        | `λ t => P (t + 1)`                     |
| P → ◯ Q            | `∀ t, P t → Q (t + 1)`                 |
| □^k (always next k)| `∀ t, P t → Q (t + k)`                 |

This chapter walks through three proof patterns:

1. **Pure-spec invariant** — prove a property of the
   next-state function in isolation.  No `Signal` involved;
   closed by `bv_decide`, `decide`, or case analysis.
2. **K-cycle preservation** — extend a single-cycle property
   over `k` cycles by induction on `k`.
3. **Saturation** — prove a stuck-state property
   (once we reach a state, we stay there).

The running example is a **saturating up-counter**: increments
on enable, stops at `0xFF`.

```lean
import Sparkle

open Sparkle.Core.Domain
open Sparkle.Core.Signal

namespace Notebooks.Ch06

```
## 6.1 The design — saturating up-counter

We define both a **pure-spec next-state** (operates on plain
`BitVec`) and a **Signal-level wrapper** (operates on
`Signal dom (BitVec 8)`).  Pure spec is what we prove
properties about; Signal version is what we'd actually
synthesise.

```lean
/-- Pure spec: next value of the counter. -/
def satNextPure (en : Bool) (curr : BitVec 8) : BitVec 8 :=
  if en then
    if curr == 0xFF#8 then 0xFF#8
    else curr + 1#8
  else
    curr

```
## 6.2 Property #1 — bounded

"Globally, the counter is at most `0xFF`" — `□ (count ≤ 0xFF)`.
For a `BitVec 8` value this is a tautology (trivially every
8-bit value is at most `0xFF`), but the proof structure
generalises to non-trivial bounds.

```lean
theorem satNext_bounded :
    ∀ (en : Bool) (curr : BitVec 8),
      satNextPure en curr ≤ 0xFF#8 := by
  intro en curr
  unfold satNextPure
  cases en <;> bv_decide

```
## 6.3 Property #2 — disabled means unchanged

"If `en` is false, the counter doesn't change."  This is a
single-cycle property — prove it for the next-state function,
and the K-cycle version (Property #5) follows by induction.

```lean
theorem satNext_disabled :
    ∀ (curr : BitVec 8),
      satNextPure false curr = curr := by
  intro _
  rfl

```
## 6.4 Property #3 — saturation is sticky

"If the counter is at `0xFF`, after one cycle it's still at
`0xFF`, regardless of `en`."

```lean
theorem satNext_saturated :
    ∀ (en : Bool),
      satNextPure en 0xFF#8 = 0xFF#8 := by
  intro en
  cases en <;> rfl

```
## 6.5 Property #4 — K-cycle preservation under disable

"If `en` is false for `k` consecutive cycles, the counter's
value is unchanged after `k` cycles."  This is the LTL
formula `□^k (¬en in [t, t+k) → count(t+k) = count(t))`.

The proof is **induction on k** plus the recurrence
hypothesis (the register's defining equation).  The pattern
generalises: any single-cycle property + recurrence + induction
→ K-cycle property.

```lean
theorem satCounter_preserved_K_cycles_disabled {dom : DomainConfig}
    (regSig : Signal dom (BitVec 8))
    (en : Signal dom Bool)
    (h_recurrence :
      ∀ s, regSig.val (s + 1) =
        satNextPure (en.val s) (regSig.val s)) :
    ∀ (t k : Nat),
      (∀ i, i < k → en.val (t + i) = false) →
      regSig.val (t + k) = regSig.val t := by
  intro t k
  induction k with
  | zero =>
    intro _
    show regSig.val (t + 0) = regSig.val t
    simp
  | succ k ih =>
    intro h_no_en
    -- Step from t+k to t+(k+1) using the recurrence + disabled at cycle (t+k).
    have h_no_en_k : en.val (t + k) = false :=
      h_no_en k (Nat.lt_succ_self k)
    have h_ih : regSig.val (t + k) = regSig.val t := by
      apply ih
      intro i hi
      exact h_no_en i (Nat.lt_succ_of_lt hi)
    have : t + (k + 1) = (t + k) + 1 := by omega
    rw [this, h_recurrence (t + k), h_no_en_k]
    show satNextPure false (regSig.val (t + k)) = regSig.val t
    rw [satNext_disabled]
    exact h_ih

```
## 6.6 Property #5 — stuck at saturation

"Once the counter is at `0xFF`, it stays at `0xFF` forever
(for any number of cycles `k`, regardless of `en`)."

```lean
theorem satCounter_stuck_at_FF {dom : DomainConfig}
    (regSig : Signal dom (BitVec 8))
    (en : Signal dom Bool)
    (h_recurrence :
      ∀ s, regSig.val (s + 1) =
        satNextPure (en.val s) (regSig.val s)) :
    ∀ (t k : Nat),
      regSig.val t = 0xFF#8 →
      regSig.val (t + k) = 0xFF#8 := by
  intro t k h_init
  induction k with
  | zero => simpa using h_init
  | succ k ih =>
    have h_at_tk : regSig.val (t + k) = 0xFF#8 := ih
    have h_step : t + (k + 1) = (t + k) + 1 := by omega
    rw [h_step, h_recurrence (t + k), h_at_tk]
    exact satNext_saturated (en.val (t + k))

```
## 6.7 Exercise — saturating 4-bit counter

Adapt the above for a **4-bit** saturating counter that caps
at `0xF#4`.  Prove the bound and the stickiness property.
Reference solution in `Solutions/Ch06.lean`.

```lean
-- TODO: implement `sat4Next` and prove its bound + stickiness.

end Notebooks.Ch06
```
