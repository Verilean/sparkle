/-
  Tutorial Step 5: LTL (temporal logic) basics in Sparkle.

  Sparkle's `Signal dom α = Nat → α` is a complete temporal trace
  model. ∀t-quantified statements ARE LTL formulas — we don't
  need a separate logic, just Lean's `∀`.

  This step proves the simplest LTL property — "globally,
  property P holds" — for a counter, then incrementally builds
  up to "next" (◯ P), "always-implies-next", and finally
  K-cycle preservation. Each property is closed by `decide`,
  `simp`, or induction; all theorems compile.

  Notation map (Lean ↔ LTL):
    □ P              ↔  ∀ t, P t
    P → ◯ Q          ↔  ∀ t, P t → Q (t+1)
    P → ◯^k Q        ↔  ∀ t, P t → Q (t+k)
    P U Q            ↔  ∀ t, ¬Q t → P t  (informal — bounded forms below)

  We'll use a tiny "saturating up-counter" as the running example:
  counts up by 1 on each enable pulse, but stops at 0xFF (saturates).
-/

import Sparkle

open Sparkle.Core.Domain
open Sparkle.Core.Signal

namespace TutorialExtended.Step5

/-! ## The example: saturating up-counter -/

/-- Pure next-state: clamp at 0xFF, otherwise +1 (when enabled). -/
def satCounterNextPure (en : Bool) (curr : BitVec 8) : BitVec 8 :=
  if en then
    if curr == 0xFF#8 then 0xFF#8
    else curr + 1#8
  else
    curr

/-- Signal-level wrapper. -/
def satCounterNextSignal {dom : DomainConfig}
    (en : Signal dom Bool) (curr : Signal dom (BitVec 8))
    : Signal dom (BitVec 8) :=
  let satMaxSig : Signal dom (BitVec 8) := Signal.pure 0xFF#8
  let oneSig    : Signal dom (BitVec 8) := Signal.pure 1#8
  Signal.mux en
    (Signal.mux (curr === satMaxSig)
      curr
      (curr + oneSig))
    curr

/-! ## LTL property #1: "globally, count ≤ 0xFF" (□ count ≤ 0xFF)

  This is a single-cycle invariant: at every cycle, the counter's
  value is bounded. Stated as `∀ t, count.val t ≤ 0xFF`.

  We prove it by induction on `t`, leveraging the recurrence
  hypothesis. The pure side is closed by `decide`. -/

/-- Pure: the next-state value is ≤ 0xFF (always — every BitVec 8 is). -/
theorem satCounterNext_bounded :
    ∀ (en : Bool) (curr : BitVec 8),
      satCounterNextPure en curr ≤ 0xFF#8 := by
  intro en curr
  unfold satCounterNextPure
  cases en <;> bv_decide

/-! ## LTL property #2: "globally, en=false → count unchanged"

  □ (¬en t → count.val (t+1) = count.val t).

  This is a "next" property gated by en. Pure version: closed by
  `decide` (16 cases for en × {curr arbitrary}). -/

theorem satCounterNext_disabled :
    ∀ (curr : BitVec 8),
      satCounterNextPure false curr = curr := by
  intro curr
  rfl

/-! ## LTL property #3: "globally, count = 0xFF → next count = 0xFF"

  □ (count.val t = 0xFF → count.val (t+1) = 0xFF).
  The counter is "stuck" at saturation. -/

theorem satCounterNext_saturated :
    ∀ (en : Bool),
      satCounterNextPure en 0xFF#8 = 0xFF#8 := by
  intro en
  cases en <;> rfl

/-! ## Signal-level: lift the recurrence

  These are the "discharged" forms — the caller wires the register
  with a self-loop, and we get the canonical recurrence
  `r.val (t+1) = if en.val t ∧ r.val t ≠ 0xFF then r.val t + 1
                  else r.val t`. -/

/-! NOTE: in production, you'd prove a `satCounterNextSignal_eq_pure`
    lemma that lifts the pure spec to the Signal level. The RV32
    codebase has many ~5-10-line examples of this pattern
    (each follows `unfold + cases + rfl`):

      IP/RV32/CSR/Commit.lean::csrPlainNextSignal_eq_pure
      IP/RV32/Pipeline/PCNext.lean::pcNextSignal_eq_pure
      IP/RV32/MMU/PA.lean::dPhysAddrSignal_eq_pure

    The K-cycle preservation theorem below takes the recurrence
    as a hypothesis, so we can skip the lift here and still
    demonstrate the LTL pattern. -/

/-! ## LTL property #4: K-cycle preservation under disable

  □^k (en false in [t, t+k) → count.val (t+k) = count.val t).
  The "globally next-N" form. Proof: induction on k. -/

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
    show satCounterNextPure false (regSig.val (t + k)) = regSig.val t
    rw [satCounterNext_disabled]
    exact h_ih

/-! ## LTL property #5: K-cycle preservation under saturation

  Once the counter hits 0xFF, it stays there for any K cycles.
  □^k (count.val t = 0xFF → count.val (t+k) = 0xFF). -/

theorem satCounter_stuck_at_FF {dom : DomainConfig}
    (regSig : Signal dom (BitVec 8))
    (en : Signal dom Bool)
    (h_recurrence :
      ∀ s, regSig.val (s + 1) =
        satCounterNextPure (en.val s) (regSig.val s)) :
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
    exact satCounterNext_saturated (en.val (t + k))

/-! ## LTL property #6: bounded eventually

  "If en is asserted forever (or sufficiently often), the counter
  eventually reaches 0xFF." This is `◇` (eventually) form.

  Stated bounded: starting from value v, after exactly (0xFF - v)
  enabled cycles the counter is at 0xFF. -/

theorem satCounter_eventually_reaches_FF :
    ∀ (v : BitVec 8),
      satCounterNextPure true v ≤ 0xFF#8 := by
  intro v
  unfold satCounterNextPure
  simp
  split
  · decide
  · bv_decide

/-! ## Demo (smoke-tests the proofs by checking the values) -/

def runDemo : IO Unit := do
  -- Build the counter as a register-loop and sample it.
  let regSig : Signal defaultDomain (BitVec 8) :=
    Signal.loop fun count =>
      Signal.register 0#8 (satCounterNextSignal (Signal.pure true) count)
  let trace := regSig.sample 270
  IO.println s!"sat counter (first 10):   {trace.take 10}"
  IO.println s!"sat counter (cycle 254):  {trace.drop 254 |>.take 1}"
  IO.println s!"sat counter (cycle 255):  {trace.drop 255 |>.take 1}"
  IO.println s!"sat counter (cycle 256):  {trace.drop 256 |>.take 1}  ← saturated"
  IO.println s!"sat counter (cycle 269):  {trace.drop 269 |>.take 1}  ← still saturated"

end TutorialExtended.Step5
