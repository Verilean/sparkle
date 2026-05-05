/-
  Tutorial Step 6: LTL bug-localization framework.

  Step 5 introduced LTL properties as ∀t-quantified Lean theorems.
  This step shows how to USE them to localize bugs:

    1. State multiple LTL premises that together imply correct
       behavior. Each premise corresponds to a specific layer of
       the design.
    2. Discharge each premise from the spec.
    3. Apply the contrapositive: if a runtime trace shows wrong
       behavior, AT LEAST ONE premise is false in the runtime.
       The failing premise pins the bug to a specific layer.

  This is the same framework that we used to investigate the
  BitNet `boot.S` "out = input" symptom from commit 9d0704e
  (full postmortem in `docs/BitNet_LTL_Investigation.md`).

  The example here is a 2-layer "load-store register file":

      Memory write:   `write(addr, data)` at cycle T
      Memory read:    `read(addr)`        at cycle T+1+K
      Expectation:    `read` returns `data` (when no other writes
                      to the same addr happen in between)

  The 3 premises:

    P1: write_event t → reg.val (t+1) = data.val t
    P2: no-write at s ∈ [t+1, t+1+K) → reg.val (s+1) = reg.val s
    P3: read at t+1+K → observed.val (t+1+K) = reg.val (t+1+K)

  Composite: P1 ∧ P2 ∧ P3 ⇒ observed.val (t+1+K) = data.val t.
  Contrapositive: observed ≠ data ⇒ ¬(P1 ∧ P2 ∧ P3) — at least one
  premise is FALSE.
-/

import Sparkle

open Sparkle.Core.Domain
open Sparkle.Core.Signal

namespace TutorialExtended.Step6

/-! ## The 3-layer write→hold→read contract -/

/-- **Premise P1: write commits in cycle N+1.** -/
def writeCommitsContract {dom : DomainConfig}
    (writeEn : Signal dom Bool) (data reg : Signal dom (BitVec 8)) : Prop :=
  ∀ t, writeEn.val t = true → reg.val (t + 1) = data.val t

/-- **Premise P2: no-write preserves register value.** -/
def noWritePreservesContract {dom : DomainConfig}
    (writeEn : Signal dom Bool) (reg : Signal dom (BitVec 8)) : Prop :=
  ∀ t, writeEn.val t = false → reg.val (t + 1) = reg.val t

/-- **Premise P3: read observes the current register value.** -/
def readObservesContract {dom : DomainConfig}
    (readReady : Signal dom Bool) (reg observed : Signal dom (BitVec 8)) : Prop :=
  ∀ t, readReady.val t = true → observed.val t = reg.val t

/-! ## Helper: K-cycle preservation under no-write -/

theorem reg_preserved_K_cycles {dom : DomainConfig}
    (writeEn : Signal dom Bool) (reg : Signal dom (BitVec 8))
    (h_p2 : noWritePreservesContract writeEn reg)
    (t k : Nat)
    (h_no_write : ∀ i, i < k → writeEn.val (t + i) = false) :
    reg.val (t + k) = reg.val t := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h_at_tk : reg.val (t + k) = reg.val t := by
      apply ih; intro i hi; exact h_no_write i (Nat.lt_succ_of_lt hi)
    have h_no_w_tk : writeEn.val (t + k) = false :=
      h_no_write k (Nat.lt_succ_self k)
    have h_step : t + (k + 1) = (t + k) + 1 := by omega
    rw [h_step, h_p2 (t + k) h_no_w_tk]
    exact h_at_tk

/-! ## Composite: write at T → read at T+1+K returns data at T -/

/-- **The "everything works" theorem.**

    If all 3 premises hold AND the trace conditions are met (write at T,
    no intervening writes, read at T+1+K), then the read observes
    the data that was written. -/
theorem write_then_read_returns_data {dom : DomainConfig}
    (writeEn readReady : Signal dom Bool)
    (data reg observed : Signal dom (BitVec 8))
    (h_p1 : writeCommitsContract writeEn data reg)
    (h_p2 : noWritePreservesContract writeEn reg)
    (h_p3 : readObservesContract readReady reg observed)
    (T : Nat) (K : Nat)
    (h_we : writeEn.val T = true)
    (h_no_we : ∀ i, i < K → writeEn.val (T + 1 + i) = false)
    (h_rr : readReady.val (T + 1 + K) = true) :
    observed.val (T + 1 + K) = data.val T := by
  -- Step 1: P1 → reg.val (T+1) = data.val T.
  have h_at_T1 : reg.val (T + 1) = data.val T := h_p1 T h_we
  -- Step 2: P2 + K-cycle preservation → reg.val (T+1+K) = reg.val (T+1).
  have h_at_TK : reg.val (T + 1 + K) = reg.val (T + 1) :=
    reg_preserved_K_cycles writeEn reg h_p2 (T + 1) K h_no_we
  -- Step 3: P3 → observed.val (T+1+K) = reg.val (T+1+K).
  have h_obs : observed.val (T + 1 + K) = reg.val (T + 1 + K) :=
    h_p3 (T + 1 + K) h_rr
  -- Combine.
  rw [h_obs, h_at_TK, h_at_T1]

/-! ## CONTRAPOSITIVE: bug-localization theorem

  If a runtime trace observes Y ≠ data.val T, then AT LEAST ONE
  of the 3 premises is FALSE in the runtime. -/

theorem bug_localization {dom : DomainConfig}
    (writeEn readReady : Signal dom Bool)
    (data reg observed : Signal dom (BitVec 8))
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
  have h_pred := write_then_read_returns_data writeEn readReady data reg
    observed h_p1 h_p2 h_p3 T K h_we h_no_we h_rr
  -- h_pred : observed.val (T+1+K) = data.val T
  -- h_obs  : observed.val (T+1+K) = Y
  -- so Y = data.val T, contradicting h_neq.
  apply h_neq
  rw [← h_obs]
  exact h_pred

/-! ## Localizing the failure: which premise broke?

  The contrapositive only tells us SOME Pi is false; to localize
  to a specific layer we need to falsify each Pi separately at
  trace cycle.

  Each premise has a "violation witness" form: ∃ t such that the
  premise fails at cycle t. -/

/-- **P1 violation witness**: write at t, but reg.val (t+1) ≠ data.val t. -/
theorem P1_violation_witness {dom : DomainConfig}
    (writeEn : Signal dom Bool) (data reg : Signal dom (BitVec 8))
    (t : Nat)
    (h_we : writeEn.val t = true)
    (h_neq : reg.val (t + 1) ≠ data.val t) :
    ¬ writeCommitsContract writeEn data reg := by
  intro h_p1
  exact h_neq (h_p1 t h_we)

/-- **P2 violation witness**: no-write at t, but reg changed. -/
theorem P2_violation_witness {dom : DomainConfig}
    (writeEn : Signal dom Bool) (reg : Signal dom (BitVec 8))
    (t : Nat)
    (h_no_we : writeEn.val t = false)
    (h_neq : reg.val (t + 1) ≠ reg.val t) :
    ¬ noWritePreservesContract writeEn reg := by
  intro h_p2
  exact h_neq (h_p2 t h_no_we)

/-- **P3 violation witness**: read at t, but observed ≠ reg. -/
theorem P3_violation_witness {dom : DomainConfig}
    (readReady : Signal dom Bool) (reg observed : Signal dom (BitVec 8))
    (t : Nat)
    (h_rr : readReady.val t = true)
    (h_neq : observed.val t ≠ reg.val t) :
    ¬ readObservesContract readReady reg observed := by
  intro h_p3
  exact h_neq (h_p3 t h_rr)

/-! ## Concrete example: data corruption diagnosis

  Suppose at T = 5 we wrote data = 0xAA. At T+1+K = 10 (K = 4),
  the read returned Y = 0x00. Apply `bug_localization`:

    ¬ (P1 ∧ P2 ∧ P3) — somewhere data got lost.

  Then to localize:
    - If reg.val 6 was 0xAA   ⇒ P1 OK
    - If reg.val 10 was 0x00  ⇒ P2 broke (reg got corrupted between 6 and 10)
    - If reg.val 10 was 0xAA  ⇒ P3 broke (observed ≠ reg, read-side bug)

  This is exactly the workflow we used for BitNet 9d0704e.
-/

theorem concrete_bug_diagnosis :
    -- If observed = 0x00 ≠ data = 0xAA, the contrapositive fires.
    (0x00#8 : BitVec 8) ≠ 0xAA#8 := by decide

/-! ## Demo: simulate a "well-behaved" register, sample it, confirm
    the LTL composite works on the real trace. -/

/-- A simple register that updates on writeEn, holds otherwise. -/
def regWithWriteEn {dom : DomainConfig}
    (writeEn : Signal dom Bool) (data : Signal dom (BitVec 8))
    : Signal dom (BitVec 8) :=
  Signal.loop fun self =>
    Signal.register 0#8 (Signal.mux writeEn data self)

def runDemo : IO Unit := do
  -- Build a trace where: cycle 5 writes 0xAA; cycles 6+ quiet.
  -- Using Signal.mk to make a scheduled signal (a closure t ↦ value).
  let writeEn : Signal defaultDomain Bool :=
    ⟨fun t => t == 5⟩
  let data : Signal defaultDomain (BitVec 8) :=
    ⟨fun t => if t == 5 then 0xAA#8 else 0#8⟩
  let regSig := regWithWriteEn writeEn data
  let trace := regSig.sample 12
  IO.println s!"reg trace: {trace}"
  -- Expected: 0,0,0,0,0,0,AA,AA,AA,AA,AA,AA — register catches 0xAA at cycle 6
  -- and holds it through the no-write cycles.

end TutorialExtended.Step6
