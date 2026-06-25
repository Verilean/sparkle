/-
  Divider — cycle-33 register correctness and cycle-34 output, for ALL four
  RISC-V operations (DIVU / REMU / DIV / REM), any divisor ≠ 0.

  Connects the FSM state sequence `divStates` (with its counter/start control)
  to the bare working-step iteration `bwsteps`, then applies `bwsteps_32`:
  after a start pulse the 32 working steps run on the *magnitudes* `|D|`,`|V|`
  that `divNext` latches, so at cycle 33 the quotient register holds `|D|/|V|`
  and the remainder register holds `|D|%|V|`.  At cycle 34 the output decode
  applies the latched sign correction, yielding exactly `BitVec.udiv`/`umod`
  (unsigned) and `BitVec.sdiv`/`srem` (signed).  (`done` strobes at cycle 34.)
-/
import Sparkle.Verification.Divider.Bridge
import Sparkle.Verification.Divider.BitProof
import Std.Tactic.BVDecide

set_option maxHeartbeats 1000000
set_option maxRecDepth 16384

namespace Sparkle.Verification.Divider.States33

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.RV32.Divider
open Sparkle.Verification.Divider.Bridge
open Sparkle.Verification.Divider.BitProof

/-- A start pulse: high only at cycle 0. -/
def startPulse {dom : DomainConfig} : Signal dom Bool := ⟨fun t => t == 0⟩

-- ============================================================================
-- Sign pre-processing, transcribed verbatim from `divNext`'s start branch.
-- ============================================================================

/-- The sign-bit test `divNext` uses: `extractLsb' 31 1 x == 1`. -/
def signBit (x : BitVec 32) : Bool := BitVec.extractLsb' 31 1 x == 1#1

/-- The operand magnitude `divNext` latches: negate iff signed and negative. -/
def absBV (sgn : Bool) (x : BitVec 32) : BitVec 32 := if sgn && signBit x then 0#32 - x else x

/-- The output-negation flag `divNext` latches. -/
def negFlag (sgn rem : Bool) (D V : BitVec 32) : Bool :=
  if rem then sgn && signBit D
  else sgn && ((signBit D && !signBit V) || (!signBit D && signBit V))

/-- The pre-sign magnitude of the result: `|D|/|V|` (div) or `|D|%|V|` (rem). -/
def rawMag (sgn rem : Bool) (D V : BitVec 32) : BitVec 32 :=
  if rem then (absBV sgn D).umod (absBV sgn V) else (absBV sgn D).udiv (absBV sgn V)

/-- The fully decoded result `divOutput` produces (divisor ≠ 0). -/
def divResult (sgn rem : Bool) (D V : BitVec 32) : BitVec 32 :=
  if negFlag sgn rem D V then 0#32 - rawMag sgn rem D V else rawMag sgn rem D V

-- ============================================================================
-- Glue: the FSM's bit fiddling matches the standard BitVec operations.
-- ============================================================================

theorem signBit_eq_msb (x : BitVec 32) : signBit x = x.msb := by
  unfold signBit
  rw [BitVec.msb_eq_getLsbD_last]
  exact (BitVec.getLsbD_eq_extractLsb' x 31).symm

theorem zero_sub_neg (x : BitVec 32) : 0#32 - x = -x := BitVec.zero_sub x

/-- The magnitude of a non-zero divisor is non-zero. -/
theorem absBV_pos (sgn : Bool) (V : BitVec 32) (hV : V ≠ 0#32) : 0 < (absBV sgn V).toNat := by
  have hVn : V.toNat ≠ 0 := fun h => hV (BitVec.eq_of_toNat_eq (by simpa using h))
  unfold absBV
  split
  · rw [zero_sub_neg, BitVec.toNat_neg]
    have : V.toNat < 2 ^ 32 := V.isLt
    omega
  · omega

theorem divResult_udiv (D V : BitVec 32) : divResult false false D V = D.udiv V := by
  simp [divResult, rawMag, negFlag, absBV]

theorem divResult_umod (D V : BitVec 32) : divResult false true D V = D.umod V := by
  simp [divResult, rawMag, negFlag, absBV]

theorem divResult_sdiv (D V : BitVec 32) : divResult true false D V = BitVec.sdiv D V := by
  simp only [divResult, rawMag, negFlag, absBV, signBit_eq_msb, zero_sub_neg, Bool.true_and,
    Bool.false_eq_true, if_false]
  cases hd : D.msb <;> cases hv : V.msb <;> simp [BitVec.sdiv, hd, hv]

theorem divResult_srem (D V : BitVec 32) : divResult true true D V = BitVec.srem D V := by
  simp only [divResult, rawMag, negFlag, absBV, signBit_eq_msb, zero_sub_neg, Bool.true_and,
    if_true]
  cases hd : D.msb <;> cases hv : V.msb <;> simp [BitVec.srem, hd, hv]

-- ============================================================================
-- FSM transition lemmas (generalised over is_signed / is_rem).
-- ============================================================================

/-- One working transition equals one `bwstep` and preserves the latched
    divisor / negate / is-rem registers (independent of `is_signed`/`is_rem`). -/
theorem divNext_working (st : DivState) (D V : BitVec 32) (sgn rem : Bool)
    (hidle : (st.1 == 0#6) = false) (hfin : (st.1 == 1#6) = false) :
    (divNext st D V false sgn rem false).2.1 = (bwstep st.2.2.2.1 st.2.1 st.2.2.1).1
    ∧ (divNext st D V false sgn rem false).2.2.1 = (bwstep st.2.2.2.1 st.2.1 st.2.2.1).2
    ∧ (divNext st D V false sgn rem false).1 = st.1 - 1#6
    ∧ (divNext st D V false sgn rem false).2.2.2.1 = st.2.2.2.1
    ∧ (divNext st D V false sgn rem false).2.2.2.2.2.1 = st.2.2.2.2.2.1
    ∧ (divNext st D V false sgn rem false).2.2.2.2.2.2.1 = st.2.2.2.2.2.2.1 := by
  unfold divNext bwstep
  simp only [hidle, hfin, Bool.not_false, Bool.and_self, if_true]
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The finishing transition (counter = 1): registers unchanged except the
    counter clears and `done` asserts. -/
theorem divNext_finishing (st : DivState) (D V : BitVec 32) (sgn rem : Bool)
    (hfin : (st.1 == 1#6) = true) :
    divNext st D V false sgn rem false
      = (0#6, st.2.1, st.2.2.1, st.2.2.2.1, st.2.2.2.2.1,
         st.2.2.2.2.2.1, st.2.2.2.2.2.2.1, true) := by
  unfold divNext
  simp only [hfin, Bool.not_true, Bool.not_false, Bool.and_false, Bool.false_and, Bool.and_true]
  rfl

/-- The latched state after the start pulse (any operation). -/
theorem divNext_start (D V : BitVec 32) (sgn rem : Bool) :
    divNext divInit D V true sgn rem false
      = (33#6, 0#33, absBV sgn D, 0#1 ++ absBV sgn V, D, negFlag sgn rem D V, rem, false) := by
  unfold divNext divInit absBV negFlag signBit
  simp

/-- With `start = false`, `divNext` never rewrites the dividend register
    (`dividendRegNext` only fires on `startAndIdle`).  Holds for the idle,
    working *and* finishing transitions — no counter hypotheses needed. -/
theorem divNext_preserves_dividend (st : DivState) (D V : BitVec 32) (sgn rem : Bool) :
    (divNext st D V false sgn rem false).2.2.2.2.1 = st.2.2.2.2.1 := by
  unfold divNext
  simp only [Bool.false_and]
  rfl

/-- **The done register is exactly the `counter == 1` test** (with `abort =
    false`): `doneNext := isFinishing && (!abort) = (counter == 1) && true`.
    Independent of `start` and every operand, so it holds for the idle,
    working *and* finishing transitions. -/
theorem divNext_done (st : DivState) (D V : BitVec 32) (start sgn rem : Bool) :
    (divNext st D V start sgn rem false).2.2.2.2.2.2.2 = (st.1 == 1#6) := by
  unfold divNext
  simp only [Bool.not_false, Bool.and_true]

/-- With `start = false` and an idle counter (`counter = 0`), the counter stays
    `0`: `startAndIdle`/`isWorking`/`isFinishing` are all false, so `counterNext`
    falls through to `counterReg`. -/
theorem divNext_idle_counter (st : DivState) (D V : BitVec 32) (sgn rem : Bool)
    (h : st.1 = 0#6) :
    (divNext st D V false sgn rem false).1 = 0#6 := by
  unfold divNext
  simp [h]

-- the run of the FSM from a start pulse (a `def`, not `abbrev`, so `rw` does
-- not eagerly unfold it and force deep `divStates` reduction)
private def run (V32 D32 : BitVec 32) (sgn rem : Bool) (n : Nat) : DivState :=
  divStates (dom := defaultDomain) (Signal.pure D32) (Signal.pure V32) startPulse
    (Signal.pure sgn) (Signal.pure rem) (Signal.pure false) n

/-- A 6-bit register compares unequal to a constant when their `toNat`s differ. -/
private theorem counter_beq_false {a c : BitVec 6} (h : a.toNat ≠ c.toNat) :
    (a == c) = false := by
  cases hh : (a == c) with
  | false => rfl
  | true => rw [beq_iff_eq] at hh; rw [hh] at h; omega

/-- **One FSM transition at any cycle `≥ 1`.**  The start pulse is low for every
    `t ≥ 1`, so the step runs with `start = false`.  Folds the repeated
    `startPulse`-unfolding boilerplate used throughout the divider proofs. -/
theorem run_step_lo (V D : BitVec 32) (sgn rem : Bool) (n : Nat) :
    run V D sgn rem (n + 1 + 1) = divNext (run V D sgn rem (n + 1)) D V false sgn rem false := by
  show divNext (run V D sgn rem (n + 1)) D V
    ((startPulse (dom := defaultDomain)).val (n + 1)) sgn rem false = _
  rw [show (startPulse (dom := defaultDomain)).val (n + 1) = false from by simp [startPulse]]

/-- **The FSM drives the working iteration on the magnitudes.**  After a start
    pulse, the state at cycle `m+1` has counter `33-m`, divisor register
    `0 ++ |V|`, remainder/quotient equal to `m` working steps on `(0, |D|)`, the
    negate / is-rem registers latched, and the dividend register still holding
    the raw `D` (needed for the divide-by-zero REM/REMU result). -/
theorem divStates_run (V32 D32 : BitVec 32) (sgn rem : Bool) :
    ∀ m, m ≤ 32 →
      (run V32 D32 sgn rem (m + 1)).1.toNat = 33 - m
      ∧ (run V32 D32 sgn rem (m + 1)).2.2.2.1 = 0#1 ++ absBV sgn V32
      ∧ (run V32 D32 sgn rem (m + 1)).2.1 = (bwsteps (0#1 ++ absBV sgn V32) m (0#33, absBV sgn D32)).1
      ∧ (run V32 D32 sgn rem (m + 1)).2.2.1 = (bwsteps (0#1 ++ absBV sgn V32) m (0#33, absBV sgn D32)).2
      ∧ (run V32 D32 sgn rem (m + 1)).2.2.2.2.2.1 = negFlag sgn rem D32 V32
      ∧ (run V32 D32 sgn rem (m + 1)).2.2.2.2.2.2.1 = rem
      ∧ (run V32 D32 sgn rem (m + 1)).2.2.2.2.1 = D32 := by
  intro m
  induction m with
  | zero =>
    intro _
    have h1 : run V32 D32 sgn rem 1
        = (33#6, 0#33, absBV sgn D32, 0#1 ++ absBV sgn V32, D32, negFlag sgn rem D32 V32, rem, false) := by
      show divNext divInit D32 V32 true sgn rem false = _
      exact divNext_start D32 V32 sgn rem
    rw [h1]
    refine ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
    show (33#6 : BitVec 6).toNat = 33 - 0
    decide
  | succ m ih =>
    intro hm1
    obtain ⟨hcount, hdiv, hRm, hQm, hNeg, hIsRem, hDvd⟩ := ih (by omega)
    have hidle : ((run V32 D32 sgn rem (m + 1)).1 == 0#6) = false :=
      counter_beq_false (by rw [hcount]; show 33 - m ≠ 0; omega)
    have hfin : ((run V32 D32 sgn rem (m + 1)).1 == 1#6) = false :=
      counter_beq_false (by rw [hcount]; show 33 - m ≠ 1; omega)
    have hstep := run_step_lo V32 D32 sgn rem m
    obtain ⟨hwR, hwQ, hwC, hwD, hwNeg, hwIsRem⟩ :=
      divNext_working (run V32 D32 sgn rem (m + 1)) D32 V32 sgn rem hidle hfin
    rw [hstep]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hwC, BitVec.toNat_sub]
      simp only [BitVec.toNat_ofNat]
      omega
    · rw [hwD, hdiv]
    · rw [hwR, hdiv, hRm, hQm]; rfl
    · rw [hwQ, hdiv, hRm, hQm]; rfl
    · rw [hwNeg, hNeg]
    · rw [hwIsRem, hIsRem]
    · rw [divNext_preserves_dividend]; exact hDvd

-- ============================================================================
-- Done-pulse timing: `done` is high at cycle 34 and nowhere else.
-- ============================================================================

/-- **The counter is cleared from cycle 34 onward.**  The finishing transition
    (cycle 33 → 34) zeroes the counter, and every later transition (start low,
    counter idle) leaves it at `0`. -/
theorem run_counter_zero (V D : BitVec 32) (sgn rem : Bool) :
    ∀ t, 34 ≤ t → (run V D sgn rem t).1 = 0#6 := by
  intro t
  induction t with
  | zero => intro h; exact absurd h (by omega)
  | succ s ih =>
    intro hle
    rcases Nat.lt_or_ge s 34 with hlt | hge
    · -- 34 ≤ s + 1 and s < 34 force s = 33: the finishing transition clears it.
      have hs : s = 33 := by omega
      subst hs
      obtain ⟨hc, _, _, _, _, _, _⟩ := divStates_run V D sgn rem 32 (by omega)
      have hfin33 : ((run V D sgn rem (32 + 1)).1 == 1#6) = true := by
        rw [show (run V D sgn rem (32 + 1)).1 = 1#6 from
          BitVec.eq_of_toNat_eq (by rw [hc]; decide)]; decide
      show (run V D sgn rem (32 + 1 + 1)).1 = 0#6
      rw [run_step_lo, divNext_finishing _ _ _ _ _ hfin33]
    · -- s ≥ 34: idle persistence keeps the counter at 0.
      obtain ⟨k, rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
      rw [run_step_lo]
      exact divNext_idle_counter _ _ _ _ _ (ih hge)

/-- **The counter holds the finishing value `1` at cycle 33.** -/
theorem run_counter_33 (V D : BitVec 32) (sgn rem : Bool) : (run V D sgn rem 33).1 = 1#6 := by
  obtain ⟨hc, _, _, _, _, _, _⟩ := divStates_run V D sgn rem 32 (by omega)
  apply BitVec.eq_of_toNat_eq
  show (run V D sgn rem (32 + 1)).1.toNat = (1#6).toNat
  rw [hc]; decide

/-- **The cycle 33 → 34 transition is the finishing transition.** -/
theorem run_34_eq (V D : BitVec 32) (sgn rem : Bool) :
    run V D sgn rem 34 = divNext (run V D sgn rem 33) D V false sgn rem false :=
  run_step_lo V D sgn rem 32

/-- **The counter equals `1` only at cycle 33.**  Before the start pulse it is
    `0`; during the 32 working steps (cycles 1..33) it counts `33 → 1`, hitting
    `1` exactly at cycle 33; from cycle 34 on it is `0`. -/
theorem run_counter_ne_one (V D : BitVec 32) (sgn rem : Bool) (s : Nat) (hs : s ≠ 33) :
    (run V D sgn rem s).1.toNat ≠ 1 := by
  rcases s with _ | s'
  · -- cycle 0: counter = 0
    rw [show (run V D sgn rem 0).1 = 0#6 from rfl]; decide
  · rcases Nat.lt_or_ge (s' + 1) 34 with hlt | hge
    · -- cycles 1..32: counter = 34 - (s'+1) ∈ [2, 33]
      obtain ⟨hc, _, _, _, _, _, _⟩ := divStates_run V D sgn rem s' (by omega)
      rw [hc]; omega
    · -- cycles ≥ 34: counter = 0
      rw [run_counter_zero V D sgn rem (s' + 1) hge]; decide

/-- **Done-pulse timing (pure FSM).**  After a start pulse, the `done` register
    is high at cycle 34 and low at every other cycle: `done t = (t == 34)`. -/
theorem run_done (V D : BitVec 32) (sgn rem : Bool) (t : Nat) :
    (run V D sgn rem t).2.2.2.2.2.2.2 = (t == 34) := by
  rcases t with _ | s
  · rfl
  · have hstep : (run V D sgn rem (s + 1)).2.2.2.2.2.2.2 = ((run V D sgn rem s).1 == 1#6) := by
      show (divNext (run V D sgn rem s) D V (startPulse.val s) sgn rem false).2.2.2.2.2.2.2 = _
      exact divNext_done _ _ _ _ _ _
    rw [hstep]
    by_cases h : s = 33
    · subst h
      rw [run_counter_33]; decide
    · rw [counter_beq_false (c := 1#6) (run_counter_ne_one V D sgn rem s h),
        beq_eq_false_iff_ne.mpr (show s + 1 ≠ 34 by omega)]

/-- **`divOutput` at cycle 34 (the `done` cycle), any operation, divisor ≠ 0.**
    The finishing transition fires, `done` asserts, and the decode returns the
    fully sign-corrected `divResult`. -/
theorem divOutput_run_34 (V32 D32 : BitVec 32) (sgn rem : Bool) (hV : V32 ≠ 0#32) :
    divOutput (run V32 D32 sgn rem 34) = (divResult sgn rem D32 V32, true) := by
  have hVpos : 0 < (absBV sgn V32).toNat := absBV_pos sgn V32 hV
  obtain ⟨_, hdv, hR, hQ, hNeg, hIsRem, _⟩ := divStates_run V32 D32 sgn rem 32 (by omega)
  have hV33 : (0#1 ++ absBV sgn V32 : BitVec 33).toNat = (absBV sgn V32).toNat := by
    rw [BitVec.toNat_append]; simp
  have hbR := (bwsteps_32 (0#1 ++ absBV sgn V32) (absBV sgn D32)
    (hV33.symm ▸ hVpos) (hV33.symm ▸ (absBV sgn V32).isLt) (absBV sgn D32).isLt).1
  have hbQ := (bwsteps_32 (0#1 ++ absBV sgn V32) (absBV sgn D32)
    (hV33.symm ▸ hVpos) (hV33.symm ▸ (absBV sgn V32).isLt) (absBV sgn D32).isLt).2
  -- quotient register = |D|.udiv |V|
  have hquot : (bwsteps (0#1 ++ absBV sgn V32) 32 (0#33, absBV sgn D32)).2
      = (absBV sgn D32).udiv (absBV sgn V32) := by
    apply BitVec.eq_of_toNat_eq
    rw [hbQ, hV33]
    exact (BitVec.toNat_udiv).symm
  -- low 32 bits of the remainder register = |D|.umod |V|
  have hRlt : (bwsteps (0#1 ++ absBV sgn V32) 32 (0#33, absBV sgn D32)).1.toNat < 2 ^ 32 := by
    rw [hbR, hV33]
    exact Nat.lt_of_lt_of_le (Nat.mod_lt _ hVpos) (Nat.le_of_lt (absBV sgn V32).isLt)
  have hrem : BitVec.extractLsb' 0 32 (bwsteps (0#1 ++ absBV sgn V32) 32 (0#33, absBV sgn D32)).1
      = (absBV sgn D32).umod (absBV sgn V32) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.extractLsb'_toNat, Nat.shiftRight_zero, Nat.mod_eq_of_lt hRlt, hbR, hV33]
    exact (BitVec.toNat_umod).symm
  have hdz : ((0#1 ++ absBV sgn V32 : BitVec 33) == 0#33) = false := by
    cases h : ((0#1 ++ absBV sgn V32 : BitVec 33) == 0#33) with
    | false => rfl
    | true =>
      rw [beq_iff_eq] at h
      have := congrArg BitVec.toNat h; rw [hV33] at this; simp at this; omega
  rw [run_34_eq, divNext_finishing _ _ _ _ _ (by rw [run_counter_33]; decide)]
  dsimp only [divOutput]
  rw [hIsRem, hNeg, hdv, hR, hQ, hdz, hquot, hrem]
  simp only [divResult, rawMag, Bool.false_eq_true, if_false]

/-- **`divOutput` at cycle 34 for divisor `V = 0` (any operation).**  The
    divisor register latches `0 ++ |0| = 0`, so `divOutput` takes its
    `divByZeroResult` branch: `done` asserts and the result is the all-ones
    word `0xFFFFFFFF` for DIV/DIVU (`is_rem = false`) or the raw dividend `D`
    for REM/REMU (`is_rem = true`), exactly per the RISC-V M-extension spec. -/
theorem divOutput_run_34_byzero (D32 : BitVec 32) (sgn rem : Bool) :
    divOutput (run 0#32 D32 sgn rem 34)
      = (if rem then D32 else 0xFFFFFFFF#32, true) := by
  obtain ⟨_, hdv, _, _, _, hIsRem, hDvd⟩ := divStates_run 0#32 D32 sgn rem 32 (by omega)
  -- |0| = 0, so the latched divisor register is all-zero
  have habs0 : absBV sgn (0#32) = 0#32 := by cases sgn <;> decide
  have hdvz : (0#1 ++ absBV sgn (0#32) : BitVec 33) = 0#33 := by rw [habs0]; decide
  rw [run_34_eq, divNext_finishing _ _ _ _ _ (by rw [run_counter_33]; decide)]
  dsimp only [divOutput]
  rw [hIsRem, hDvd, hdv, hdvz]
  simp

-- ============================================================================
-- Circuit-level done-pulse timing — the `done` flag of the real `dividerSignal`
-- strobes at cycle 34 and nowhere else, for ANY operation and operands.
-- ============================================================================

/-- **Done timing (circuit).**  The `done` output of the real `dividerSignal`,
    started by `startPulse`, is high exactly at cycle 34: `done t = (t == 34)`
    for every cycle `t`, every operation and every pair of operands. -/
theorem dividerSignal_done (D V : BitVec 32) (sgn rem : Bool) (t : Nat) :
    ((dividerSignal (dom := defaultDomain) (Signal.pure D) (Signal.pure V) startPulse
        (Signal.pure sgn) (Signal.pure rem)).val t).2 = (t == 34) := by
  rw [dividerSignal_eq]
  exact run_done V D sgn rem t

/-- **`done` is low away from cycle 34** — the form requested by the audit. -/
theorem dividerSignal_done_low (D V : BitVec 32) (sgn rem : Bool) (t : Nat) (ht : t ≠ 34) :
    ((dividerSignal (dom := defaultDomain) (Signal.pure D) (Signal.pure V) startPulse
        (Signal.pure sgn) (Signal.pure rem)).val t).2 = false := by
  rw [dividerSignal_done]
  exact beq_eq_false_iff_ne.mpr ht

-- ============================================================================
-- GENERAL operating contract.  Everything above fixes a single canonical
-- scenario (start pulse at cycle 0, constant operands, no abort).  The lemmas
-- below lift all of it to an operation that begins at an ARBITRARY idle cycle
-- `t0`, with ARBITRARY surrounding input signals: the operands are sampled at
-- the start cycle and inputs thereafter are don't-cares (`abort` aside).  The
-- engine: once latched, a non-idle `divNext` ignores every input but `abort`,
-- so the arbitrary-input trajectory coincides cycle-for-cycle with the
-- constant-operand `run`, and every prior theorem transports verbatim.
-- ============================================================================

/-- **Start latching from any idle state.**  Generalises `divNext_start`: only
    `counter = 0` matters; the other registers of the idle state are discarded
    because the start transition overwrites all eight. -/
theorem divNext_start_gen (st : DivState) (D V : BitVec 32) (sgn rem : Bool)
    (hidle : st.1 = 0#6) :
    divNext st D V true sgn rem false
      = (33#6, 0#33, absBV sgn D, 0#1 ++ absBV sgn V, D, negFlag sgn rem D V, rem, false) := by
  unfold divNext absBV negFlag signBit
  simp [hidle]

/-- **Non-idle transitions ignore the data/control inputs.**  When `startAndIdle`
    is false on both sides (e.g. the counter is non-idle) and `abort = false`,
    `divNext` depends only on the current state — not on dividend/divisor/start/
    is_signed/is_rem.  This is the locality fact that makes an arbitrary-input
    run equal the constant-operand `run`. -/
theorem divNext_si_false_irrel (st : DivState)
    (D1 V1 : BitVec 32) (s1 sg1 r1 : Bool)
    (D2 V2 : BitVec 32) (s2 sg2 r2 : Bool)
    (h1 : (s1 && (st.1 == 0#6)) = false)
    (h2 : (s2 && (st.1 == 0#6)) = false) :
    divNext st D1 V1 s1 sg1 r1 false = divNext st D2 V2 s2 sg2 r2 false := by
  unfold divNext
  simp [h1, h2]

/-- **Abort suppresses the done pulse.**  With `abort = true`, `doneNext =
    isFinishing && !true = false` regardless of the rest of the state. -/
theorem divNext_abort_done (st : DivState) (D V : BitVec 32) (s sg r : Bool) :
    (divNext st D V s sg r true).2.2.2.2.2.2.2 = false := by
  unfold divNext
  simp only [Bool.not_true, Bool.and_false]

/-- The `run` counter is non-idle on cycles `1..33` (it counts `33 → 1`). -/
theorem run_counter_pos (V D : BitVec 32) (sgn rem : Bool) (n : Nat)
    (h1 : 1 ≤ n) (h2 : n ≤ 33) :
    ((run V D sgn rem n).1 == 0#6) = false := by
  obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 := ⟨n - 1, by omega⟩
  apply counter_beq_false
  obtain ⟨hc, _, _, _, _, _, _⟩ := divStates_run V D sgn rem p (by omega)
  rw [hc, show (0#6 : BitVec 6).toNat = 0 from rfl]
  omega

section General

variable {dom : DomainConfig}
  (dividend divisor : Signal dom (BitVec 32))
  (start is_signed is_rem abort : Signal dom Bool)

/-- **The bridge: an arbitrary-input run coincides with the constant `run`.**
    If the machine is idle at cycle `t0` and `start` fires there with `abort`
    low across the operation window, then for every cycle `t0 + (m+1)`,
    `1 ≤ m+1 ≤ 34`, the real state equals the constant-operand `run` at `m+1`,
    where the operands are the values *sampled at `t0`*.  Hence the surrounding
    inputs — operands after `t0`, `start` during the run, `is_signed`/`is_rem`
    after `t0` — are all don't-cares. -/
theorem divStates_bridge (t0 : Nat) (D V : BitVec 32) (sgn rem : Bool)
    (hidle : (divStates dividend divisor start is_signed is_rem abort t0).1 = 0#6)
    (hstart : start.val t0 = true)
    (hD : dividend.val t0 = D) (hV : divisor.val t0 = V)
    (hsgn : is_signed.val t0 = sgn) (hrem : is_rem.val t0 = rem)
    (habort : ∀ k, k ≤ 33 → abort.val (t0 + k) = false) :
    ∀ m, m ≤ 33 →
      divStates dividend divisor start is_signed is_rem abort (t0 + (m + 1))
        = run V D sgn rem (m + 1) := by
  intro m
  induction m with
  | zero =>
    intro _
    have e1 : run V D sgn rem 1
        = (33#6, 0#33, absBV sgn D, 0#1 ++ absBV sgn V, D, negFlag sgn rem D V, rem, false) := by
      show divNext divInit D V true sgn rem false = _
      exact divNext_start D V sgn rem
    rw [e1]
    show divNext (divStates dividend divisor start is_signed is_rem abort t0)
      (dividend.val t0) (divisor.val t0) (start.val t0) (is_signed.val t0) (is_rem.val t0)
      (abort.val t0) = _
    rw [hstart, hD, hV, hsgn, hrem, show abort.val t0 = false from habort 0 (by omega)]
    exact divNext_start_gen _ D V sgn rem hidle
  | succ m ih =>
    intro hm
    have ihm := ih (by omega)
    show divNext (divStates dividend divisor start is_signed is_rem abort (t0 + (m + 1)))
      (dividend.val (t0 + (m + 1))) (divisor.val (t0 + (m + 1))) (start.val (t0 + (m + 1)))
      (is_signed.val (t0 + (m + 1))) (is_rem.val (t0 + (m + 1))) (abort.val (t0 + (m + 1)))
      = run V D sgn rem (m + 1 + 1)
    rw [ihm, show abort.val (t0 + (m + 1)) = false from habort (m + 1) (by omega)]
    show divNext (run V D sgn rem (m + 1)) _ _ _ _ _ false
      = divNext (run V D sgn rem (m + 1)) D V (startPulse.val (m + 1)) sgn rem false
    apply divNext_si_false_irrel
    · rw [run_counter_pos V D sgn rem (m + 1) (by omega) (by omega)]; exact Bool.and_false _
    · have : (startPulse (dom := defaultDomain)).val (m + 1) = false := by simp [startPulse]
      rw [this]; exact Bool.false_and _

/-- **General result correctness (divisor ≠ 0).**  An operation that starts at
    any idle cycle `t0` produces, at `t0 + 34`, the fully sign-corrected
    `divResult` of the operands *sampled at `t0`* — for ALL four operations
    (DIVU/REMU/DIV/REM via `divResult_{udiv,umod,sdiv,srem}`), with arbitrary
    surrounding inputs.  `done` is simultaneously high (see below). -/
theorem dividerSignal_result_gen (t0 : Nat) (D V : BitVec 32) (sgn rem : Bool)
    (hidle : (divStates dividend divisor start is_signed is_rem abort t0).1 = 0#6)
    (hstart : start.val t0 = true)
    (hD : dividend.val t0 = D) (hV : divisor.val t0 = V)
    (hsgn : is_signed.val t0 = sgn) (hrem : is_rem.val t0 = rem)
    (habort : ∀ k, k ≤ 33 → abort.val (t0 + k) = false)
    (hVne : V ≠ 0#32) :
    (dividerSignal dividend divisor start is_signed is_rem abort).val (t0 + 34)
      = (divResult sgn rem D V, true) := by
  rw [dividerSignal_eq]
  have hb : divStates dividend divisor start is_signed is_rem abort (t0 + 34)
      = run V D sgn rem 34 :=
    divStates_bridge dividend divisor start is_signed is_rem abort t0 D V sgn rem
      hidle hstart hD hV hsgn hrem habort 33 (by omega)
  rw [hb]
  exact divOutput_run_34 V D sgn rem hVne

/-- **General divide-by-zero.**  Starting at any idle cycle `t0` with a zero
    divisor sampled there, the result at `t0 + 34` is `0xFFFFFFFF` (DIV/DIVU) or
    the raw dividend `D` (REM/REMU), `done` high — per the RISC-V spec. -/
theorem dividerSignal_byzero_gen (t0 : Nat) (D : BitVec 32) (sgn rem : Bool)
    (hidle : (divStates dividend divisor start is_signed is_rem abort t0).1 = 0#6)
    (hstart : start.val t0 = true)
    (hD : dividend.val t0 = D) (hV : divisor.val t0 = 0#32)
    (hsgn : is_signed.val t0 = sgn) (hrem : is_rem.val t0 = rem)
    (habort : ∀ k, k ≤ 33 → abort.val (t0 + k) = false) :
    (dividerSignal dividend divisor start is_signed is_rem abort).val (t0 + 34)
      = (if rem then D else 0xFFFFFFFF#32, true) := by
  rw [dividerSignal_eq]
  have hb : divStates dividend divisor start is_signed is_rem abort (t0 + 34)
      = run 0#32 D sgn rem 34 :=
    divStates_bridge dividend divisor start is_signed is_rem abort t0 D 0#32 sgn rem
      hidle hstart hD hV hsgn hrem habort 33 (by omega)
  rw [hb]
  exact divOutput_run_34_byzero D sgn rem

/-- **General done-pulse timing.**  After a start at idle cycle `t0`, `done` is
    high exactly at `t0 + 34` and low across the rest of the operation window
    (`done (t0+k) = (k == 34)` for `1 ≤ k ≤ 34`), for arbitrary inputs. -/
theorem dividerSignal_done_gen (t0 : Nat) (D V : BitVec 32) (sgn rem : Bool)
    (hidle : (divStates dividend divisor start is_signed is_rem abort t0).1 = 0#6)
    (hstart : start.val t0 = true)
    (hD : dividend.val t0 = D) (hV : divisor.val t0 = V)
    (hsgn : is_signed.val t0 = sgn) (hrem : is_rem.val t0 = rem)
    (habort : ∀ k, k ≤ 33 → abort.val (t0 + k) = false)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : k ≤ 34) :
    ((dividerSignal dividend divisor start is_signed is_rem abort).val (t0 + k)).2 = (k == 34) := by
  rw [dividerSignal_eq]
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hb : divStates dividend divisor start is_signed is_rem abort (t0 + (m + 1))
      = run V D sgn rem (m + 1) :=
    divStates_bridge dividend divisor start is_signed is_rem abort t0 D V sgn rem
      hidle hstart hD hV hsgn hrem habort m (by omega)
  rw [hb]
  show (run V D sgn rem (m + 1)).2.2.2.2.2.2.2 = (m + 1 == 34)
  exact run_done V D sgn rem (m + 1)

/-- **The machine returns to idle after the operation.**  At cycle `t0 + 34`
    the counter is back to `0`, so a fresh operation may start there — chaining
    this with `hidle` at the next `t0` makes the contract reusable for
    back-to-back operations. -/
theorem divStates_idle_after_gen (t0 : Nat) (D V : BitVec 32) (sgn rem : Bool)
    (hidle : (divStates dividend divisor start is_signed is_rem abort t0).1 = 0#6)
    (hstart : start.val t0 = true)
    (hD : dividend.val t0 = D) (hV : divisor.val t0 = V)
    (hsgn : is_signed.val t0 = sgn) (hrem : is_rem.val t0 = rem)
    (habort : ∀ k, k ≤ 33 → abort.val (t0 + k) = false) :
    (divStates dividend divisor start is_signed is_rem abort (t0 + 34)).1 = 0#6 := by
  have hb : divStates dividend divisor start is_signed is_rem abort (t0 + 34)
      = run V D sgn rem 34 :=
    divStates_bridge dividend divisor start is_signed is_rem abort t0 D V sgn rem
      hidle hstart hD hV hsgn hrem habort 33 (by omega)
  rw [hb]
  exact run_counter_zero V D sgn rem 34 (by omega)

/-- **Abort suppresses the done pulse.**  Whenever `abort` is high at cycle
    `ta`, the `done` output is low at `ta + 1`, for any state/inputs — the FSM
    cannot emit a stale completion strobe through an abort. -/
theorem dividerSignal_abort_done_gen (ta : Nat) (ha : abort.val ta = true) :
    ((dividerSignal dividend divisor start is_signed is_rem abort).val (ta + 1)).2 = false := by
  rw [dividerSignal_eq]
  show (divNext (divStates dividend divisor start is_signed is_rem abort ta)
    (dividend.val ta) (divisor.val ta) (start.val ta) (is_signed.val ta) (is_rem.val ta)
    (abort.val ta)).2.2.2.2.2.2.2 = false
  rw [ha]
  exact divNext_abort_done _ _ _ _ _ _

end General

-- ============================================================================
-- Canonical single-shot circuit results — the common case (start pulse at
-- cycle 0, constant operands), now stated as thin corollaries of the GENERAL
-- contract above (`dividerSignal_result_gen` / `_byzero_gen` at `t0 = 0`).
-- These are the readable, named entry points for the four RISC-V operations.
-- ============================================================================

/-- The general result contract at the canonical scenario — start pulse at
    cycle 0, constant (pure) operands, no abort.  The four named operations
    below are immediate via `divResult_{udiv,umod,sdiv,srem}`. -/
theorem dividerSignal_canonical (D V : BitVec 32) (sgn rem : Bool) (hV : V ≠ 0#32) :
    (dividerSignal (dom := defaultDomain) (Signal.pure D) (Signal.pure V) startPulse
        (Signal.pure sgn) (Signal.pure rem)).val 34 = (divResult sgn rem D V, true) := by
  have h := dividerSignal_result_gen (dom := defaultDomain)
    (Signal.pure D) (Signal.pure V) startPulse (Signal.pure sgn) (Signal.pure rem)
    (Signal.pure false) 0 D V sgn rem rfl (by simp [startPulse]) rfl rfl rfl rfl
    (fun k _ => rfl) hV
  simpa using h

/-- The general divide-by-zero contract at the canonical scenario. -/
theorem dividerSignal_canonical_byzero (D : BitVec 32) (sgn rem : Bool) :
    (dividerSignal (dom := defaultDomain) (Signal.pure D) (Signal.pure 0#32) startPulse
        (Signal.pure sgn) (Signal.pure rem)).val 34 = (if rem then D else 0xFFFFFFFF#32, true) := by
  have h := dividerSignal_byzero_gen (dom := defaultDomain)
    (Signal.pure D) (Signal.pure 0#32) startPulse (Signal.pure sgn) (Signal.pure rem)
    (Signal.pure false) 0 D sgn rem rfl (by simp [startPulse]) rfl rfl rfl rfl (fun k _ => rfl)
  simpa using h

/-- **DIVU** — unsigned quotient, any divisor ≠ 0. -/
theorem dividerSignal_divu (D V : BitVec 32) (hV : V ≠ 0#32) :
    (dividerSignal (dom := defaultDomain) (Signal.pure D) (Signal.pure V) startPulse
        (Signal.pure false) (Signal.pure false)).val 34 = (D.udiv V, true) := by
  have h := dividerSignal_canonical D V false false hV; rwa [divResult_udiv] at h

/-- **REMU** — unsigned remainder, any divisor ≠ 0. -/
theorem dividerSignal_remu (D V : BitVec 32) (hV : V ≠ 0#32) :
    (dividerSignal (dom := defaultDomain) (Signal.pure D) (Signal.pure V) startPulse
        (Signal.pure false) (Signal.pure true)).val 34 = (D.umod V, true) := by
  have h := dividerSignal_canonical D V false true hV; rwa [divResult_umod] at h

/-- **DIV** — signed quotient (truncating, RISC-V semantics), any divisor ≠ 0. -/
theorem dividerSignal_sdiv (D V : BitVec 32) (hV : V ≠ 0#32) :
    (dividerSignal (dom := defaultDomain) (Signal.pure D) (Signal.pure V) startPulse
        (Signal.pure true) (Signal.pure false)).val 34 = (BitVec.sdiv D V, true) := by
  have h := dividerSignal_canonical D V true false hV; rwa [divResult_sdiv] at h

/-- **REM** — signed remainder (sign of dividend, RISC-V semantics), any divisor ≠ 0. -/
theorem dividerSignal_srem (D V : BitVec 32) (hV : V ≠ 0#32) :
    (dividerSignal (dom := defaultDomain) (Signal.pure D) (Signal.pure V) startPulse
        (Signal.pure true) (Signal.pure true)).val 34 = (BitVec.srem D V, true) := by
  have h := dividerSignal_canonical D V true true hV; rwa [divResult_srem] at h

/-- **DIVU by zero** — all ones (`0xFFFFFFFF`), any dividend. -/
theorem dividerSignal_divu_by_zero (D : BitVec 32) :
    (dividerSignal (dom := defaultDomain) (Signal.pure D) (Signal.pure 0#32) startPulse
        (Signal.pure false) (Signal.pure false)).val 34 = (0xFFFFFFFF#32, true) := by
  simpa using dividerSignal_canonical_byzero D false false

/-- **REMU by zero** — the dividend, unchanged, any dividend. -/
theorem dividerSignal_remu_by_zero (D : BitVec 32) :
    (dividerSignal (dom := defaultDomain) (Signal.pure D) (Signal.pure 0#32) startPulse
        (Signal.pure false) (Signal.pure true)).val 34 = (D, true) := by
  simpa using dividerSignal_canonical_byzero D false true

/-- **DIV (signed) by zero** — all ones (`-1 = 0xFFFFFFFF`), any dividend. -/
theorem dividerSignal_sdiv_by_zero (D : BitVec 32) :
    (dividerSignal (dom := defaultDomain) (Signal.pure D) (Signal.pure 0#32) startPulse
        (Signal.pure true) (Signal.pure false)).val 34 = (0xFFFFFFFF#32, true) := by
  simpa using dividerSignal_canonical_byzero D true false

/-- **REM (signed) by zero** — the dividend, unchanged, any dividend. -/
theorem dividerSignal_srem_by_zero (D : BitVec 32) :
    (dividerSignal (dom := defaultDomain) (Signal.pure D) (Signal.pure 0#32) startPulse
        (Signal.pure true) (Signal.pure true)).val 34 = (D, true) := by
  simpa using dividerSignal_canonical_byzero D true true

end Sparkle.Verification.Divider.States33
