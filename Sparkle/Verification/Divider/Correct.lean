/-
  Divider — end-to-end correctness on the real `dividerSignal`.

  Built on the `Signal.loop` characterization (`LoopProps`) and the circuit ↔
  pure-FSM bridge (`Divider.Bridge`).  These are genuine machine-checked
  theorems about the actual hardware-generating `dividerSignal`.

  Timing.  With `start` pulsed at cycle 0 while idle, the FSM latches at cycle
  1 (counter ← 33), runs 32 restoring-division steps, and asserts `done` for one
  cycle at cycle 34 with the final result.  All theorems sample cycle 34.

  Scope of THIS file: the special cases pinned to literal RISC-V values —
  divide-by-zero (DIVU/REMU → 0xFFFFFFFF / dividend) and the signed overflow
  INT_MIN / −1 (DIV → INT_MIN, REM → 0).  The general `V ≠ 0` correctness for
  all four operations is in `Divider.States33` (`dividerSignal_{divu,remu,sdiv,
  srem}`), proved for every input rather than sampled vectors; the divide-by-
  zero result for every dividend (all four operations) is likewise general
  there (`dividerSignal_{divu,remu,sdiv,srem}_by_zero`).  The literal vectors
  below remain as independent native-decide cross-checks of the FSM model.
-/
import Sparkle.Verification.Divider.Bridge

set_option maxHeartbeats 400000

namespace Sparkle.Verification.Divider.Correct

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.RV32.Divider
open Sparkle.Verification.Divider.Bridge

/-- A `start` pulse: high only at cycle 0 (the divider must be idle then). -/
def startPulse {dom : DomainConfig} : Signal dom Bool := ⟨fun t => t == 0⟩

/-- Run the pure FSM from a single start pulse with constant operands, sampling
    the `done` cycle (34).  Returns `(result, done)`. -/
def runDiv (dividend divisor : BitVec 32) (isSigned isRem : Bool) : BitVec 32 × Bool :=
  divOutput (divStates (dom := defaultDomain)
    (Signal.pure dividend) (Signal.pure divisor) startPulse
    (Signal.pure isSigned) (Signal.pure isRem) (Signal.pure false) 34)

/-- **Circuit = run.**  The real `dividerSignal`, sampled at the `done` cycle,
    equals the pure `runDiv`.  This is the bridge specialised to the start
    scenario; every concrete theorem below rewrites through it. -/
theorem circuit_eq_run (D V : BitVec 32) (sgn rem : Bool) :
    (dividerSignal (dom := defaultDomain) (Signal.pure D) (Signal.pure V)
        startPulse (Signal.pure sgn) (Signal.pure rem)).val 34
      = runDiv D V sgn rem := by
  rw [dividerSignal_eq]; rfl

-- ============================================================================
-- Edge cases excluded from the generic theorem and the batched vectors below:
-- divide-by-zero and the signed INT_MIN / −1 overflow.
-- ============================================================================

/-- DIVU by zero → all ones (0xFFFFFFFF). -/
theorem divu_by_zero :
    (dividerSignal (dom := defaultDomain) (Signal.pure 100#32) (Signal.pure 0#32)
        startPulse (Signal.pure false) (Signal.pure false)).val 34 = (0xFFFFFFFF#32, true) := by
  rw [circuit_eq_run 100#32 0#32 false false]; native_decide

/-- REMU by zero → the dividend, unchanged. -/
theorem remu_by_zero :
    (dividerSignal (dom := defaultDomain) (Signal.pure 100#32) (Signal.pure 0#32)
        startPulse (Signal.pure false) (Signal.pure true)).val 34 = (100#32, true) := by
  rw [circuit_eq_run 100#32 0#32 false true]; native_decide

/-- DIV signed overflow: INT_MIN / (−1) → INT_MIN (no trap, per spec). -/
theorem div_intmin_div_neg1 :
    (dividerSignal (dom := defaultDomain) (Signal.pure 0x80000000#32) (Signal.pure (-1#32))
        startPulse (Signal.pure true) (Signal.pure false)).val 34 = (0x80000000#32, true) := by
  rw [circuit_eq_run 0x80000000#32 (-1#32) true false]; native_decide

/-- REM signed overflow: INT_MIN % (−1) → 0 (per spec). -/
theorem rem_intmin_rem_neg1 :
    (dividerSignal (dom := defaultDomain) (Signal.pure 0x80000000#32) (Signal.pure (-1#32))
        startPulse (Signal.pure true) (Signal.pure true)).val 34 = (0#32, true) := by
  rw [circuit_eq_run 0x80000000#32 (-1#32) true true]; native_decide

/- General correctness for every divisor `V ≠ 0` — DIVU/REMU/DIV/REM against
   `BitVec.udiv`/`umod`/`sdiv`/`srem` — is proved for ALL inputs (not just
   sampled vectors) in `Sparkle.Verification.Divider.States33`
   (`dividerSignal_divu` / `_remu` / `_sdiv` / `_srem`). Divide-by-zero for
   ALL dividends (DIVU/DIV → 0xFFFFFFFF, REMU/REM → dividend) is proved there
   too (`dividerSignal_{divu,remu,sdiv,srem}_by_zero`), so `divu_by_zero` /
   `remu_by_zero` above are now corollary vectors of those general theorems.
   The INT_MIN/−1 signed overflow cases (V = −1 ≠ 0) remain genuine boundary
   points pinned to their literal RISC-V values. -/

end Sparkle.Verification.Divider.Correct
