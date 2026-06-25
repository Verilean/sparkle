/-
  Divider — Signal circuit ↔ pure FSM bridge.

  `dividerSignal` is built from `Signal.loop`, which is opaque.  Using the
  `loop_iterate` reduction from `LoopProps`, this file proves that the real
  circuit is *exactly* a pure finite state machine:

    * `divInit`   — the reset state
    * `divNext`   — the pure one-step transition (mirrors `dividerLoopBody`)
    * `divOutput` — the pure output decode (mirrors `dividerSignal`'s tail)
    * `divStates` — the state sequence obtained by iterating `divNext`

  Main results:
    * `loopState_eq`     : the opaque loop equals `divStates` at every cycle
    * `dividerSignal_eq` : `(dividerSignal …).val t = divOutput (divStates … t)`

  After this, all reasoning about the hardware happens on the pure FSM —
  no `Signal` and no `Signal.loop` remain in the obligations.
-/
import Sparkle.Verification.LoopProps
import IP.RV32.Divider

set_option maxHeartbeats 1000000
set_option maxRecDepth 16384

namespace Sparkle.Verification.Divider.Bridge

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Verification.LoopProps
open Sparkle.IP.RV32.Divider

-- ============================================================================
-- Pure model
-- ============================================================================

/-- Reset state: counter idle, everything zero/false. -/
def divInit : DivState := (0#6, 0#33, 0#32, 0#33, 0#32, false, false, false)

/-- Pure one-step transition — a faithful transcription of `dividerLoopBody`.
    `st` is the current 8-register state; the remaining arguments are the
    external inputs sampled this cycle. -/
def divNext (st : DivState) (dividend divisor : BitVec 32)
    (start is_signed is_rem abort : Bool) : DivState :=
  let counterReg    := st.1
  let remainderReg  := st.2.1
  let quotientReg   := st.2.2.1
  let divisorReg    := st.2.2.2.1
  let dividendReg   := st.2.2.2.2.1
  let negateReg     := st.2.2.2.2.2.1
  let isRemReg      := st.2.2.2.2.2.2.1
  let isIdle := counterReg == 0#6
  let isFinishing := counterReg == 1#6
  let isWorking := (!isIdle) && (!isFinishing)
  let dividendSign := BitVec.extractLsb' 31 1 dividend == 1#1
  let divisorSign := BitVec.extractLsb' 31 1 divisor == 1#1
  let dividendNeg := 0#32 - dividend
  let dividendNeedNeg := is_signed && dividendSign
  let absDividend := if dividendNeedNeg then dividendNeg else dividend
  let divisorNeg := 0#32 - divisor
  let divisorNeedNeg := is_signed && divisorSign
  let absDivisor := if divisorNeedNeg then divisorNeg else divisor
  let signsDiffer_a := dividendSign && (!divisorSign)
  let signsDiffer_b := (!dividendSign) && divisorSign
  let signsDiffer := signsDiffer_a || signsDiffer_b
  let negateQuot := is_signed && signsDiffer
  let negateRem := is_signed && dividendSign
  let negateFlag := if is_rem then negateRem else negateQuot
  let startAndIdle := start && isIdle
  let absDivisor33 := (0#1 : BitVec 1) ++ absDivisor
  let quotientTopBit := BitVec.extractLsb' 31 1 quotientReg
  let quotientTopBit33 := (0#32 : BitVec 32) ++ quotientTopBit
  let remShifted := remainderReg <<< (1#33)
  let remWithBit := remShifted ||| quotientTopBit33
  let trialSub := remWithBit - divisorReg
  let trialBit32 := BitVec.extractLsb' 32 1 trialSub
  let trialNonNeg := trialBit32 == 0#1
  let newRemainder := if trialNonNeg then trialSub else remWithBit
  let quotShifted := quotientReg <<< (1#32)
  let quotWithBit := quotShifted ||| (if trialNonNeg then 1#32 else 0#32)
  let counterDec := counterReg - 1#6
  let counterNext :=
    if abort then 0#6
    else if startAndIdle then 33#6
    else if isWorking then counterDec
    else if isFinishing then 0#6
    else counterReg
  let remainderNext :=
    if startAndIdle then 0#33
    else if isWorking then newRemainder
    else remainderReg
  let quotientNext :=
    if startAndIdle then absDividend
    else if isWorking then quotWithBit
    else quotientReg
  let divisorRegNext := if startAndIdle then absDivisor33 else divisorReg
  let dividendRegNext := if startAndIdle then dividend else dividendReg
  let negateNext := if startAndIdle then negateFlag else negateReg
  let isRemNext := if startAndIdle then is_rem else isRemReg
  let doneNext := isFinishing && (!abort)
  (counterNext, remainderNext, quotientNext, divisorRegNext,
   dividendRegNext, negateNext, isRemNext, doneNext)

/-- Pure output decode — mirrors the tail of `dividerSignal`. -/
def divOutput (st : DivState) : BitVec 32 × Bool :=
  let remainderReg  := st.2.1
  let quotientReg   := st.2.2.1
  let divisorReg    := st.2.2.2.1
  let dividendReg   := st.2.2.2.2.1
  let negateReg     := st.2.2.2.2.2.1
  let isRemReg      := st.2.2.2.2.2.2.1
  let doneReg       := st.2.2.2.2.2.2.2
  let finalRem := BitVec.extractLsb' 0 32 remainderReg
  let rawResult := if isRemReg then finalRem else quotientReg
  let negResult := 0#32 - rawResult
  let result := if negateReg then negResult else rawResult
  let divisorRegIsZero := divisorReg == 0#33
  let divByZeroResult := if isRemReg then dividendReg else 0xFFFFFFFF#32
  let finalOutput := if divisorRegIsZero then divByZeroResult else result
  (finalOutput, doneReg)

/-- The pure state sequence: iterate `divNext`, sampling the input signals. -/
def divStates {dom : DomainConfig}
    (dividend divisor : Signal dom (BitVec 32))
    (start is_signed is_rem abort : Signal dom Bool) : Nat → DivState
  | 0 => divInit
  | t + 1 =>
    divNext (divStates dividend divisor start is_signed is_rem abort t)
      (dividend.val t) (divisor.val t) (start.val t)
      (is_signed.val t) (is_rem.val t) (abort.val t)

-- ============================================================================
-- Bridge: dividerLoopBody reduces to divInit / divNext cycle-by-cycle
-- ============================================================================

variable {dom : DomainConfig}
  (dividend divisor : Signal dom (BitVec 32))
  (start is_signed is_rem abort : Signal dom Bool)

theorem dividerBody_zero (s : Signal dom DivState) :
    (dividerLoopBody dividend divisor start is_signed is_rem abort s).val 0 = divInit := by
  rfl

theorem dividerBody_succ (s : Signal dom DivState) (t : Nat) :
    (dividerLoopBody dividend divisor start is_signed is_rem abort s).val (t + 1)
      = divNext (s.val t) (dividend.val t) (divisor.val t) (start.val t)
          (is_signed.val t) (is_rem.val t) (abort.val t) := by
  rfl

/-- **The bridge.**  The opaque `Signal.loop` state equals the pure iterate. -/
theorem loopState_eq (t : Nat) :
    (Signal.loop
      (dividerLoopBody dividend divisor start is_signed is_rem abort)).val t
      = divStates dividend divisor start is_signed is_rem abort t := by
  apply loop_iterate
    (f := dividerLoopBody dividend divisor start is_signed is_rem abort)
    (c0 := divInit)
    (next := fun u x => divNext x (dividend.val u) (divisor.val u) (start.val u)
                          (is_signed.val u) (is_rem.val u) (abort.val u))
    (st := divStates dividend divisor start is_signed is_rem abort)
  · intro s; exact dividerBody_zero dividend divisor start is_signed is_rem abort s
  · intro s u; exact dividerBody_succ dividend divisor start is_signed is_rem abort s u
  · rfl
  · intro u; rfl

/-- **Circuit = pure FSM.**  Every output sample of the real `dividerSignal`
    equals the pure output decode of the pure state sequence. -/
theorem dividerSignal_eq (t : Nat) :
    (dividerSignal dividend divisor start is_signed is_rem abort).val t
      = divOutput (divStates dividend divisor start is_signed is_rem abort t) := by
  have hL := loopState_eq dividend divisor start is_signed is_rem abort
  simp only [dividerSignal, divOutput, hL, bundle2_val, fst_val, snd_val, mux_val,
    beq_val, bv_sub_valCl, map_val, pure_val]

/- The general unsigned correctness theorems (register values at cycle 33, and
   the circuit-level output `(D/V, true)` at cycle 34) are proved downstream in
   `Sparkle.Verification.Divider.States33` — they need `Divider.BitProof`, which
   imports this file, so they cannot live here. -/

end Sparkle.Verification.Divider.Bridge


