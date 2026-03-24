/-
  Hardware Divider — Signal DSL

  Multi-cycle restoring division algorithm for RV32 M-extension.
  Takes ~33 cycles per division operation.

  Inputs:
    dividend[31:0]  - Numerator
    divisor[31:0]   - Denominator
    start           - Begin a new division (pulse)
    is_signed       - Treat inputs as signed (DIV/REM vs DIVU/REMU)
    is_rem          - Return remainder instead of quotient

  Output:
    result[31:0]    - Quotient or remainder
    done            - Result valid for 1 cycle

  State registers (8 total in Signal.loop):
    0: counter      : BitVec 6  -- busy counter (0=idle, 32..1=shifting)
    1: remainder    : BitVec 33 -- working remainder (33-bit for sign)
    2: quotient     : BitVec 32 -- accumulated quotient bits
    3: divisor_reg  : BitVec 33 -- latched divisor (33-bit)
    4: dividend_reg : BitVec 32 -- latched dividend (for REM edge case)
    5: negate_result: Bool      -- negate final result
    6: is_rem_reg   : Bool      -- return remainder
    7: done_reg     : Bool      -- done pulse

  Edge cases (RISC-V spec):
    DIV by 0  -> 0xFFFFFFFF (all ones)
    DIVU by 0 -> 0xFFFFFFFF
    REM by 0  -> dividend
    REMU by 0 -> dividend
    Signed overflow (INT_MIN / -1) -> INT_MIN (DIV), 0 (REM)
-/

import Sparkle
import Sparkle.Compiler.Elab

set_option maxRecDepth 8192
set_option maxHeartbeats 800000

namespace Sparkle.Examples.RV32.Divider

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-- Multi-cycle restoring divider — Signal DSL.

    Uses Signal.loop with 8 state registers.

    FSM:
    1. On `start` AND counter=0: latch abs(dividend), abs(divisor),
       compute negate flag, set counter=33.
    2. While counter > 1: restoring division shift-subtract step, decrement.
    3. When counter=1: apply final negation if needed, assert done, set counter=0.
    4. When counter=0: idle, done=false. -/
def dividerSignal {dom : DomainConfig}
    (dividend : Signal dom (BitVec 32))
    (divisor : Signal dom (BitVec 32))
    (start : Signal dom Bool)
    (is_signed : Signal dom Bool)
    (is_rem : Signal dom Bool)
    (abort : Signal dom Bool := Signal.pure false)
    : Signal dom (BitVec 32 × Bool) :=
  let loopState := Signal.loop fun state =>
    let counterReg    := projN! state 8 0  -- BitVec 6
    let remainderReg  := projN! state 8 1  -- BitVec 33
    let quotientReg   := projN! state 8 2  -- BitVec 32
    let divisorReg    := projN! state 8 3  -- BitVec 33
    let dividendReg   := projN! state 8 4  -- BitVec 32
    let negateReg     := projN! state 8 5  -- Bool
    let isRemReg      := projN! state 8 6  -- Bool
    let doneReg       := projN! state 8 7  -- Bool

    -- Is the divider idle?
    let isIdle := counterReg === 0#6

    -- Is counter = 1? (finishing step)
    let isFinishing := counterReg === 1#6

    -- Is counter > 1? (working step)
    let isWorking := (· && ·) <$>
      (~~~isIdle) <*>
      (~~~isFinishing)

    -- ====================================================================
    -- START: Latch inputs, compute absolute values, set counter
    -- ====================================================================

    -- Sign of dividend (bit 31)
    let dividendSign := (· == ·) <$>
      (dividend.map (BitVec.extractLsb' 31 1 ·)) <*> Signal.pure 1#1
    -- Sign of divisor (bit 31)
    let divisorSign := (· == ·) <$>
      (divisor.map (BitVec.extractLsb' 31 1 ·)) <*> Signal.pure 1#1

    -- Negate dividend if signed and negative
    let dividendNeg := (· - ·) <$> Signal.pure 0#32 <*> dividend
    let dividendNeedNeg := is_signed &&& dividendSign
    let absDividend := Signal.mux dividendNeedNeg dividendNeg dividend

    -- Negate divisor if signed and negative
    let divisorNeg := (· - ·) <$> Signal.pure 0#32 <*> divisor
    let divisorNeedNeg := is_signed &&& divisorSign
    let absDivisor := Signal.mux divisorNeedNeg divisorNeg divisor

    -- For quotient: negate if signs differ (signed mode only)
    -- XOR on Bool = (a && !b) || (!a && b)
    let signsDiffer_a := dividendSign &&& (~~~divisorSign)
    let signsDiffer_b := (· && ·) <$> (~~~dividendSign) <*> divisorSign
    let signsDiffer := signsDiffer_a ||| signsDiffer_b
    let negateQuot := is_signed &&& signsDiffer

    -- For remainder: negate if dividend is negative (signed mode only)
    let negateRem := is_signed &&& dividendSign

    -- Negate result flag: depends on is_rem
    let negateFlag := Signal.mux is_rem negateRem negateQuot

    -- Divisor == 0 check
    let divisorIsZero := divisor === 0#32

    -- Start condition: start pulse AND idle
    let startAndIdle := start &&& isIdle

    -- Zero-extend absolute dividend and divisor to 33 bits
    let absDividend33 := (· ++ ·) <$> Signal.pure 0#1 <*> absDividend
    let absDivisor33 := (· ++ ·) <$> Signal.pure 0#1 <*> absDivisor

    -- ====================================================================
    -- WORKING: Restoring division step
    -- ====================================================================

    -- Shift remainder left by 1, bringing in the next dividend bit
    -- remainder_shifted = (remainder << 1) | dividend_bit
    -- The dividend bits come from quotientReg (which holds the unprocessed
    -- dividend bits, shifted left each cycle).
    -- Top bit of quotientReg is the next bit to bring into remainder.
    let quotientTopBit := quotientReg.map (BitVec.extractLsb' 31 1 ·)
    let quotientTopBit33 := (· ++ ·) <$> Signal.pure 0#32 <*> quotientTopBit

    -- Shift remainder left by 1
    let remShifted := (· <<< ·) <$> remainderReg <*> Signal.pure 1#33
    -- OR in the top bit of the quotient (next dividend bit)
    let remWithBit := remShifted ||| quotientTopBit33

    -- Trial subtraction: remainder - divisor
    let trialSub := remWithBit - divisorReg

    -- Check if subtraction result is non-negative (bit 32 = 0 means positive)
    let trialBit32 := trialSub.map (BitVec.extractLsb' 32 1 ·)
    let trialNonNeg := trialBit32 === 0#1

    -- If non-negative: remainder = trialSub, quotient bit = 1
    -- If negative: remainder unchanged (restore), quotient bit = 0
    let newRemainder := Signal.mux trialNonNeg trialSub remWithBit

    -- Shift quotient left and OR in the new bit
    let quotShifted := (· <<< ·) <$> quotientReg <*> Signal.pure 1#32
    let quotWithBit := (· ||| ·) <$> quotShifted <*>
      (Signal.mux trialNonNeg (Signal.pure 1#32) (Signal.pure 0#32))

    -- Decrement counter
    let counterDec := counterReg - 1#6

    -- ====================================================================
    -- FINISHING: Apply negation, output result
    -- ====================================================================

    -- Final quotient (from register, after last working step)
    let finalQuot := quotientReg
    -- Final remainder: lower 32 bits of remainder register
    let finalRem := remainderReg.map (BitVec.extractLsb' 0 32 ·)

    -- Select quotient or remainder
    let rawResult := Signal.mux isRemReg finalRem finalQuot

    -- Negate if needed
    let negResult := (· - ·) <$> Signal.pure 0#32 <*> rawResult
    let finalResult := Signal.mux negateReg negResult rawResult

    -- ====================================================================
    -- Div-by-zero override: when divisor was zero at start
    -- We handle this by checking divisorReg == 0 at finish time
    -- ====================================================================
    let divisorRegIsZero := divisorReg === 0#33

    -- DIV/0 -> 0xFFFFFFFF, REM/0 -> dividend
    let divByZeroResult := Signal.mux isRemReg dividendReg (Signal.pure 0xFFFFFFFF#32)
    let finishResult := Signal.mux divisorRegIsZero divByZeroResult finalResult

    -- ====================================================================
    -- State update mux: idle/start -> working -> finishing -> idle
    -- ====================================================================

    -- Counter next
    let counterNext_start := Signal.pure 33#6
    let counterNext_work := counterDec
    let counterNext_finish := Signal.pure 0#6
    let counterNext :=
      Signal.mux abort (Signal.pure 0#6)
        (Signal.mux startAndIdle counterNext_start
          (Signal.mux isWorking counterNext_work
            (Signal.mux isFinishing counterNext_finish
              counterReg)))

    -- Remainder next
    let initRemainder := Signal.pure 0#33
    let remainderNext :=
      Signal.mux startAndIdle initRemainder
        (Signal.mux isWorking newRemainder
          remainderReg)

    -- Quotient next: on start, load the absolute dividend value
    let quotientNext :=
      Signal.mux startAndIdle absDividend
        (Signal.mux isWorking quotWithBit
          quotientReg)

    -- Divisor reg next
    let divisorRegNext :=
      Signal.mux startAndIdle absDivisor33
        divisorReg

    -- Dividend reg next (for div-by-zero REM result)
    let dividendRegNext :=
      Signal.mux startAndIdle dividend
        dividendReg

    -- Negate flag next
    let negateNext :=
      Signal.mux startAndIdle negateFlag
        negateReg

    -- is_rem flag next
    let isRemNext :=
      Signal.mux startAndIdle is_rem
        isRemReg

    -- Done flag: true for exactly 1 cycle when counter transitions 1->0
    -- Suppress on abort to avoid stale done pulses
    let doneNext := isFinishing &&& (~~~abort)

    bundleAll! [
      Signal.register 0#6 counterNext,
      Signal.register 0#33 remainderNext,
      Signal.register 0#32 quotientNext,
      Signal.register 0#33 divisorRegNext,
      Signal.register 0#32 dividendRegNext,
      Signal.register false negateNext,
      Signal.register false isRemNext,
      Signal.register false doneNext
    ]

  -- Extract outputs from loop state
  let counterOut := projN! loopState 8 0
  let doneOut := projN! loopState 8 7
  let quotientOut := projN! loopState 8 2
  let remainderOut := projN! loopState 8 1
  let negateOut := projN! loopState 8 5
  let isRemOut := projN! loopState 8 6
  let divisorRegOut := projN! loopState 8 3
  let dividendRegOut := projN! loopState 8 4

  -- Recompute final result outside loop for output
  let isFinishingOut := counterOut === 1#6

  -- The done register holds the finishing flag from last cycle
  -- When done=true, the registers hold the final values
  let finalRem := remainderOut.map (BitVec.extractLsb' 0 32 ·)
  let rawResult := Signal.mux isRemOut finalRem quotientOut
  let negResult := (· - ·) <$> Signal.pure 0#32 <*> rawResult
  let result := Signal.mux negateOut negResult rawResult

  -- Div-by-zero override
  let divisorRegIsZero := divisorRegOut === 0#33
  let divByZeroResult := Signal.mux isRemOut dividendRegOut (Signal.pure 0xFFFFFFFF#32)
  let finalOutput := Signal.mux divisorRegIsZero divByZeroResult result

  bundle2 finalOutput doneOut

#synthesizeVerilog dividerSignal

end Sparkle.Examples.RV32.Divider
