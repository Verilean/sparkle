/-
  Width-generic Q-format divider — the precision upgrade of `IP/RV32/Divider`.

  ## Why the RV32 divider is not enough

  `IP/RV32/Divider.lean` is a 32-bit *integer* restoring divider with RISC-V
  edge-case semantics, and its correctness proof
  (`Sparkle/Verification/Divider/`) is pinned to exactly 33 iterations at
  exactly 32 bits.  A Kalman gain needs *fractional* division:

      K = num / den   in Q(w-f).f   ⇒   quotient = (num · 2^f) / den

  so the dividend is `w + f` bits wide before the divide even starts.  Rather
  than perturb the one fully-proven circuit in the repo, this module is the
  width-generic restoring core, parameterized on `(w, f)` the same way
  `FixedPointGen` is, with the RV32 divider's loop structure carried over
  (compare `dividerLoopBody` — start / working / finishing phases, trial
  subtraction against a widened divisor, quotient bits shifted in from the top).

  ## Semantics

  `divQref` below is the reference: `saturate ((num.toInt * 2^f).tdiv den.toInt)`.

  Note **`tdiv`, not floor**.  The hardware divides magnitudes and negates,
  which truncates toward zero — unlike the multiply path, whose arithmetic
  shift floors.  So division error is in `(-1, 1)` LSB and *sign-dependent*,
  twice the multiply's `(-1, 0]`.  The error budget in
  `proofs/SparkleProofs/Control/` must use `|error| < lsb` for any divided
  quantity, and does.

  Saturation: `(num · 2^f) / den` can exceed the `w`-bit range (small
  denominator), so the quotient clamps to `±(2^(w-1)-1)` instead of wrapping.
  Division by zero saturates positive or negative by the dividend's sign —
  the restoring core produces the all-ones quotient naturally in that case,
  which the clamp then folds into the same saturation value.  Total, and the
  right behaviour for a control datapath: a huge gain, not a wrapped garbage one.

  ## Cycle count

  `W + 2` cycles per division where `W = w + f` (one start, `W` shift steps,
  one finishing).  Q15.16 (`w=32, f=16`): 50 cycles.  At a 27 MHz clock and a
  1 kHz control loop that is 0.19 % of the sample period — multi-cycle is free
  here.
-/

import Sparkle
import Sparkle.Compiler.Elab
import IP.Control.FixedPointGen

set_option maxRecDepth 100000

namespace Sparkle.IP.Control.DividerQ

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Control.FixedPointGen

variable {dom : DomainConfig}

/-! ### Pure reference semantics -/

/-- Saturate an `Int` into the **symmetric** signed `w`-bit range
    `[-(2^(w-1)-1), 2^(w-1)-1]`.

    Symmetric on purpose: the circuit negates a clamped magnitude, so the
    asymmetric `INT_MIN` is never produced, and this reference matches it
    exactly.  (Also matches `FixedPointGen.clampSym`'s convention.) -/
def satToWidth (w : Nat) (x : Int) : BitVec w :=
  if x > 2 ^ (w - 1) - 1 then BitVec.ofInt w (2 ^ (w - 1) - 1)
  else if x < -(2 ^ (w - 1) - 1) then BitVec.ofInt w (-(2 ^ (w - 1) - 1))
  else BitVec.ofInt w x

/-- Reference Q division: `(num · 2^f) tdiv den`, saturated to `w` bits.

    `tdiv` (truncate toward zero) because the hardware divides magnitudes and
    then negates — see the header.  Division by zero saturates by the sign of
    the dividend (positive max for `num ≥ 0`, negative max otherwise). -/
def divQref (w f : Nat) (num den : BitVec w) : BitVec w :=
  if den.toInt == 0 then
    if num.toInt < 0 then BitVec.ofInt w (-(2 ^ (w - 1) - 1))
    else BitVec.ofInt w (2 ^ (w - 1) - 1)
  else
    satToWidth w ((num.toInt * 2 ^ f).tdiv den.toInt)

/-! ### The FSM, as a pure step function

Mirrors the `Signal` circuit below definition-for-definition, so the test can
cross-check the circuit against this and this against `divQref`. -/

/-- Divider state.  `W = w + f` is the core width; the remainder carries one
    extra bit for the trial subtraction's sign. -/
structure State (W : Nat) where
  /-- 0 = idle; `W+1 .. 1` = counting down through the shift steps. -/
  counter : BitVec 8
  /-- Working remainder, `W+1` bits. -/
  rem : BitVec (W + 1)
  /-- Quotient accumulator; starts holding the widened |dividend|. -/
  quot : BitVec W
  /-- Latched |divisor|, widened. -/
  den : BitVec (W + 1)
  /-- Negate the final quotient (signs differed). -/
  negate : Bool
  /-- Done pulse. -/
  done : Bool

instance (W : Nat) : Inhabited (State W) :=
  ⟨⟨0#8, BitVec.zero _, BitVec.zero _, BitVec.zero _, false, false⟩⟩

/-- One cycle.  `num`/`den` are the Q(w-f).f operands, sampled on `start`. -/
def step (w f : Nat) (st : State (w + f)) (num den : BitVec w) (start : Bool)
    : State (w + f) :=
  let W := w + f
  let isIdle := st.counter = 0#8
  let isFinishing := st.counter = 1#8
  let isWorking := ¬isIdle ∧ ¬isFinishing
  if start ∧ isIdle then
    -- Latch: magnitudes, sign, pre-shift the dividend by f.
    let numNeg := num.toInt < 0
    let denNeg := den.toInt < 0
    let absNum := if numNeg then -num else num
    let absDen := if denNeg then -den else den
    -- |num| · 2^f as the W-bit initial "quotient" (dividend bits shift out its top)
    let dividendW : BitVec W := (absNum.zeroExtend W) <<< f
    let denW1 : BitVec (W + 1) := absDen.zeroExtend (W + 1)
    { counter := BitVec.ofNat 8 (W + 1)
      rem := BitVec.zero _
      quot := dividendW
      den := denW1
      negate := numNeg ≠ denNeg
      done := false }
  else if isWorking then
    -- Restoring step: shift the next dividend bit into the remainder, trial-subtract.
    let topBit : BitVec (W + 1) := (st.quot.extractLsb' (W - 1) 1).zeroExtend (W + 1)
    let remShift := (st.rem <<< 1) ||| topBit
    let trial := remShift - st.den
    let trialNonNeg := trial.extractLsb' W 1 = 0#1
    { st with
      counter := st.counter - 1#8
      rem := if trialNonNeg then trial else remShift
      quot := (st.quot <<< 1) ||| (if trialNonNeg then BitVec.ofNat W 1 else BitVec.zero W)
      done := false }
  else if isFinishing then
    { st with counter := 0#8, done := true }
  else
    { st with done := false }

/-- Decode the result from a finished divider: saturate the `W`-bit magnitude
    into `w` bits, apply the sign. -/
def result (w f : Nat) (st : State (w + f)) : BitVec w :=
  let mag : Int := st.quot.toNat   -- magnitude, always ≥ 0
  let signedVal : Int := if st.negate then -mag else mag
  satToWidth w signedVal

/-- Run a complete division through the pure FSM: pulse `start`, iterate until
    `done`, decode.  Fuel-bounded; `w + f + 4` cycles always suffice. -/
def runDivision (w f : Nat) (num den : BitVec w) : BitVec w := Id.run do
  let mut st : State (w + f) := default
  st := step w f st num den true
  for _ in [0 : w + f + 3] do
    if st.done then
      return result w f st
    st := step w f st num den false
  return result w f st

/-! ### The circuit -/

/-- Divider state bundle for `Signal.loop`, matching `bundleAll!` order:
    counter, remainder, quotient, divisor, negate, done. -/
abbrev SigState (W : Nat) : Type :=
  BitVec 8 × BitVec (W + 1) × BitVec W × BitVec (W + 1) × Bool × Bool

/-- The combinational next-state body — the `Signal`-level image of `step`.
    Same shape as `IP/RV32/Divider.dividerLoopBody`. -/
@[reducible] def loopBody (w f : Nat)
    (num den : Signal dom (BitVec w)) (start : Signal dom Bool)
    : Signal dom (SigState (w + f)) → Signal dom (SigState (w + f)) :=
  fun state =>
    let W := w + f
    let counterReg := projN! state 6 0
    let remReg := projN! state 6 1
    let quotReg := projN! state 6 2
    let denReg := projN! state 6 3
    let negateReg := projN! state 6 4

    let isIdle := counterReg === (Signal.lit dom 0#8)
    let isFinishing := counterReg === (Signal.lit dom 1#8)
    let isWorking := (~~~isIdle) &&& (~~~isFinishing)
    let startAndIdle := start &&& isIdle

    -- START: magnitudes + sign via MSB (`Signal.slt` against 0 also works;
    -- MSB-extract matches the RV32 divider and the synth-verified idiom).
    let numNeg := (num.map (BitVec.extractLsb' (w - 1) 1 ·)) === (Signal.lit dom 1#1)
    let denNeg := (den.map (BitVec.extractLsb' (w - 1) 1 ·)) === (Signal.lit dom 1#1)
    let zeroW := (Signal.lit dom (BitVec.zero w) : Signal dom (BitVec w))
    let absNum := Signal.mux numNeg (zeroW - num) num
    let absDen := Signal.mux denNeg (zeroW - den) den

    -- widen |num| to W bits and pre-shift by f: high zeros ++ |num|, then <<< f
    let dividendW : Signal dom (BitVec W) :=
      ((Signal.lit dom (BitVec.zero f) : Signal dom (BitVec f)) ++ absNum : Signal dom (BitVec (f + w))).map
        (BitVec.extractLsb' 0 W ·) <<< (Signal.lit dom (BitVec.ofNat W f))
    -- widen |den| to W+1 bits
    let denW1 : Signal dom (BitVec (W + 1)) :=
      ((Signal.lit dom (BitVec.zero (f + 1)) : Signal dom (BitVec (f + 1))) ++ absDen
        : Signal dom (BitVec (f + 1 + w))).map (BitVec.extractLsb' 0 (W + 1) ·)

    let negA := numNeg &&& (~~~denNeg)
    let negB := (~~~numNeg) &&& denNeg
    let negateFlag := negA ||| negB

    -- WORKING: restoring step.
    -- Widen the quotient's top bit to W+1 via a constant-prefix append
    -- (`.map zeroExtend` does NOT lower in the synth elaborator; a pure-zero
    -- `++` does).
    let topBit1 : Signal dom (BitVec 1) := quotReg.map (BitVec.extractLsb' (W - 1) 1 ·)
    let topBit : Signal dom (BitVec (W + 1)) :=
      ((Signal.lit dom (BitVec.zero W) : Signal dom (BitVec W)) ++ topBit1
        : Signal dom (BitVec (W + 1)))
    let remShift := (remReg <<< (Signal.lit dom (BitVec.ofNat (W + 1) 1))) ||| topBit
    let trial := remShift - denReg
    let trialNonNeg := (trial.map (BitVec.extractLsb' W 1 ·)) === (Signal.lit dom 0#1)
    let newRem := Signal.mux trialNonNeg trial remShift
    let quotShift := quotReg <<< (Signal.lit dom (BitVec.ofNat W 1))
    let oneW := (Signal.lit dom (BitVec.ofNat W 1) : Signal dom (BitVec W))
    let zeroWq := (Signal.lit dom (BitVec.zero W) : Signal dom (BitVec W))
    let newQuot := quotShift ||| (Signal.mux trialNonNeg oneW zeroWq)

    -- Next-state muxes: start > working > finishing > hold.
    let counterNext :=
      Signal.mux startAndIdle (Signal.lit dom (BitVec.ofNat 8 (W + 1)))
        (Signal.mux isWorking (counterReg - (Signal.lit dom 1#8))
          (Signal.mux isFinishing (Signal.lit dom 0#8) counterReg))
    let remNext :=
      Signal.mux startAndIdle (Signal.lit dom (BitVec.zero (W + 1)))
        (Signal.mux isWorking newRem remReg)
    let quotNext :=
      Signal.mux startAndIdle dividendW
        (Signal.mux isWorking newQuot quotReg)
    let denNext := Signal.mux startAndIdle denW1 denReg
    let negateNext := Signal.mux startAndIdle negateFlag negateReg
    let doneNext := isFinishing

    bundleAll! [
      Signal.register 0#8 counterNext,
      Signal.register (BitVec.zero (W + 1)) remNext,
      Signal.register (BitVec.zero W) quotNext,
      Signal.register (BitVec.zero (W + 1)) denNext,
      Signal.register false negateNext,
      Signal.register false doneNext
    ]

/-- The divider engine.  Emits `(result, done)`; `result` is valid on the
    cycle `done` pulses.  Instantiate at concrete `(w, f)` for synthesis —
    same convention as every module in `FixedPointGen`. -/
@[reducible] def dividerQ (w f : Nat)
    (num den : Signal dom (BitVec w)) (start : Signal dom Bool)
    : Signal dom (BitVec w × Bool) :=
  let W := w + f
  let state := Signal.loop (loopBody w f num den start)
  let quotReg := projN! state 6 2
  let negateReg := projN! state 6 4
  let doneReg := projN! state 6 5
  -- Saturating narrow: magnitude ≥ 2^(w-1) ⇒ clamp.
  let maxW : Signal dom (BitVec W) := Signal.lit dom (BitVec.ofNat W (2 ^ (w - 1) - 1))
  let tooBig := Signal.ult maxW quotReg
  let magClamped := Signal.mux tooBig maxW quotReg
  let magNarrow : Signal dom (BitVec w) := magClamped.map (BitVec.extractLsb' 0 w ·)
  let zeroS := (Signal.lit dom (BitVec.zero w) : Signal dom (BitVec w))
  -- negative saturation is -(2^(w-1)-1) - 1... keep symmetric: negate the
  -- clamped magnitude, so range is [-(2^(w-1)-1), 2^(w-1)-1].  Symmetric on
  -- purpose (matches `clampSym`); the asymmetric INT_MIN is never produced.
  let signedResult := Signal.mux negateReg (zeroS - magNarrow) magNarrow
  bundle2 signedResult doneReg

/-! ### Concrete instantiations -/

/-- Q7.8 divider (core width 24, 26 cycles). -/
@[reducible] def dividerQ7_8 (num den : Signal dom (BitVec 16)) (start : Signal dom Bool)
    : Signal dom (BitVec 16 × Bool) :=
  dividerQ 16 8 num den start

/-- Q15.16 divider (core width 48, 50 cycles) — the Kalman-gain divider. -/
@[reducible] def dividerQ15_16 (num den : Signal dom (BitVec 32)) (start : Signal dom Bool)
    : Signal dom (BitVec 32 × Bool) :=
  dividerQ 32 16 num den start

end Sparkle.IP.Control.DividerQ
