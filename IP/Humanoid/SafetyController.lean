/-
  Safety Controller — Force Limiting + Fall Detection — Signal DSL

  Monitors joint torques and body attitude for humanoid safety:

  1. Torque limiting: clamp motor commands to safe range
     (prevents damage to gears and injury to humans)

  2. Collision detection: sudden torque spike = unexpected contact
     → reduce compliance (make joints soft)

  3. Fall detection: body tilt exceeds threshold
     → enter protective pose (crouch, tuck arms)

  4. Emergency stop: external E-stop signal
     → all motors to zero torque

  All Q16.16 fixed-point, fully combinational.
-/

import Sparkle.Core.Signal
import Sparkle.Core.Domain

namespace Sparkle.IP.Humanoid

open Sparkle.Core.Signal
open Sparkle.Core.Domain

variable {dom : DomainConfig}

/-- Torque limiter: clamp value to [-limit, +limit].
    Uses signed comparison via subtraction sign bit. -/
def torqueLimiter
    (value limit : Signal dom (BitVec 32))
    : Signal dom (BitVec 32) :=
  let negLimit := (Signal.pure 0#32 : Signal dom (BitVec 32)) - limit
  -- Check if value > limit
  let overMax : Signal dom Bool :=
    Signal.map (BitVec.extractLsb' 31 1 ·) (limit - value)
      === (Signal.pure 1#1 : Signal dom (BitVec 1))  -- limit < value
  -- Check if value < -limit
  let underMin : Signal dom Bool :=
    Signal.map (BitVec.extractLsb' 31 1 ·) (value - negLimit)
      === (Signal.pure 1#1 : Signal dom (BitVec 1))  -- value < negLimit
  Signal.mux overMax limit (Signal.mux underMin negLimit value)

/-- Collision detector: monitors torque rate of change.
    Spike = |torque - prevTorque| > threshold.
    Returns (collisionDetected × filteredTorque). -/
def collisionDetector
    (torque : Signal dom (BitVec 32))
    (threshold : Signal dom (BitVec 32))
    : Signal dom (Bool × BitVec 32) :=
  let state := Signal.loop (dom := dom) (α := BitVec 32)
    fun (prevTorque : Signal dom (BitVec 32)) =>
    Signal.register 0#32 torque

  let prevTorque := state
  let diff := torque - prevTorque
  -- |diff|: if negative, negate
  let isNeg : Signal dom Bool :=
    Signal.map (BitVec.extractLsb' 31 1 ·) diff
      === (Signal.pure 1#1 : Signal dom (BitVec 1))
  let absDiff := Signal.mux isNeg
    ((Signal.pure 0#32 : Signal dom (BitVec 32)) - diff) diff

  -- Compare |diff| > threshold
  let collision : Signal dom Bool :=
    Signal.map (BitVec.extractLsb' 31 1 ·) (threshold - absDiff)
      === (Signal.pure 1#1 : Signal dom (BitVec 1))

  -- On collision: reduce torque to 25% (ASR by 2)
  let softTorque := Signal.map (fun v => BitVec.sshiftRight v 2) torque
  let filteredTorque := Signal.mux collision softTorque torque

  bundle2 collision filteredTorque

/-- Fall detector: monitors body tilt angle.
    If |roll| or |pitch| exceeds fallThreshold, trigger protective response. -/
def fallDetector
    (roll pitch : Signal dom (BitVec 32))
    (fallThreshold : Signal dom (BitVec 32))
    : Signal dom (Bool × BitVec 4) :=
  -- |roll|
  let rollNeg : Signal dom Bool :=
    Signal.map (BitVec.extractLsb' 31 1 ·) roll
      === (Signal.pure 1#1 : Signal dom (BitVec 1))
  let absRoll := Signal.mux rollNeg
    ((Signal.pure 0#32 : Signal dom (BitVec 32)) - roll) roll

  -- |pitch|
  let pitchNeg : Signal dom Bool :=
    Signal.map (BitVec.extractLsb' 31 1 ·) pitch
      === (Signal.pure 1#1 : Signal dom (BitVec 1))
  let absPitch := Signal.mux pitchNeg
    ((Signal.pure 0#32 : Signal dom (BitVec 32)) - pitch) pitch

  -- Falling if either axis exceeds threshold
  let rollFall : Signal dom Bool :=
    Signal.map (BitVec.extractLsb' 31 1 ·) (fallThreshold - absRoll)
      === (Signal.pure 1#1 : Signal dom (BitVec 1))
  let pitchFall : Signal dom Bool :=
    Signal.map (BitVec.extractLsb' 31 1 ·) (fallThreshold - absPitch)
      === (Signal.pure 1#1 : Signal dom (BitVec 1))

  let isFalling : Signal dom Bool :=
    Signal.mux rollFall (Signal.pure true : Signal dom Bool) pitchFall

  -- Fall direction code: 1=forward, 2=backward, 3=left, 4=right
  let code : Signal dom (BitVec 4) :=
    Signal.mux pitchFall
      (Signal.mux pitchNeg
        (Signal.pure 2#4 : Signal dom (BitVec 4))   -- backward
        (Signal.pure 1#4 : Signal dom (BitVec 4)))  -- forward
      (Signal.mux rollFall
        (Signal.mux rollNeg
          (Signal.pure 4#4 : Signal dom (BitVec 4))   -- right
          (Signal.pure 3#4 : Signal dom (BitVec 4)))  -- left
        (Signal.pure 0#4 : Signal dom (BitVec 4)))    -- stable

  bundle2 isFalling code

/-- Complete safety controller.

    Inputs:
      servoCmd     — raw servo command from motion controller
      measuredTorque — actual joint torque (from sensor)
      roll, pitch  — body attitude
      eStop        — emergency stop button
      torqueLimit  — maximum allowed torque
      collisionThreshold — torque spike threshold
      fallThreshold — maximum tilt angle

    Returns:
      safeServoCmd — limited/filtered servo command
      eStopActive  — E-stop is engaged
      isFalling    — fall detected
      fallDir      — fall direction code
      isCollision  — collision detected -/
def safetyController
    (servoCmd : Signal dom (BitVec 32))
    (measuredTorque : Signal dom (BitVec 32))
    (roll pitch : Signal dom (BitVec 32))
    (eStop : Signal dom Bool)
    (torqueLimit collisionThreshold fallThreshold : Signal dom (BitVec 32))
    : Signal dom (BitVec 32 × (Bool × (Bool × (BitVec 4 × Bool)))) :=
  -- Torque limiting
  let limited := torqueLimiter servoCmd torqueLimit

  -- Collision detection
  let collOut := collisionDetector measuredTorque collisionThreshold
  let isCollision := Signal.fst collOut

  -- Fall detection
  let fallOut := fallDetector roll pitch fallThreshold
  let isFalling := Signal.fst fallOut
  let fallDir := Signal.snd fallOut

  -- E-stop: zero all commands
  -- Falling: go to protective pose (center position = 0x8000)
  let protectiveCmd := (Signal.pure 0x00008000#32 : Signal dom (BitVec 32))  -- center
  let zeroCmd := (Signal.pure 0#32 : Signal dom (BitVec 32))

  let safeCmd := Signal.mux eStop zeroCmd
    (Signal.mux isFalling protectiveCmd
      (Signal.mux isCollision
        (Signal.map (fun v => BitVec.sshiftRight v 2) limited)  -- soft on collision
        limited))

  bundle2 safeCmd (bundle2 eStop (bundle2 isFalling (bundle2 fallDir isCollision)))

end Sparkle.IP.Humanoid
