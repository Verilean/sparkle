/-
  Position & Velocity & Altitude Controller — Signal DSL

  Outer control loops that sit between the path planner and the attitude
  PID (ClassicalFC). Converts waypoint targets into attitude setpoints
  and throttle commands.

  Control stack (fully cascaded):
    path planner → position P → velocity PID → attitude setpoint + throttle
                                                      ↓
                                               classicalFC (attitude PID)
                                                      ↓
                                               motor mixer

  All arithmetic is signed Q16.16 via `fixMulS` from ClassicalFC.
-/

import Sparkle.Core.Signal
import Sparkle.Core.Domain
import IP.Drone.ClassicalFC  -- fixMulS, clampSym, signExt32to64

namespace Sparkle.IP.Drone

open Sparkle.Core.Signal
open Sparkle.Core.Domain

variable {dom : DomainConfig}

-- ============================================================
-- Position P controller (one horizontal axis)
-- ============================================================

/-- Position P: posErr → velocity setpoint.
    velSetpoint = Kp_pos × (targetPos - currentPos), clamped to ±maxVel.

    Kp_pos ≈ 1.0 in Q16.16 = 0x00010000
    maxVel ≈ 5.0 m/s in Q16.16 = 0x00050000 -/
def positionP
    (targetPos currentPos : Signal dom (BitVec 32))
    : Signal dom (BitVec 32) :=
  let kpPos   : Signal dom (BitVec 32) := (Signal.pure 0x00010000#32 : Signal dom (BitVec 32))
  let maxVel  : Signal dom (BitVec 32) := (Signal.pure 0x00050000#32 : Signal dom (BitVec 32))
  let posErr := targetPos - currentPos
  let velSet := fixMulS kpPos posErr
  clampSym velSet maxVel

-- ============================================================
-- Velocity PID (one horizontal axis)
-- ============================================================

/-- Velocity PID: velErr → attitude angle setpoint.
    The velocity error maps to a desired tilt angle (pitch for X, roll for Y).

    Kp_vel ≈ 0.15  = 0x00002666
    Ki_vel ≈ 0.02  = 0x0000051E
    Kd_vel ≈ 0.01  = 0x0000028F
    iLimit  ≈ 0.2 rad = 0x00003333
    outLimit ≈ 0.5 rad (~28°) = 0x00008000 -/
def velocityPID
    (velSetpoint currentVel : Signal dom (BitVec 32))
    : Signal dom (BitVec 32) :=
  let kp     : Signal dom (BitVec 32) := (Signal.pure 0x00002666#32 : Signal dom (BitVec 32))
  let ki     : Signal dom (BitVec 32) := (Signal.pure 0x0000051E#32 : Signal dom (BitVec 32))
  let kd     : Signal dom (BitVec 32) := (Signal.pure 0x0000028F#32 : Signal dom (BitVec 32))
  let iLimit : Signal dom (BitVec 32) := (Signal.pure 0x00003333#32 : Signal dom (BitVec 32))
  let oLimit : Signal dom (BitVec 32) := (Signal.pure 0x00008000#32 : Signal dom (BitVec 32))
  ratePID velSetpoint currentVel kp ki kd iLimit oLimit

-- ============================================================
-- Altitude PID
-- ============================================================

/-- Altitude PID: altErr → throttle adjustment (added to hover baseline).
    Output is a throttle delta in Q16.16, ±0.3 range.

    Kp_alt ≈ 0.3   = 0x00004CCC
    Ki_alt ≈ 0.05  = 0x00000CCC
    Kd_alt ≈ 0.1   = 0x00001999
    iLimit  ≈ 0.2  = 0x00003333
    outLimit ≈ 0.3 = 0x00004CCC -/
def altitudePID
    (targetAlt currentAlt : Signal dom (BitVec 32))
    : Signal dom (BitVec 32) :=
  let kp     : Signal dom (BitVec 32) := (Signal.pure 0x00004CCC#32 : Signal dom (BitVec 32))
  let ki     : Signal dom (BitVec 32) := (Signal.pure 0x00000CCC#32 : Signal dom (BitVec 32))
  let kd     : Signal dom (BitVec 32) := (Signal.pure 0x00001999#32 : Signal dom (BitVec 32))
  let iLimit : Signal dom (BitVec 32) := (Signal.pure 0x00003333#32 : Signal dom (BitVec 32))
  let oLimit : Signal dom (BitVec 32) := (Signal.pure 0x00004CCC#32 : Signal dom (BitVec 32))
  ratePID targetAlt currentAlt kp ki kd iLimit oLimit

-- ============================================================
-- Full navigation controller
-- ============================================================

/-- Navigation controller: waypoint → attitude setpoints + throttle.

    Inputs:
      targetX, targetY  — waypoint position (Q16.16 meters, local frame)
      targetAlt          — target altitude (Q16.16 meters, positive = up)
      currentX, currentY — current GPS position (Q16.16 meters, local)
      currentAlt         — current altitude (Q16.16 meters)
      velX, velY, velZ   — current velocity (Q16.16 m/s)

    Outputs:
      pitchSet  — pitch angle setpoint (Q16.16 rad, + = nose down = forward)
      rollSet   — roll angle setpoint (Q16.16 rad, + = right = move right)
      yawRateSet — yaw rate setpoint (0 for now)
      throttleCmd — total throttle command (Q16.16, 0 to 1)
-/
def navigationController
    (targetX targetY targetAlt : Signal dom (BitVec 32))
    (currentX currentY currentAlt : Signal dom (BitVec 32))
    (velX velY velZ : Signal dom (BitVec 32))
    : Signal dom (BitVec 32 × (BitVec 32 × (BitVec 32 × BitVec 32))) :=
  -- Position → velocity setpoints
  let velXset := positionP targetX currentX
  let velYset := positionP targetY currentY

  -- Velocity → attitude setpoints
  -- Forward velocity (X) → pitch: to fly forward, pitch nose down (negative pitch)
  -- So pitchSet = -velocityPID(velXset, velX)
  let pitchDelta := velocityPID velXset velX
  let pitchSet : Signal dom (BitVec 32) :=
    (Signal.pure 0#32 : Signal dom (BitVec 32)) - pitchDelta
  -- Lateral velocity (Y) → roll: to fly right, roll right (positive roll)
  let rollSet := velocityPID velYset velY

  -- Altitude → throttle
  let altDelta := altitudePID targetAlt currentAlt
  -- Base hover throttle + altitude correction
  let hoverThrottle : Signal dom (BitVec 32) :=
    (Signal.pure 0x00008000#32 : Signal dom (BitVec 32))
  let throttleCmd := hoverThrottle + altDelta

  -- Yaw rate: 0 (hold heading)
  let yawRateSet : Signal dom (BitVec 32) := (Signal.pure 0#32 : Signal dom (BitVec 32))

  bundle2 pitchSet (bundle2 rollSet (bundle2 yawRateSet throttleCmd))

end Sparkle.IP.Drone
