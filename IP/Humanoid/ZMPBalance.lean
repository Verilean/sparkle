/-
  ZMP Balance Controller — Signal DSL

  Zero Moment Point (ZMP) based balance control for bipedal walking.

  ZMP: the point on the ground where the net moment of all forces
  (gravity + inertia) is zero. If ZMP stays inside the support
  polygon (foot contact area), the robot doesn't fall.

  Inputs:
    - 4 foot pressure sensors per foot (8 total) → ZMP position
    - IMU (roll, pitch) → body tilt
    - Target ZMP from gait planner

  Output:
    - Ankle torque corrections (pitch + roll per foot)
    - Hip compensation torques

  Control law (simplified):
    ankle_correction = Kp × (target_zmp - actual_zmp) + Kd × zmp_velocity

  All Q16.16 fixed-point, fully combinational.
-/

import Sparkle.Core.Signal
import Sparkle.Core.Domain

namespace Sparkle.IP.Humanoid

open Sparkle.Core.Signal
open Sparkle.Core.Domain

variable {dom : DomainConfig}

/-- Fixed-point multiply: (a × b) >> 16. -/
def fmul (a b : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  let aExt : Signal dom (BitVec 64) :=
    a ++ (Signal.pure 0#32 : Signal dom (BitVec 32))
  let bExt : Signal dom (BitVec 64) :=
    b ++ (Signal.pure 0#32 : Signal dom (BitVec 32))
  let prod := aExt * bExt
  Signal.map (BitVec.extractLsb' 16 32 ·) prod

/-- Compute ZMP from 4 foot pressure sensors.
    Sensors at corners: front-left, front-right, back-left, back-right.
    ZMP_x = (Ffr + Fbr - Ffl - Fbl) × footWidth / (2 × Ftotal)
    ZMP_y = (Ffl + Ffr - Fbl - Fbr) × footLength / (2 × Ftotal)

    Simplified: ZMP ≈ weighted average of sensor positions.
    Returns (zmpX × zmpY). -/
def computeZMP
    (frontLeft frontRight backLeft backRight : Signal dom (BitVec 32))
    (footWidth footLength : Signal dom (BitVec 32))
    : Signal dom (BitVec 32 × BitVec 32) :=
  -- Total force
  let total := (frontLeft + frontRight) + (backLeft + backRight)

  -- Moment about center
  -- X moment: right sensors positive, left sensors negative
  let momentX := (frontRight + backRight) - (frontLeft + backLeft)
  -- Y moment: front sensors positive, back sensors negative
  let momentY := (frontLeft + frontRight) - (backLeft + backRight)

  -- ZMP = moment × footSize / total (simplified: moment / 4 for equal foot size)
  -- Avoid division: approximate as moment >>> 2
  let zmpX := Signal.map (fun v => BitVec.sshiftRight v 2) momentX
  let zmpY := Signal.map (fun v => BitVec.sshiftRight v 2) momentY

  bundle2 zmpX zmpY

/-- PD controller for one axis.
    output = Kp × error + Kd × (error - prevError)
    Returns (output × prevError_updated). -/
def pdController
    (kp kd : Signal dom (BitVec 32))
    (target actual : Signal dom (BitVec 32))
    : Signal dom (BitVec 32 × BitVec 32) :=
  let state := Signal.loop (dom := dom) (α := BitVec 32)
    fun (prevError : Signal dom (BitVec 32)) =>
    let error := target - actual
    let derivative := error - prevError
    let pTerm := fmul kp error
    let dTerm := fmul kd derivative
    let output := pTerm + dTerm
    -- Store error for next cycle
    Signal.register 0#32 error

  let error := target - actual
  let prevError := state
  let derivative := error - prevError
  let pTerm := fmul kp error
  let dTerm := fmul kd derivative
  let output := pTerm + dTerm

  bundle2 output error

/-- Full ZMP balance controller for bipedal robot.

    Inputs:
      -- Right foot pressure sensors (4 corners)
      rfFL, rfFR, rfBL, rfBR — front-left/right, back-left/right
      -- Left foot pressure sensors
      lfFL, lfFR, lfBL, lfBR
      -- Target ZMP from gait planner
      targetZmpX, targetZmpY
      -- PD gains
      kp, kd

    Returns:
      rAnklePitchCorr  — right ankle pitch correction
      rAnkleRollCorr   — right ankle roll correction
      lAnklePitchCorr  — left ankle pitch correction
      lAnkleRollCorr   — left ankle roll correction
      actualZmpX       — measured ZMP X (for monitoring)
      actualZmpY       — measured ZMP Y -/
def zmpBalanceController
    -- Right foot sensors
    (rfFL rfFR rfBL rfBR : Signal dom (BitVec 32))
    -- Left foot sensors
    (lfFL lfFR lfBL lfBR : Signal dom (BitVec 32))
    -- Target ZMP
    (targetZmpX targetZmpY : Signal dom (BitVec 32))
    -- PD gains
    (kp kd : Signal dom (BitVec 32))
    : Signal dom (BitVec 32 × (BitVec 32 × (BitVec 32 × (BitVec 32 × (BitVec 32 × BitVec 32))))) :=
  let footWidth := (Signal.pure 0x00080000#32 : Signal dom (BitVec 32))   -- 8 cm
  let footLength := (Signal.pure 0x00100000#32 : Signal dom (BitVec 32))  -- 16 cm

  -- Compute ZMP for each foot
  let rFootZMP := computeZMP rfFL rfFR rfBL rfBR footWidth footLength
  let lFootZMP := computeZMP lfFL lfFR lfBL lfBR footWidth footLength

  -- Combined ZMP: average of both feet (when both on ground)
  let rZmpX := Signal.fst rFootZMP
  let rZmpY := Signal.snd rFootZMP
  let lZmpX := Signal.fst lFootZMP
  let lZmpY := Signal.snd lFootZMP

  let actualZmpX := Signal.map (fun v => BitVec.sshiftRight v 1) (rZmpX + lZmpX)
  let actualZmpY := Signal.map (fun v => BitVec.sshiftRight v 1) (rZmpY + lZmpY)

  -- PD control: correction = Kp × (target - actual) + Kd × derivative
  let xCorrection := Signal.fst (pdController kp kd targetZmpX actualZmpX)
  let yCorrection := Signal.fst (pdController kp kd targetZmpY actualZmpY)

  -- Map corrections to ankle joints:
  -- X correction → ankle roll (lateral balance)
  -- Y correction → ankle pitch (fore-aft balance)
  let rAnklePitch := yCorrection
  let rAnkleRoll := xCorrection
  let lAnklePitch := yCorrection
  let lAnkleRoll := xCorrection

  bundle2 rAnklePitch (bundle2 rAnkleRoll
    (bundle2 lAnklePitch (bundle2 lAnkleRoll
      (bundle2 actualZmpX actualZmpY))))

end Sparkle.IP.Humanoid
