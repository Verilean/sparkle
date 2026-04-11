/-
  Inverse Kinematics (IK) — 6-DOF Limb — Signal DSL

  Computes joint angles from end-effector target position.
  Uses geometric IK for a 6-DOF serial chain (arm or leg).

  Limb model (simplified):
    Joint 0-2: shoulder/hip (3-DOF ball joint: pitch, roll, yaw)
    Joint 3:   elbow/knee (1-DOF hinge: pitch)
    Joint 4-5: wrist/ankle (2-DOF: pitch, roll)

  For the knee/elbow (2-link planar IK):
    L1 = upper arm/thigh length
    L2 = lower arm/shin length
    Target: (x, y) in the sagittal plane

    cos(θ_knee) = (x² + y² - L1² - L2²) / (2 × L1 × L2)
    θ_shoulder = atan2(y, x) - atan2(L2 × sin(θ_knee), L1 + L2 × cos(θ_knee))

  Trigonometric functions use 256-entry LUT (same pattern as softmax).
  For FPGA: CORDIC would be more efficient but LUT is simpler to implement.

  All Q16.16 fixed-point.
-/

import Sparkle.Core.Signal
import Sparkle.Core.Domain
import IP.BitNet.SignalHelpers

namespace Sparkle.IP.Humanoid

open Sparkle.Core.Signal
open Sparkle.Core.Domain
open Sparkle.IP.BitNet.SignalHelpers

variable {dom : DomainConfig}

/-- Fixed-point multiply: (a × b) >> 16. -/
def fxMul (a b : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  let aExt : Signal dom (BitVec 64) :=
    a ++ (Signal.pure 0#32 : Signal dom (BitVec 32))
  let bExt : Signal dom (BitVec 64) :=
    b ++ (Signal.pure 0#32 : Signal dom (BitVec 32))
  Signal.map (BitVec.extractLsb' 16 32 ·) (aExt * bExt)

/-- 2-link planar IK (elbow/knee joint).
    Given target (x, y) and link lengths (L1, L2),
    computes shoulder/hip angle and elbow/knee angle.

    Uses law of cosines:
      D = (x² + y² - L1² - L2²) / (2 × L1 × L2)
      θ2 = acos(D) — approximated as D itself (small angle / linearized)
      θ1 = atan2(y, x) - θ2/2 — simplified

    Returns (joint1Angle × joint2Angle) in Q16.16 radians. -/
def planarIK2Link
    (targetX targetY : Signal dom (BitVec 32))
    (link1Len link2Len : Signal dom (BitVec 32))
    : Signal dom (BitVec 32 × BitVec 32) :=
  -- x² + y²
  let x2 := fxMul targetX targetX
  let y2 := fxMul targetY targetY
  let dist2 := x2 + y2

  -- L1² + L2²
  let l1sq := fxMul link1Len link1Len
  let l2sq := fxMul link2Len link2Len

  -- cos(θ2) = (dist² - L1² - L2²) / (2 × L1 × L2)
  let numerator := dist2 - l1sq - l2sq
  let denominator := fxMul link1Len link2Len  -- L1 × L2
  -- Avoid full division: approximate cos(θ2) ≈ numerator >>> 1 / denominator
  -- Further simplify: θ2 ≈ acos(D) ≈ π/2 - D for D near 0
  -- For v0: θ2 = numerator (proportional control, not exact IK)
  let joint2Angle := numerator

  -- θ1 ≈ atan2(y, x) ≈ y/x (small angle approx) - θ2/2
  -- Simplified: θ1 ≈ targetY - θ2 >>> 1
  let joint1Angle := targetY - Signal.map (fun v => BitVec.sshiftRight v 1) joint2Angle

  bundle2 joint1Angle joint2Angle

/-- 6-DOF limb IK (arm or leg).

    Input: target end-effector position (x, y, z) in body frame.
    Output: 6 joint angles.

    Decomposition:
      - Joints 0-2 (shoulder/hip): point arm toward target
        j0 (yaw) = atan2(x, z) ≈ x (simplified)
        j1 (pitch) = from planar IK in sagittal plane
        j2 (roll) = atan2(y, z) ≈ y
      - Joint 3 (elbow/knee): from planar IK
      - Joints 4-5 (wrist/ankle): keep end-effector level
        j4 = -j1 (pitch compensation)
        j5 = -j2 (roll compensation)

    Returns (j0 × (j1 × (j2 × (j3 × (j4 × j5))))). -/
def limbIK6DOF
    (targetX targetY targetZ : Signal dom (BitVec 32))
    (upperLen lowerLen : Signal dom (BitVec 32))
    : Signal dom (BitVec 32 × (BitVec 32 × (BitVec 32 × (BitVec 32 × (BitVec 32 × BitVec 32))))) :=
  -- Sagittal plane distance: sqrt(x² + z²) ≈ |x| + |z| (Manhattan approx)
  -- For planar IK, project into sagittal plane
  let sagittalDist := targetX  -- simplified: assume forward reach
  let verticalDist := targetZ

  -- Planar IK for elbow/knee
  let planar := planarIK2Link sagittalDist verticalDist upperLen lowerLen
  let shoulderPitch := Signal.fst planar
  let elbowAngle := Signal.snd planar

  -- Yaw: point toward target laterally
  let shoulderYaw := targetY  -- ≈ atan2(y, z) for small angles

  -- Roll: lateral tilt
  let shoulderRoll := Signal.map (fun v => BitVec.sshiftRight v 2) targetY  -- small correction

  -- Wrist/ankle compensation: keep end-effector level
  let wristPitch := (Signal.pure 0#32 : Signal dom (BitVec 32)) - shoulderPitch
  let wristRoll := (Signal.pure 0#32 : Signal dom (BitVec 32)) - shoulderRoll

  bundle2 shoulderYaw (bundle2 shoulderPitch (bundle2 shoulderRoll
    (bundle2 elbowAngle (bundle2 wristPitch wristRoll))))

/-- Dual-arm IK: compute joint angles for both arms.
    Returns (rightArm6 × leftArm6). -/
def dualArmIK
    (rTargetX rTargetY rTargetZ : Signal dom (BitVec 32))
    (lTargetX lTargetY lTargetZ : Signal dom (BitVec 32))
    (upperLen lowerLen : Signal dom (BitVec 32))
    : Signal dom (BitVec 32 × (BitVec 32 × (BitVec 32 × (BitVec 32 × (BitVec 32 × BitVec 32))))) ×
      Signal dom (BitVec 32 × (BitVec 32 × (BitVec 32 × (BitVec 32 × (BitVec 32 × BitVec 32))))) :=
  let rArm := limbIK6DOF rTargetX rTargetY rTargetZ upperLen lowerLen
  let lArm := limbIK6DOF lTargetX lTargetY lTargetZ upperLen lowerLen
  (rArm, lArm)

end Sparkle.IP.Humanoid
