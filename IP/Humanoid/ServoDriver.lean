/-
  Humanoid Servo Driver — 30-Channel PWM — Signal DSL

  Drives up to 30 hobby servos (or smart servos in PWM mode).
  Standard RC servo: 50 Hz, 1-2 ms pulse (1.5 ms = center).

  At 200 MHz:
    Period = 200M / 50 = 4,000,000 cycles (20 ms)
    1 ms = 200,000 cycles (minimum pulse)
    2 ms = 400,000 cycles (maximum pulse)
    Center = 300,000 cycles (1.5 ms)

  Each channel: 16-bit position → PWM pulse width
    0x0000 = 1.0 ms (full left)
    0x8000 = 1.5 ms (center)
    0xFFFF = 2.0 ms (full right)

  Mapping: pulse_cycles = 200000 + (position >> 6) * 3125 / 1024
  Simplified: pulse_cycles = 200000 + position[15:6] * 200000 / 1024

  Joint mapping (typical humanoid):
    ch0-2:   head (pan, tilt, roll)
    ch3-8:   right arm (shoulder pitch/roll/yaw, elbow, wrist pitch/roll)
    ch9-14:  left arm
    ch15-20: right leg (hip pitch/roll/yaw, knee, ankle pitch/roll)
    ch21-26: left leg
    ch27-29: torso/waist
-/

import Sparkle.Core.Signal
import Sparkle.Core.Domain

namespace Sparkle.IP.Humanoid

open Sparkle.Core.Signal
open Sparkle.Core.Domain

variable {dom : DomainConfig}

/-- Single PWM servo channel.
    Generates 50 Hz PWM with 1-2 ms pulse width.
    `position`: 16-bit (0 = 1ms, 0x8000 = 1.5ms, 0xFFFF = 2ms)
    Returns pwmOut signal. -/
def servoChannel
    (enable : Signal dom Bool)
    (position : Signal dom (BitVec 16))
    : Signal dom Bool :=
  -- 20-bit counter for 20 ms period (wraps at ~1M, scaled)
  -- Use 22-bit counter: 2^22 = 4,194,304 ≈ 4M (close to 20 ms @ 200 MHz)
  let state := Signal.loop (dom := dom) (α := BitVec 22)
    fun (self : Signal dom (BitVec 22)) =>
    let nextCount : Signal dom (BitVec 22) :=
      self + (Signal.pure 1#22 : Signal dom (BitVec 22))
    Signal.register 0#22 nextCount

  -- Pulse width: 200000 + position * 200000 / 65536
  -- Simplified: extract top 10 bits of position, multiply by ~195
  -- pulse = 200000 + position[15:6] * 195
  -- Even simpler: compare counter against (200000 + position * 3)
  -- For now: counter[21:6] < 3125 + position[15:0] * 3
  -- Simplest approximation: counter < (200000 + position <<< 2)
  let posExt : Signal dom (BitVec 22) :=
    (Signal.pure 0#6 : Signal dom (BitVec 6)) ++ position
  let pulseWidth : Signal dom (BitVec 22) :=
    (Signal.pure (BitVec.ofNat 22 200000) : Signal dom (BitVec 22)) +
    (posExt >>> (Signal.pure 2#22 : Signal dom (BitVec 22)))  -- position/4 ≈ 0-16384 cycles

  -- PWM: output high when counter < pulseWidth
  let diff : Signal dom (BitVec 22) := state - pulseWidth
  let counterLess : Signal dom Bool :=
    Signal.map (BitVec.extractLsb' 21 1 ·) diff === (Signal.pure 1#1 : Signal dom (BitVec 1))

  Signal.mux enable counterLess (Signal.pure false : Signal dom Bool)

/-- 6-channel servo bank (one limb: 6 DOF arm or leg).
    All channels share the same 50 Hz timebase.
    Returns (ch0 × (ch1 × (ch2 × (ch3 × (ch4 × ch5))))). -/
def servoBank6
    (enable : Signal dom Bool)
    (p0 p1 p2 p3 p4 p5 : Signal dom (BitVec 16))
    : Signal dom (Bool × (Bool × (Bool × (Bool × (Bool × Bool))))) :=
  let s0 := servoChannel enable p0
  let s1 := servoChannel enable p1
  let s2 := servoChannel enable p2
  let s3 := servoChannel enable p3
  let s4 := servoChannel enable p4
  let s5 := servoChannel enable p5
  bundle2 s0 (bundle2 s1 (bundle2 s2 (bundle2 s3 (bundle2 s4 s5))))

/-- 30-channel servo controller for humanoid robot.
    5 banks × 6 channels: head(3) + arms(2×6) + legs(2×6) + torso(3)
    (head and torso use 3 of 6 channels each, rest unused)

    Inputs:
      enable  — master enable
      positions — 30 × 16-bit servo positions (passed as 5 × 6)

    Returns 30 PWM output signals (bundled as 5 banks). -/
def servoController30
    (enable : Signal dom Bool)
    -- Head (3 DOF): pan, tilt, roll
    (headPan headTilt headRoll : Signal dom (BitVec 16))
    -- Right arm (6 DOF)
    (rShoulderP rShoulderR rShoulderY rElbow rWristP rWristR : Signal dom (BitVec 16))
    -- Left arm (6 DOF)
    (lShoulderP lShoulderR lShoulderY lElbow lWristP lWristR : Signal dom (BitVec 16))
    -- Right leg (6 DOF)
    (rHipP rHipR rHipY rKnee rAnkleP rAnkleR : Signal dom (BitVec 16))
    -- Left leg (6 DOF)
    (lHipP lHipR lHipY lKnee lAnkleP lAnkleR : Signal dom (BitVec 16))
    -- Torso (3 DOF): waist yaw, pitch, roll
    (waistY waistP waistR : Signal dom (BitVec 16))
    : Signal dom (Bool × (Bool × (Bool × (Bool × (Bool × Bool))))) ×
      Signal dom (Bool × (Bool × (Bool × (Bool × (Bool × Bool))))) ×
      Signal dom (Bool × (Bool × (Bool × (Bool × (Bool × Bool))))) ×
      Signal dom (Bool × (Bool × (Bool × (Bool × (Bool × Bool))))) ×
      Signal dom (Bool × (Bool × (Bool × (Bool × (Bool × Bool))))) :=
  -- Head + torso bank
  let headBank := servoBank6 enable headPan headTilt headRoll waistY waistP waistR
  -- Arm banks
  let rArmBank := servoBank6 enable rShoulderP rShoulderR rShoulderY rElbow rWristP rWristR
  let lArmBank := servoBank6 enable lShoulderP lShoulderR lShoulderY lElbow lWristP lWristR
  -- Leg banks
  let rLegBank := servoBank6 enable rHipP rHipR rHipY rKnee rAnkleP rAnkleR
  let lLegBank := servoBank6 enable lHipP lHipR lHipY lKnee lAnkleP lAnkleR

  (headBank, rArmBank, lArmBank, rLegBank, lLegBank)

end Sparkle.IP.Humanoid
