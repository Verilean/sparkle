/-
  Humanoid Robot SoC — Signal DSL

  Complete system-on-chip for bipedal humanoid robot:

    SPI Encoders (30ch) → State + IK → Neural Motion → Safety → PWM Servos (30ch)
    SPI IMU → ZMP Balance → ankle corrections → merge with motion
    Gait Generator → foot targets → leg IK
    E-stop + fall detection → safety override

  Control loop @ 1 kHz:
    1. Read 30 encoders + IMU (SPI, ~77 μs)
    2. Gait generator provides foot targets
    3. IK computes joint angles from targets
    4. Neural motion + ZMP balance computes corrections
    5. Safety limits and collision check
    6. Output to 30 servos (PWM)

  Target: Zynq-7020 (53,200 LUT, 220 DSP)
-/

import Sparkle.Core.Signal
import Sparkle.Core.Domain
import IP.Humanoid.ServoDriver
import IP.Humanoid.Encoder
import IP.Humanoid.NeuralMotion
import IP.Humanoid.ZMPBalance
import IP.Humanoid.InverseKinematics
import IP.Humanoid.GaitGenerator
import IP.Humanoid.SafetyController
import IP.Drone.SPIIMU

namespace Sparkle.IP.Humanoid

open Sparkle.Core.Signal
open Sparkle.Core.Domain
open Sparkle.IP.Drone

variable {dom : DomainConfig}

/-- Humanoid robot SoC — simplified 6-DOF version for synthesis test.
    Full 30-DOF is structurally identical (replicate per limb).

    External pins:
      encoderMiso   — shared SPI MISO from encoder chain
      imuMiso       — SPI MISO from IMU
      eStop         — emergency stop button
      walkEnable    — enable walking
      4 × footPressure — foot pressure sensors (simplified to 4)

    Returns:
      6 × servo PWM outputs
      encoderSck, encoderMosi, encoderCsN — SPI to encoders
      imuSck, imuMosi, imuCsN — SPI to IMU
      isFalling, fallDir — safety status -/
def humanoidSoC6DOF
    (encoderMiso : Signal dom Bool)
    (imuMiso : Signal dom Bool)
    (eStop : Signal dom Bool)
    (walkEnable : Signal dom Bool)
    -- Foot pressure (4 sensors, simplified)
    (footFL footFR footBL footBR : Signal dom (BitVec 32))
    : Signal dom (
        Bool ×           -- servo0
        (Bool ×          -- servo1
        (Bool ×          -- servo2
        (Bool ×          -- servo3
        (Bool ×          -- servo4
        (Bool ×          -- servo5
        (Bool ×          -- encoderSck
        (Bool ×          -- imuSck
        (Bool ×          -- isFalling
        BitVec 4         -- fallDir
        ))))))))) :=

  -- ================================================================
  -- 1. Sensor reads (1 kHz trigger)
  -- ================================================================
  let trigger := Signal.loop (dom := dom) (α := BitVec 32 × Bool)
    fun (self : Signal dom (BitVec 32 × Bool)) =>
    let counter := Signal.fst self
    let atRate : Signal dom Bool :=
      counter === (Signal.pure 199999#32 : Signal dom (BitVec 32))
    let nextC : Signal dom (BitVec 32) :=
      Signal.mux atRate (Signal.pure 0#32 : Signal dom (BitVec 32))
        (counter + (Signal.pure 1#32 : Signal dom (BitVec 32)))
    bundle2 (Signal.register 0#32 nextC) (Signal.register false atRate)
  let sensorGo := Signal.snd trigger

  -- Encoders (6 channels for test)
  let encOut := multiEncoderReader 5#8 sensorGo encoderMiso
  let encAngle := Signal.fst encOut
  let er1 := Signal.snd encOut
  let _encChIdx := Signal.fst er1
  let er2 := Signal.snd er1
  let _encDone := Signal.fst er2
  let er3 := Signal.snd er2
  let encSck := Signal.fst er3
  let er4 := Signal.snd er3
  let _encMosi := Signal.fst er4
  let _encCsActive := Signal.snd er4

  -- IMU
  let imuOut := spiIMUDriver sensorGo imuMiso
  let imuSck := Signal.fst imuOut
  let ir1 := Signal.snd imuOut
  let _imuMosi := Signal.fst ir1
  let ir2 := Signal.snd ir1
  let _imuCsN := Signal.fst ir2
  let ir3 := Signal.snd ir2
  let accelX := Signal.fst ir3
  let ir4 := Signal.snd ir3
  let accelY := Signal.fst ir4
  let ir5 := Signal.snd ir4
  let accelZ := Signal.fst ir5
  let ir6 := Signal.snd ir5
  let gyroX := Signal.fst ir6
  let ir7 := Signal.snd ir6
  let gyroY := Signal.fst ir7
  let ir8 := Signal.snd ir7
  let gyroZ := Signal.fst ir8
  let _imuValid := Signal.snd ir8

  -- ================================================================
  -- 2. Gait generator
  -- ================================================================
  let stepLen := (Signal.pure 0x00140000#32 : Signal dom (BitVec 32))  -- 20 cm
  let stepH := (Signal.pure 0x00050000#32 : Signal dom (BitVec 32))    -- 5 cm
  let gaitOut := gaitGenerator walkEnable stepLen stepH 200000#16
  let rFootX := Signal.fst gaitOut
  let gr1 := Signal.snd gaitOut
  let rFootZ := Signal.fst gr1

  -- ================================================================
  -- 3. IK: foot target → joint angles
  -- ================================================================
  let upperLen := (Signal.pure 0x001E0000#32 : Signal dom (BitVec 32))  -- 30 cm
  let lowerLen := (Signal.pure 0x001E0000#32 : Signal dom (BitVec 32))  -- 30 cm
  let legIK := limbIK6DOF rFootX (Signal.pure 0#32 : Signal dom (BitVec 32)) rFootZ upperLen lowerLen
  let _ikJ0 := Signal.fst legIK

  -- ================================================================
  -- 4. ZMP Balance
  -- ================================================================
  let kp := (Signal.pure 0x00010000#32 : Signal dom (BitVec 32))
  let kd := (Signal.pure 0x00002000#32 : Signal dom (BitVec 32))
  let zmpOut := zmpBalanceController footFL footFR footBL footBR
    footFL footFR footBL footBR  -- same foot for both (simplified)
    (Signal.pure 0#32 : Signal dom (BitVec 32)) (Signal.pure 0#32 : Signal dom (BitVec 32))
    kp kd
  let _ankleCorr := Signal.fst zmpOut

  -- ================================================================
  -- 5. Neural motion controller
  -- ================================================================
  let ax32 : Signal dom (BitVec 32) := accelX ++ (Signal.pure 0#16 : Signal dom (BitVec 16))
  let ay32 : Signal dom (BitVec 32) := accelY ++ (Signal.pure 0#16 : Signal dom (BitVec 16))
  let az32 : Signal dom (BitVec 32) := accelZ ++ (Signal.pure 0#16 : Signal dom (BitVec 16))
  let gx32 : Signal dom (BitVec 32) := gyroX ++ (Signal.pure 0#16 : Signal dom (BitVec 16))
  let gy32 : Signal dom (BitVec 32) := gyroY ++ (Signal.pure 0#16 : Signal dom (BitVec 16))
  let gz32 : Signal dom (BitVec 32) := gyroZ ++ (Signal.pure 0#16 : Signal dom (BitVec 16))
  let encAngle32 : Signal dom (BitVec 32) :=
    encAngle ++ (Signal.pure 0#18 : Signal dom (BitVec 18))

  let motionOut := motionController6DOF
    encAngle32 encAngle32 encAngle32 encAngle32 encAngle32 encAngle32
    ax32 ay32 az32 gx32 gy32 gz32
  let servo0cmd := Signal.fst motionOut

  -- ================================================================
  -- 6. Safety
  -- ================================================================
  let roll32 := ax32   -- simplified: use accel as roll proxy
  let pitch32 := ay32
  let tLim := (Signal.pure 0x00100000#32 : Signal dom (BitVec 32))
  let cThr := (Signal.pure 0x00010000#32 : Signal dom (BitVec 32))
  let fThr := (Signal.pure 0x00300000#32 : Signal dom (BitVec 32))  -- ~0.75 rad
  let safeOut := safetyController servo0cmd (Signal.pure 0#32 : Signal dom (BitVec 32))
    roll32 pitch32 eStop tLim cThr fThr
  let safeCmd := Signal.fst safeOut
  let sr1 := Signal.snd safeOut
  let _eStopActive := Signal.fst sr1
  let sr2 := Signal.snd sr1
  let isFalling := Signal.fst sr2
  let sr3 := Signal.snd sr2
  let fallDir := Signal.fst sr3

  -- ================================================================
  -- 7. Servo output (6 channels)
  -- ================================================================
  let enable := Signal.mux eStop (Signal.pure false : Signal dom Bool) (Signal.pure true : Signal dom Bool)
  let servoPos := Signal.map (BitVec.extractLsb' 16 16 ·) safeCmd
  let servos := servoBank6 enable servoPos servoPos servoPos servoPos servoPos servoPos
  let s0 := Signal.fst servos
  let sv1 := Signal.snd servos
  let s1 := Signal.fst sv1
  let sv2 := Signal.snd sv1
  let s2 := Signal.fst sv2
  let sv3 := Signal.snd sv2
  let s3 := Signal.fst sv3
  let sv4 := Signal.snd sv3
  let s4 := Signal.fst sv4
  let s5 := Signal.snd sv4

  -- ================================================================
  -- Output
  -- ================================================================
  bundle2 s0 (bundle2 s1 (bundle2 s2 (bundle2 s3 (bundle2 s4 (bundle2 s5
    (bundle2 encSck (bundle2 imuSck (bundle2 isFalling fallDir))))))))

end Sparkle.IP.Humanoid
