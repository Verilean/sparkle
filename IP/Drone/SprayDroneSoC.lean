/-
  Agricultural Spray Drone SoC — Signal DSL

  Complete drone system-on-chip for autonomous crop spraying:

    Sensors:
      SPI IMU → State Estimator → Neural FC → DShot ESC → Motors
      UART GPS → State Estimator
                → Path Planner → spray enable
      SBUS RC → manual override / emergency

    Actuators:
      DShot × 4 → brushless motors
      PWM × 4 → spray nozzles

    Safety:
      Failsafe controller monitors all inputs, overrides FC on fault

    Vision (optional, external):
      YOLOv8 obstacle detection → FC thrust reduction

    Control loop @ 1 kHz:
      1. Read IMU (SPI, ~1 μs)
      2. State estimation (complementary filter, combinational)
      3. Path planner provides target waypoint
      4. Neural FC computes motor commands (~15 ns)
      5. Failsafe checks and overrides if needed
      6. Output to ESC (DShot, ~27 μs) + pump (PWM)

  Target FPGA: Zynq-7010 (17,600 LUT, 80 DSP)
-/

import Sparkle.Core.Signal
import Sparkle.Core.Domain
import IP.Drone.FlightController
import IP.Drone.DShot
import IP.Drone.SPIIMU
import IP.Drone.UARTGPS
import IP.Drone.PWMPump
import IP.Drone.SBUS
import IP.Drone.StateEstimator
import IP.Drone.PathPlanner
import IP.Drone.Failsafe

namespace Sparkle.IP.Drone

open Sparkle.Core.Signal
open Sparkle.Core.Domain

variable {dom : DomainConfig}

/-- Agricultural spray drone SoC — all subsystems wired together.

    External pins:
      -- SPI (IMU)
      imuMiso       — SPI data from IMU
      → imuSck, imuMosi, imuCsN

      -- UART (GPS)
      gpsRx         — UART data from GPS module

      -- SBUS (RC)
      sbusPin       — SBUS signal from RC receiver

      -- DShot (Motors)
      → dshot1..4    — DShot signals to ESCs

      -- PWM (Pumps)
      → pump1..4     — PWM signals to spray nozzles

      -- Control
      armSwitch     — arm/disarm safety switch
      missionGo     — start autonomous mission
      obstacleDetect — from external YOLOv8 (optional)
      batteryLow    — from battery monitor ADC

    Returns all output signals bundled. -/
def sprayDroneSoC
    -- Sensor inputs
    (imuMiso : Signal dom Bool)
    (gpsRx : Signal dom Bool)
    (sbusPin : Signal dom Bool)
    -- Control inputs
    (armSwitch : Signal dom Bool)
    (missionGo : Signal dom Bool)
    (obstacleDetect : Signal dom Bool)
    (batteryLow : Signal dom Bool)
    : Signal dom (
        Bool ×           -- dshot1
        (Bool ×          -- dshot2
        (Bool ×          -- dshot3
        (Bool ×          -- dshot4
        (Bool ×          -- pump1
        (Bool ×          -- pump2
        (Bool ×          -- pump3
        (Bool ×          -- pump4
        (Bool ×          -- imuSck
        (Bool ×          -- imuMosi
        (Bool ×          -- imuCsN
        (Bool ×          -- missionDone
        BitVec 4         -- failsafeCode
        )))))))))))) :=

  -- ================================================================
  -- 1. Sensor drivers
  -- ================================================================

  -- IMU: SPI read (triggered every 200,000 cycles = 1 kHz)
  let imuTrigger := Signal.loop (dom := dom) (α := BitVec 32 × Bool)
    fun (self : Signal dom (BitVec 32 × Bool)) =>
    let counter := Signal.fst self
    let pulse := Signal.snd self
    let atRate : Signal dom Bool :=
      counter === (Signal.pure 199999#32 : Signal dom (BitVec 32))
    let nextCounter : Signal dom (BitVec 32) :=
      Signal.mux atRate (Signal.pure 0#32 : Signal dom (BitVec 32))
        (counter + (Signal.pure 1#32 : Signal dom (BitVec 32)))
    bundle2 (Signal.register 0#32 nextCounter) (Signal.register false atRate)
  let imuGo := Signal.snd imuTrigger

  let imuOut := spiIMUDriver imuGo imuMiso
  let imuSck := Signal.fst imuOut
  let ir1 := Signal.snd imuOut
  let imuMosi := Signal.fst ir1
  let ir2 := Signal.snd ir1
  let imuCsN := Signal.fst ir2
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
  let imuValid := Signal.snd ir8

  -- GPS: UART receiver + UBX parser
  let gpsOut := gpsReceiver gpsRx
  let gpsLat := Signal.fst gpsOut
  let gr1 := Signal.snd gpsOut
  let gpsLon := Signal.fst gr1
  let gr2 := Signal.snd gr1
  let gpsAlt := Signal.fst gr2
  let gpsValid := Signal.snd gr2

  -- RC: SBUS receiver
  let rcOut := sbusReceiver sbusPin
  let rcThrottle := Signal.fst (Signal.snd (Signal.snd rcOut))  -- ch3 = throttle
  let rcR1 := Signal.snd (Signal.snd (Signal.snd (Signal.snd (Signal.snd (Signal.snd (Signal.snd (Signal.snd rcOut)))))))
  let rcFailsafe := Signal.fst rcR1

  -- ================================================================
  -- 2. State estimation
  -- ================================================================
  let dt : Signal dom (BitVec 32) := (Signal.pure 0x00000041#32 : Signal dom (BitVec 32))  -- 1/1000 s
  -- Zero-extend IMU 16-bit to 32-bit for state estimator
  let ax32se : Signal dom (BitVec 32) := accelX ++ (Signal.pure 0#16 : Signal dom (BitVec 16))
  let ay32se : Signal dom (BitVec 32) := accelY ++ (Signal.pure 0#16 : Signal dom (BitVec 16))
  let az32se : Signal dom (BitVec 32) := accelZ ++ (Signal.pure 0#16 : Signal dom (BitVec 16))
  let gx32se : Signal dom (BitVec 32) := gyroX ++ (Signal.pure 0#16 : Signal dom (BitVec 16))
  let gy32se : Signal dom (BitVec 32) := gyroY ++ (Signal.pure 0#16 : Signal dom (BitVec 16))
  let gz32se : Signal dom (BitVec 32) := gyroZ ++ (Signal.pure 0#16 : Signal dom (BitVec 16))
  let _attitude := attitudeEstimator gx32se gy32se gz32se ax32se ay32se az32se dt
  let _position := positionEstimator ax32se ay32se az32se gpsLat gpsLon gpsAlt gpsValid dt

  -- ================================================================
  -- 3. Path planner
  -- ================================================================
  let fieldWidth : Signal dom (BitVec 32) := (Signal.pure 0x00640000#32 : Signal dom (BitVec 32))  -- 100 m
  let fieldLength : Signal dom (BitVec 32) := (Signal.pure 0x00C80000#32 : Signal dom (BitVec 32))  -- 200 m
  let swathWidth : Signal dom (BitVec 32) := (Signal.pure 0x00050000#32 : Signal dom (BitVec 32))  -- 5 m
  let sprayAlt : Signal dom (BitVec 32) := (Signal.pure 0x00030000#32 : Signal dom (BitVec 32))  -- 3 m
  let atWaypoint : Signal dom Bool := (Signal.pure false : Signal dom Bool)  -- placeholder
  let pathOut := serpentinePlanner missionGo atWaypoint fieldWidth fieldLength swathWidth sprayAlt
  let pr1 := Signal.snd (Signal.snd (Signal.snd pathOut))
  let sprayEnable := Signal.fst pr1
  let pr2 := Signal.snd pr1
  let missionDone := Signal.fst pr2

  -- ================================================================
  -- 4. Failsafe
  -- ================================================================
  let fsOut := failsafeController rcFailsafe batteryLow imuValid gpsValid
    (Signal.pure true : Signal dom Bool)  -- geofenceOk placeholder
    gpsAlt
  let fsOverride := Signal.fst fsOut
  let fr1 := Signal.snd fsOut
  let fsThrottle := Signal.fst fr1
  let fr2 := Signal.snd fr1
  let _fsEmergencyLand := Signal.fst fr2
  let fr3 := Signal.snd fr2
  let _fsRTH := Signal.fst fr3
  let fsCode := Signal.snd fr3

  -- ================================================================
  -- 5. Neural Flight Controller
  -- ================================================================
  -- Zero-extend 16-bit sensor values to 32-bit (inline, no closure)
  let ax32 : Signal dom (BitVec 32) := accelX ++ (Signal.pure 0#16 : Signal dom (BitVec 16))
  let ay32 : Signal dom (BitVec 32) := accelY ++ (Signal.pure 0#16 : Signal dom (BitVec 16))
  let az32 : Signal dom (BitVec 32) := accelZ ++ (Signal.pure 0#16 : Signal dom (BitVec 16))
  let gx32 : Signal dom (BitVec 32) := gyroX ++ (Signal.pure 0#16 : Signal dom (BitVec 16))
  let gy32 : Signal dom (BitVec 32) := gyroY ++ (Signal.pure 0#16 : Signal dom (BitVec 16))
  let gz32 : Signal dom (BitVec 32) := gyroZ ++ (Signal.pure 0#16 : Signal dom (BitVec 16))

  let fcOut := droneFC ax32 ay32 az32 gx32 gy32 gz32
  let motor1fc := Signal.fst fcOut
  let mr1 := Signal.snd fcOut
  let motor2fc := Signal.fst mr1
  let mr2 := Signal.snd mr1
  let motor3fc := Signal.fst mr2
  let motor4fc := Signal.snd mr2

  -- ================================================================
  -- 6. Failsafe override + obstacle avoidance
  -- ================================================================
  -- Apply obstacle avoidance (halve thrust: ASR 1, inlined)
  let m1avd := Signal.mux obstacleDetect
    (Signal.map (fun v => BitVec.sshiftRight v 1) motor1fc) motor1fc
  let m2avd := Signal.mux obstacleDetect
    (Signal.map (fun v => BitVec.sshiftRight v 1) motor2fc) motor2fc
  let m3avd := Signal.mux obstacleDetect
    (Signal.map (fun v => BitVec.sshiftRight v 1) motor3fc) motor3fc
  let m4avd := Signal.mux obstacleDetect
    (Signal.map (fun v => BitVec.sshiftRight v 1) motor4fc) motor4fc

  -- Apply failsafe override (use fsThrottle for all motors)
  let fsThrottle32 : Signal dom (BitVec 32) :=
    fsThrottle ++ (Signal.pure 0#16 : Signal dom (BitVec 16))
  let m1final := Signal.mux fsOverride fsThrottle32 m1avd
  let m2final := Signal.mux fsOverride fsThrottle32 m2avd
  let m3final := Signal.mux fsOverride fsThrottle32 m3avd
  let m4final := Signal.mux fsOverride fsThrottle32 m4avd

  -- Apply arm switch (motors off when disarmed)
  let m1armed := Signal.mux armSwitch m1final (Signal.pure 0#32 : Signal dom (BitVec 32))
  let m2armed := Signal.mux armSwitch m2final (Signal.pure 0#32 : Signal dom (BitVec 32))
  let m3armed := Signal.mux armSwitch m3final (Signal.pure 0#32 : Signal dom (BitVec 32))
  let m4armed := Signal.mux armSwitch m4final (Signal.pure 0#32 : Signal dom (BitVec 32))

  -- ================================================================
  -- 7. Motor ESC output (DShot)
  -- ================================================================
  -- Convert 32-bit motor value to 11-bit DShot throttle (top 11 bits)
  let t1 : Signal dom (BitVec 11) := Signal.map (BitVec.extractLsb' 21 11 ·) m1armed
  let t2 : Signal dom (BitVec 11) := Signal.map (BitVec.extractLsb' 21 11 ·) m2armed
  let t3 : Signal dom (BitVec 11) := Signal.map (BitVec.extractLsb' 21 11 ·) m3armed
  let t4 : Signal dom (BitVec 11) := Signal.map (BitVec.extractLsb' 21 11 ·) m4armed

  let dshotOut := dshotQuad imuGo t1 t2 t3 t4
  let dshot1 := Signal.fst dshotOut
  let dr1 := Signal.snd dshotOut
  let dshot2 := Signal.fst dr1
  let dr2 := Signal.snd dr1
  let dshot3 := Signal.fst dr2
  let dr3 := Signal.snd dr2
  let dshot4 := Signal.fst dr3

  -- ================================================================
  -- 8. Pump output (PWM)
  -- ================================================================
  let sprayDuty : Signal dom (BitVec 16) := (Signal.pure 0xC000#16 : Signal dom (BitVec 16))  -- 75% duty
  let pumpOut := quadPumpController sprayEnable sprayEnable sprayEnable sprayEnable
    sprayDuty sprayDuty sprayDuty sprayDuty
  let pump1 := Signal.fst pumpOut
  let pp1 := Signal.snd pumpOut
  let pump2 := Signal.fst pp1
  let pp2 := Signal.snd pp1
  let pump3 := Signal.fst pp2
  let pump4 := Signal.snd pp2

  -- ================================================================
  -- Output bundle
  -- ================================================================
  bundle2 dshot1 (bundle2 dshot2 (bundle2 dshot3 (bundle2 dshot4
    (bundle2 pump1 (bundle2 pump2 (bundle2 pump3 (bundle2 pump4
      (bundle2 imuSck (bundle2 imuMosi (bundle2 imuCsN
        (bundle2 missionDone fsCode)))))))))))

end Sparkle.IP.Drone
