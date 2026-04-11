/-
  Agricultural Spray Drone SoC — Parallel I/O Version — Signal DSL

  Co-simulation-friendly variant of SprayDroneSoC with parallel I/O
  instead of serial protocols. Used for:
    - Gazebo/Ignition co-simulation (direct shm ↔ signals)
    - PPO reinforcement learning loops (Python ↔ Verilator)
    - Functional testbenches (pre-decoded sensor values)

  Differences from SprayDroneSoC:
    - No SPI IMU decoding: takes 6 × 32-bit sensor values directly
    - No UART GPS parsing: takes lat/lon/alt as parallel inputs
    - No SBUS decoding: takes 8 × 16-bit RC channels + failsafe flag
    - No DShot encoding: outputs 4 × 11-bit throttle values directly
    - No PWM pump encoding: outputs 4 × 16-bit duty values directly

  The Neural FC, path planner, failsafe, and safety logic are identical
  to the serial version — only the I/O shim is different. This means
  training results transfer directly: weights learned in co-sim apply
  to the serial SoC too.
-/

import Sparkle.Core.Signal
import Sparkle.Core.Domain
import IP.Drone.FlightController
import IP.Drone.StateEstimator
import IP.Drone.PathPlanner
import IP.Drone.Failsafe

namespace Sparkle.IP.Drone

open Sparkle.Core.Signal
open Sparkle.Core.Domain

variable {dom : DomainConfig}

/-- Parallel-I/O spray drone SoC.

    Inputs (parallel, pre-decoded):
      -- IMU (Q16.16)
      accelX accelY accelZ  — m/s²
      gyroX gyroY gyroZ     — rad/s
      -- GPS (UBX format)
      gpsLat gpsLon         — 1e-7 degrees
      gpsAlt                — Q16.16 meters
      gpsValid              — GPS fix flag
      -- Battery
      batteryLow            — low-voltage flag
      -- RC
      rcFailsafe            — failsafe flag from receiver
      -- Vision
      obstacleDetect        — from external YOLOv8
      -- Control
      armSwitch             — arm/disarm
      missionGo             — start autonomous mission

    Outputs (parallel, pre-encoded):
      motor1..4             — 11-bit DShot throttle values (48-2047)
      pump1..4              — pump enable flags
      failsafeCode          — 4-bit status
      missionDone           — mission complete
-/
def sprayDroneSoCParallel
    -- IMU
    (accelX accelY accelZ : Signal dom (BitVec 32))
    (gyroX gyroY gyroZ : Signal dom (BitVec 32))
    -- GPS
    (gpsLat gpsLon gpsAlt : Signal dom (BitVec 32))
    (gpsValid : Signal dom Bool)
    -- Status
    (batteryLow : Signal dom Bool)
    (rcFailsafe : Signal dom Bool)
    (obstacleDetect : Signal dom Bool)
    (armSwitch : Signal dom Bool)
    (missionGo : Signal dom Bool)
    : Signal dom (
        BitVec 11 ×     -- motor1
        (BitVec 11 ×    -- motor2
        (BitVec 11 ×    -- motor3
        (BitVec 11 ×    -- motor4
        (Bool ×         -- pump1
        (Bool ×         -- pump2
        (Bool ×         -- pump3
        (Bool ×         -- pump4
        (Bool ×         -- missionDone
        BitVec 4        -- failsafeCode
        ))))))))) :=

  -- ================================================================
  -- 1. State estimation (attitude + position)
  -- ================================================================
  let dt : Signal dom (BitVec 32) := (Signal.pure 0x00000041#32 : Signal dom (BitVec 32))  -- 1/1000 s
  let _attitude := attitudeEstimator gyroX gyroY gyroZ accelX accelY accelZ dt
  let _position := positionEstimator accelX accelY accelZ gpsLat gpsLon gpsAlt gpsValid dt

  -- ================================================================
  -- 2. Path planner
  -- ================================================================
  let fieldWidth : Signal dom (BitVec 32) := (Signal.pure 0x00640000#32 : Signal dom (BitVec 32))  -- 100 m
  let fieldLength : Signal dom (BitVec 32) := (Signal.pure 0x00C80000#32 : Signal dom (BitVec 32))  -- 200 m
  let swathWidth : Signal dom (BitVec 32) := (Signal.pure 0x00050000#32 : Signal dom (BitVec 32))  -- 5 m
  let sprayAlt : Signal dom (BitVec 32) := (Signal.pure 0x00030000#32 : Signal dom (BitVec 32))  -- 3 m
  let atWaypoint : Signal dom Bool := (Signal.pure false : Signal dom Bool)
  let pathOut := serpentinePlanner missionGo atWaypoint fieldWidth fieldLength swathWidth sprayAlt
  let pr1 := Signal.snd (Signal.snd (Signal.snd pathOut))
  let sprayEnable := Signal.fst pr1
  let pr2 := Signal.snd pr1
  let missionDone := Signal.fst pr2

  -- ================================================================
  -- 3. Failsafe (monitors all critical signals)
  -- ================================================================
  let fsOut := failsafeController rcFailsafe batteryLow gpsValid gpsValid
    (Signal.pure true : Signal dom Bool)  -- geofenceOk (TODO: compute from position)
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
  -- 4. Neural Flight Controller (15 ns, combinational)
  -- ================================================================
  let fcOut := droneFC accelX accelY accelZ gyroX gyroY gyroZ
  let motor1fc := Signal.fst fcOut
  let mr1 := Signal.snd fcOut
  let motor2fc := Signal.fst mr1
  let mr2 := Signal.snd mr1
  let motor3fc := Signal.fst mr2
  let motor4fc := Signal.snd mr2

  -- ================================================================
  -- 5. Vision modulation: reduce thrust 50% on obstacle
  -- ================================================================
  let m1avd := Signal.mux obstacleDetect
    (Signal.map (fun v => BitVec.sshiftRight v 1) motor1fc) motor1fc
  let m2avd := Signal.mux obstacleDetect
    (Signal.map (fun v => BitVec.sshiftRight v 1) motor2fc) motor2fc
  let m3avd := Signal.mux obstacleDetect
    (Signal.map (fun v => BitVec.sshiftRight v 1) motor3fc) motor3fc
  let m4avd := Signal.mux obstacleDetect
    (Signal.map (fun v => BitVec.sshiftRight v 1) motor4fc) motor4fc

  -- ================================================================
  -- 6. Failsafe override
  -- ================================================================
  let fsThrottle32 : Signal dom (BitVec 32) :=
    fsThrottle ++ (Signal.pure 0#16 : Signal dom (BitVec 16))
  let m1ovr := Signal.mux fsOverride fsThrottle32 m1avd
  let m2ovr := Signal.mux fsOverride fsThrottle32 m2avd
  let m3ovr := Signal.mux fsOverride fsThrottle32 m3avd
  let m4ovr := Signal.mux fsOverride fsThrottle32 m4avd

  -- ================================================================
  -- 7. Arm switch (motors off when disarmed)
  -- ================================================================
  let m1armed := Signal.mux armSwitch m1ovr (Signal.pure 0#32 : Signal dom (BitVec 32))
  let m2armed := Signal.mux armSwitch m2ovr (Signal.pure 0#32 : Signal dom (BitVec 32))
  let m3armed := Signal.mux armSwitch m3ovr (Signal.pure 0#32 : Signal dom (BitVec 32))
  let m4armed := Signal.mux armSwitch m4ovr (Signal.pure 0#32 : Signal dom (BitVec 32))

  -- ================================================================
  -- 8. Convert 32-bit motor values to 11-bit DShot throttle
  -- ================================================================
  -- Take bits [21:11] of the 32-bit motor value
  let t1 : Signal dom (BitVec 11) := Signal.map (BitVec.extractLsb' 21 11 ·) m1armed
  let t2 : Signal dom (BitVec 11) := Signal.map (BitVec.extractLsb' 21 11 ·) m2armed
  let t3 : Signal dom (BitVec 11) := Signal.map (BitVec.extractLsb' 21 11 ·) m3armed
  let t4 : Signal dom (BitVec 11) := Signal.map (BitVec.extractLsb' 21 11 ·) m4armed

  -- ================================================================
  -- 9. Pump outputs (4 nozzles, enable from sprayEnable)
  -- ================================================================
  let pump1 := sprayEnable
  let pump2 := sprayEnable
  let pump3 := sprayEnable
  let pump4 := sprayEnable

  -- ================================================================
  -- Output bundle
  -- ================================================================
  bundle2 t1 (bundle2 t2 (bundle2 t3 (bundle2 t4
    (bundle2 pump1 (bundle2 pump2 (bundle2 pump3 (bundle2 pump4
      (bundle2 missionDone fsCode))))))))

end Sparkle.IP.Drone
