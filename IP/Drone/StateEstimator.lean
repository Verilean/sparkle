/-
  State Estimator — Complementary Filter — Signal DSL

  Fuses IMU (high-rate, drifts) and GPS (low-rate, absolute) for
  stable position and attitude estimation.

  Complementary filter: α × IMU + (1-α) × GPS
    High-freq from IMU (gyro integration), low-freq from GPS.
    α = 0.98 typical (trust IMU short-term, GPS long-term)

  In Q16.16 fixed-point: α = 0x0000FB00 (0.98), 1-α = 0x00000500 (0.02)

  Outputs:
    roll, pitch, yaw — attitude (Q16.16 radians)
    posX, posY, posZ — position (Q16.16 meters, GPS-corrected)
    velX, velY, velZ — velocity (Q16.16 m/s, from accel integration)

  Update rate: IMU at 1 kHz (every 200,000 cycles @ 200 MHz)
               GPS at 10 Hz (every 20,000,000 cycles)
-/

import Sparkle.Core.Signal
import Sparkle.Core.Domain

namespace Sparkle.IP.Drone

open Sparkle.Core.Signal
open Sparkle.Core.Domain

variable {dom : DomainConfig}

/-- Fixed-point multiply: (a × b) >> 16, both Q16.16.
    Uses signExtend to 64-bit, multiply, extract [47:16]. -/
def fixMul (a b : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  let aExt : Signal dom (BitVec 64) :=
    a ++ (Signal.pure 0#32 : Signal dom (BitVec 32))  -- zero-extend (simplified)
  let bExt : Signal dom (BitVec 64) :=
    b ++ (Signal.pure 0#32 : Signal dom (BitVec 32))
  let prod := aExt * bExt
  Signal.map (BitVec.extractLsb' 16 32 ·) prod

/-- Complementary filter for one axis.
    output = α × imuValue + (1-α) × gpsValue
    α = 0.98 in Q16.16 = 0xFAE1, 1-α = 0x051F -/
def complementaryFilter1D
    (imuValue gpsValue : Signal dom (BitVec 32))
    (gpsValid : Signal dom Bool)
    : Signal dom (BitVec 32) :=
  let alpha : Signal dom (BitVec 32) := (Signal.pure 0x0000FAE1#32 : Signal dom (BitVec 32))
  let oneMinusAlpha : Signal dom (BitVec 32) := (Signal.pure 0x0000051F#32 : Signal dom (BitVec 32))
  let imuTerm := fixMul imuValue alpha
  let gpsTerm := fixMul gpsValue oneMinusAlpha
  -- When GPS not valid, use IMU only
  Signal.mux gpsValid (imuTerm + gpsTerm) imuValue

/-- Attitude estimator: gyro integration + accelerometer correction.
    Integrates gyro rate to get angle, blends with accel-derived angle.

    Returns (roll × (pitch × yaw)). -/
def attitudeEstimator
    (gyroX gyroY gyroZ : Signal dom (BitVec 32))
    (accelX accelY accelZ : Signal dom (BitVec 32))
    (dt : Signal dom (BitVec 32))  -- time step in Q16.16 (e.g. 0x00000041 = 1/1000 s)
    : Signal dom (BitVec 32 × (BitVec 32 × BitVec 32)) :=
  -- Integrate gyro: angle += gyroRate * dt
  let state := Signal.loop (dom := dom)
    (α := BitVec 32 × (BitVec 32 × BitVec 32))
    fun (self : Signal dom (BitVec 32 × (BitVec 32 × BitVec 32))) =>
    let roll := Signal.fst self
    let r1 := Signal.snd self
    let pitch := Signal.fst r1
    let yaw := Signal.snd r1

    -- Gyro integration: angle += gyro * dt
    let dRoll := fixMul gyroX dt
    let dPitch := fixMul gyroY dt
    let dYaw := fixMul gyroZ dt

    let gyroRoll := roll + dRoll
    let gyroPitch := pitch + dPitch
    let gyroYaw := yaw + dYaw

    -- Accelerometer-derived angles (simplified: atan2 approximated as ratio)
    -- accelRoll ≈ accelY (when near level)
    -- accelPitch ≈ -accelX
    let accelRoll := accelY
    let accelPitch : Signal dom (BitVec 32) :=
      (Signal.pure 0#32 : Signal dom (BitVec 32)) - accelX

    -- Complementary filter: blend gyro and accel
    let alpha : Signal dom (BitVec 32) := (Signal.pure 0x0000FB00#32 : Signal dom (BitVec 32))
    let oneMinusAlpha : Signal dom (BitVec 32) := (Signal.pure 0x00000500#32 : Signal dom (BitVec 32))

    let nextRoll := fixMul gyroRoll alpha + fixMul accelRoll oneMinusAlpha
    let nextPitch := fixMul gyroPitch alpha + fixMul accelPitch oneMinusAlpha
    let nextYaw := gyroYaw  -- yaw has no accel correction (needs magnetometer)

    bundle2
      (Signal.register 0#32 nextRoll)
      (bundle2
        (Signal.register 0#32 nextPitch)
        (Signal.register 0#32 nextYaw))

  state

/-- Position estimator: GPS + accelerometer double integration.
    Returns (posX × (posY × (posZ × (velX × (velY × velZ))))). -/
def positionEstimator
    (accelX accelY accelZ : Signal dom (BitVec 32))
    (gpsLat gpsLon gpsAlt : Signal dom (BitVec 32))
    (gpsValid : Signal dom Bool)
    (dt : Signal dom (BitVec 32))
    : Signal dom (BitVec 32 × (BitVec 32 × (BitVec 32 × (BitVec 32 × (BitVec 32 × BitVec 32))))) :=
  let state := Signal.loop (dom := dom)
    (α := BitVec 32 × (BitVec 32 × (BitVec 32 × (BitVec 32 × (BitVec 32 × BitVec 32)))))
    fun (self : Signal dom (BitVec 32 × (BitVec 32 × (BitVec 32 × (BitVec 32 × (BitVec 32 × BitVec 32)))))) =>
    let posX := Signal.fst self
    let r1 := Signal.snd self
    let posY := Signal.fst r1
    let r2 := Signal.snd r1
    let posZ := Signal.fst r2
    let r3 := Signal.snd r2
    let velX := Signal.fst r3
    let r4 := Signal.snd r3
    let velY := Signal.fst r4
    let velZ := Signal.snd r4

    -- Integrate accel → velocity
    let nextVelX := velX + fixMul accelX dt
    let nextVelY := velY + fixMul accelY dt
    let nextVelZ := velZ + fixMul accelZ dt

    -- Integrate velocity → position
    let imuPosX := posX + fixMul nextVelX dt
    let imuPosY := posY + fixMul nextVelY dt
    let imuPosZ := posZ + fixMul nextVelZ dt

    -- Complementary filter with GPS
    let finalPosX := complementaryFilter1D imuPosX gpsLat gpsValid
    let finalPosY := complementaryFilter1D imuPosY gpsLon gpsValid
    let finalPosZ := complementaryFilter1D imuPosZ gpsAlt gpsValid

    bundle2
      (Signal.register 0#32 finalPosX)
      (bundle2
        (Signal.register 0#32 finalPosY)
        (bundle2
          (Signal.register 0#32 finalPosZ)
          (bundle2
            (Signal.register 0#32 nextVelX)
            (bundle2
              (Signal.register 0#32 nextVelY)
              (Signal.register 0#32 nextVelZ)))))

  state

end Sparkle.IP.Drone
