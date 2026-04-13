/-
  Failsafe Controller — Signal DSL

  Monitors critical conditions and triggers emergency actions:
    1. RC signal loss (SBUS failsafe flag) → Return to Home (RTH)
    2. Low battery → RTH then land
    3. IMU failure (no updates) → emergency landing (cut throttle slowly)
    4. GPS loss → hold position (hover in place using IMU only)
    5. Geofence violation → RTH

  Priority: IMU failure > Low battery > RC loss > Geofence > GPS loss

  Output: override mode + override throttle + emergency flags
-/

import Sparkle.Core.Signal
import Sparkle.Core.Domain

namespace Sparkle.IP.Drone

open Sparkle.Core.Signal
open Sparkle.Core.Domain

variable {dom : DomainConfig}

/-- Failsafe controller.

    Inputs:
      rcFailsafe    — RC signal lost (from SBUS)
      batteryLow    — battery voltage below threshold
      imuValid      — IMU data received recently
      gpsValid      — GPS fix valid
      geofenceOk    — within allowed flight area
      currentAlt    — current altitude (Q16.16)

    Returns:
      overrideActive — failsafe has taken control
      overrideThrottle — commanded throttle (0 = idle, 0x8000 = hover, 0xFFFF = full)
      emergencyLand — immediately descend and stop motors
      returnToHome  — navigate to home position
      failsafeCode  — 4-bit code indicating which failsafe triggered -/
def failsafeController
    (rcFailsafe : Signal dom Bool)
    (batteryLow : Signal dom Bool)
    (imuValid : Signal dom Bool)
    (gpsValid : Signal dom Bool)
    (geofenceOk : Signal dom Bool)
    (currentAlt : Signal dom (BitVec 32))
    : Signal dom (Bool × (BitVec 16 × (Bool × (Bool × BitVec 4)))) :=
  -- Watchdog: count cycles since last IMU update
  -- If imuValid doesn't pulse for 500,000 cycles (2.5 ms), declare failure
  let watchdog := Signal.loop (dom := dom) (α := BitVec 32 × Bool)
    fun (self : Signal dom (BitVec 32 × Bool)) =>
    let counter := Signal.fst self
    let imuTimeout := Signal.snd self

    let timeout : Signal dom (BitVec 32) := (Signal.pure 500000#32 : Signal dom (BitVec 32))
    let atTimeout : Signal dom Bool := counter === timeout

    let nextCounter : Signal dom (BitVec 32) :=
      Signal.mux imuValid (Signal.pure 0#32 : Signal dom (BitVec 32))
        (counter + (Signal.pure 1#32 : Signal dom (BitVec 32)))
    let nextTimeout : Signal dom Bool :=
      Signal.mux imuValid (Signal.pure false : Signal dom Bool)
        (Signal.mux atTimeout (Signal.pure true : Signal dom Bool) imuTimeout)

    bundle2 (Signal.register 0#32 nextCounter) (Signal.register false nextTimeout)

  let imuTimeout := Signal.snd watchdog

  -- Geofence violation
  let geofenceViolation : Signal dom Bool :=
    Signal.mux geofenceOk (Signal.pure false : Signal dom Bool) (Signal.pure true : Signal dom Bool)

  -- Priority encoder: highest priority failsafe condition
  -- 1: IMU failure → emergency land (most critical)
  -- 2: Low battery → RTH + land
  -- 3: RC loss → RTH
  -- 4: Geofence → RTH
  -- 5: GPS loss → position hold (least critical)

  let emergencyLand : Signal dom Bool := imuTimeout

  let returnToHome : Signal dom Bool :=
    Signal.mux imuTimeout (Signal.pure false : Signal dom Bool)  -- IMU fail overrides
      (Signal.mux batteryLow (Signal.pure true : Signal dom Bool)
        (Signal.mux rcFailsafe (Signal.pure true : Signal dom Bool)
          (Signal.mux geofenceViolation (Signal.pure true : Signal dom Bool)
            (Signal.pure false : Signal dom Bool))))

  let overrideActive : Signal dom Bool :=
    Signal.mux imuTimeout (Signal.pure true : Signal dom Bool)
      (Signal.mux batteryLow (Signal.pure true : Signal dom Bool)
        (Signal.mux rcFailsafe (Signal.pure true : Signal dom Bool)
          (Signal.mux geofenceViolation (Signal.pure true : Signal dom Bool)
            (Signal.mux gpsValid (Signal.pure false : Signal dom Bool)
              (Signal.pure true : Signal dom Bool)))))  -- GPS loss = override

  -- Override throttle:
  -- Emergency land: descend slowly (reduce from current, floor at 0)
  -- RTH: maintain hover (~50% throttle = 0x8000)
  -- GPS loss: hover
  let hoverThrottle : Signal dom (BitVec 16) := (Signal.pure 0x8000#16 : Signal dom (BitVec 16))
  let descendThrottle : Signal dom (BitVec 16) := (Signal.pure 0x4000#16 : Signal dom (BitVec 16))  -- 25%

  let overrideThrottle : Signal dom (BitVec 16) :=
    Signal.mux emergencyLand descendThrottle
      (Signal.mux returnToHome hoverThrottle
        hoverThrottle)  -- GPS loss → hover

  -- Failsafe code
  let code : Signal dom (BitVec 4) :=
    Signal.mux imuTimeout (Signal.pure 1#4 : Signal dom (BitVec 4))
      (Signal.mux batteryLow (Signal.pure 2#4 : Signal dom (BitVec 4))
        (Signal.mux rcFailsafe (Signal.pure 3#4 : Signal dom (BitVec 4))
          (Signal.mux geofenceViolation (Signal.pure 4#4 : Signal dom (BitVec 4))
            (Signal.mux gpsValid (Signal.pure 0#4 : Signal dom (BitVec 4))
              (Signal.pure 5#4 : Signal dom (BitVec 4))))))

  bundle2 overrideActive (bundle2 overrideThrottle
    (bundle2 emergencyLand (bundle2 returnToHome code)))

end Sparkle.IP.Drone
