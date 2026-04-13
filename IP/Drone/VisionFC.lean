/-
  Drone Vision + Flight Controller SoC — Signal DSL

  Combines YOLOv8n (object detection) with BitNet Neural FC:

    Camera → YOLOv8n → obstacle detection → ┐
    IMU sensors ────────────────────────────→ Neural FC → Motor PWM

  The obstacle distance from YOLOv8 is fed as an additional input
  to the neural flight controller, enabling vision-based avoidance.

  Two clock domains possible:
    - YOLOv8: may run at lower clock (image processing is batched)
    - Neural FC: 200 MHz (real-time control loop)

  For this v0: single clock domain, YOLOv8 runs to completion then
  Neural FC uses the latest detection result.

  Target: Zynq UltraScale+ (PS for camera interface, PL for inference)
-/

import Sparkle.Core.Signal
import Sparkle.Core.Domain
import IP.Drone.FlightController

namespace Sparkle.IP.Drone

open Sparkle.Core.Signal
open Sparkle.Core.Domain

variable {dom : DomainConfig}

/-- Vision-augmented flight controller.
    YOLOv8 and Neural FC are separate modules connected at the top level.
    YOLOv8 signals come as external inputs (from YOLOv8 module or testbench).

    This design allows independent synthesis of YOLOv8 and FC, connected
    in the Vivado block design or top-level wrapper. -/
def visionFlightControllerSoC
    -- IMU input
    (accelX accelY accelZ : Signal dom (BitVec 32))
    (gyroX gyroY gyroZ : Signal dom (BitVec 32))
    -- YOLOv8 detection result (from separate YOLOv8 module)
    (obstacleDetected : Signal dom Bool)
    : Signal dom (BitVec 32 × (BitVec 32 × (BitVec 32 × BitVec 32))) :=
  -- Neural Flight Controller (combinational, ~15 ns)
  let fcOut := droneFC accelX accelY accelZ gyroX gyroY gyroZ
  let motor1raw := Signal.fst fcOut
  let mr1 := Signal.snd fcOut
  let motor2raw := Signal.fst mr1
  let mr2 := Signal.snd mr1
  let motor3raw := Signal.fst mr2
  let motor4raw := Signal.snd mr2

  -- Vision modulation: reduce thrust 50% when obstacle detected
  -- (ASR by 1 = divide by 2, inlined to avoid closure)
  let motor1 := Signal.mux obstacleDetected
    (Signal.map (fun v => BitVec.sshiftRight v 1) motor1raw) motor1raw
  let motor2 := Signal.mux obstacleDetected
    (Signal.map (fun v => BitVec.sshiftRight v 1) motor2raw) motor2raw
  let motor3 := Signal.mux obstacleDetected
    (Signal.map (fun v => BitVec.sshiftRight v 1) motor3raw) motor3raw
  let motor4 := Signal.mux obstacleDetected
    (Signal.map (fun v => BitVec.sshiftRight v 1) motor4raw) motor4raw

  bundle2 motor1 (bundle2 motor2 (bundle2 motor3 motor4))

end Sparkle.IP.Drone
