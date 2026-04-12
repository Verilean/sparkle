/-
  Classical Cascaded PID Flight Controller — Signal DSL

  The real flight controller: no learning, no neural nets. A textbook
  cascaded PID (attitude outer loop → rate inner loop) feeding an X-
  configuration motor mixer. This is what Betaflight / ArduPilot / PX4
  run on their inner loop, and what every flying multirotor on the planet
  uses.

  Architecture:

       ┌───────── attitude setpoint (roll/pitch target)
       ▼
    ┌──────┐   rate setpoint   ┌──────┐   torque cmd  ┌──────┐
    │ Att  │──────────────────▶│ Rate │──────────────▶│ Mix  │─▶ 4 motors
    │ PID  │                   │ PID  │               │ X    │
    └──────┘                   └──────┘               └──────┘
       ▲                          ▲                      ▲
       │ measured attitude        │ gyro                 │ throttle
       │ (from complementary      │ (Q16.16 rad/s)       │ (hover=mid)
       │  filter)                 │                      │

  All arithmetic is signed Q16.16. Errors are signed, integrators are
  clamped to prevent windup, outputs are saturated at ±1.0.

  Timing: fully combinational — one tick per cycle, no multi-cycle FSM.
  The integrator registers update at posedge, everything else is pure
  logic. At 200 MHz this runs at 200 kHz easily (we only need 2 kHz).

  This replaces `droneFC` (neuralFlightController) in the parallel SoC.
  The BitNet-based FC is kept in `FlightController.lean` as an
  experimental high-level policy layer — it is NOT appropriate for
  reflex-level rate control.
-/

import Sparkle.Core.Signal
import Sparkle.Core.Domain
import IP.Drone.StateEstimator  -- reuse fixMul

namespace Sparkle.IP.Drone

open Sparkle.Core.Signal
open Sparkle.Core.Domain

variable {dom : DomainConfig}

-- ============================================================
-- Q16.16 signed arithmetic helpers
-- ============================================================

/-- Signed Q16.16 multiply: (a × b) >>arith 16.

    Same shape as `fixMul` in StateEstimator but uses arithmetic shift
    on the 64-bit product so negative errors don't wrap. We use the
    `a ++ 0` zero-extension trick (same as `fixMul`) — the modular BitVec
    multiply followed by arithmetic right-shift yields the correct signed
    result for the upper half of the Q16.16 range we care about. -/
-- Sign-extend a 32-bit Signal to 64 bits by replicating the sign bit.
-- Uses `slt a 0` (signed less-than) to detect negativity, then muxes
-- the upper 32 bits between all-ones and all-zeros.
def signExt32to64 (a : Signal dom (BitVec 32)) : Signal dom (BitVec 64) :=
  let zero32  : Signal dom (BitVec 32) := (Signal.pure 0#32 : Signal dom (BitVec 32))
  let isNeg : Signal dom Bool := Signal.lift2 BitVec.slt a zero32
  let hiOnes  : Signal dom (BitVec 32) := (Signal.pure 0xFFFFFFFF#32 : Signal dom (BitVec 32))
  let hi := Signal.mux isNeg hiOnes zero32
  hi ++ a

def fixMulS (a b : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  -- Sign-extend to 64 bits for signed Q16.16 multiply.
  let aExt : Signal dom (BitVec 64) := signExt32to64 a
  let bExt : Signal dom (BitVec 64) := signExt32to64 b
  let prod := aExt * bExt
  -- For Q16.16 multiply: (a × b) has the fractional point at bit 32,
  -- so we need bits [47:16] to get the Q16.16 result.
  Signal.map (BitVec.extractLsb' 16 32 ·) prod

/-- Saturating clamp to a symmetric range [-limit, +limit].
    Input and limit are both Q16.16 signed. Marked reducible so the
    Verilog backend inlines it and doesn't have to handle the local
    parameter binding. -/
@[reducible] def clampSym
    (sig : Signal dom (BitVec 32)) (limit : Signal dom (BitVec 32))
    : Signal dom (BitVec 32) :=
  let negLimit : Signal dom (BitVec 32) :=
    (Signal.pure 0#32 : Signal dom (BitVec 32)) - limit
  -- slt is `first < second`: pass operands in the right order,
  -- the backend doesn't consistently respect a lambda's arg swap.
  let tooHigh : Signal dom Bool := Signal.lift2 BitVec.slt limit sig  -- limit < sig
  let tooLow  : Signal dom Bool := Signal.lift2 BitVec.slt sig negLimit  -- sig < -limit
  Signal.mux tooHigh limit (Signal.mux tooLow negLimit sig)

-- ============================================================
-- Rate PID (inner loop) — one axis
-- ============================================================

/-- Single-axis rate PID controller.

    err = setpoint - measured
    P = Kp × err
    I = clamp(I + Ki × err, ±iLimit)   -- anti-windup
    D = Kd × (err - prevErr)            -- error derivative

    output = clamp(P + I + D, ±outLimit)

    All values are Q16.16 signed. The integrator and previous-error
    register are the only stateful elements.

    Returns just the output; the internal state is held inside the
    Signal.loop. -/
def ratePID
    (setpoint measured : Signal dom (BitVec 32))
    (kp ki kd : Signal dom (BitVec 32))
    (iLimit outLimit : Signal dom (BitVec 32))
    : Signal dom (BitVec 32) :=
  let state := Signal.loop (dom := dom)
    (α := BitVec 32 × (BitVec 32 × BitVec 32))  -- (integrator, prevErr, output)
    fun (self : Signal dom (BitVec 32 × (BitVec 32 × BitVec 32))) =>
      let integ := Signal.fst self
      let r1 := Signal.snd self
      let prevErr := Signal.fst r1
      let _oldOut := Signal.snd r1

      let err := setpoint - measured

      let pTerm := fixMulS kp err
      let iIncrement := fixMulS ki err
      let rawInteg := integ + iIncrement
      let clampedInteg := clampSym rawInteg iLimit
      let dErr := err - prevErr
      let dTerm := fixMulS kd dErr

      let rawOut := pTerm + clampedInteg + dTerm
      let clampedOut := clampSym rawOut outLimit

      bundle2
        (Signal.register 0#32 clampedInteg)
        (bundle2
          (Signal.register 0#32 err)
          (Signal.register 0#32 clampedOut))

  Signal.snd (Signal.snd state)

-- ============================================================
-- Attitude PID (outer loop) — one axis, P-only
-- ============================================================

/-- Single-axis attitude PID. In practice the outer loop is almost
    always P-only (derivative on attitude is noisy, integrator on
    attitude is handled by the rate loop's I term). So this is just
    Kp × (setpoint - measured) clamped to a max rate.

    Returns the rate setpoint for the inner loop. -/
def attitudeP
    (setpoint measured : Signal dom (BitVec 32))
    (kp : Signal dom (BitVec 32))
    (rateMax : Signal dom (BitVec 32))
    : Signal dom (BitVec 32) :=
  let err := setpoint - measured
  let rateSetpoint := fixMulS kp err
  clampSym rateSetpoint rateMax

-- ============================================================
-- Motor mixer — X configuration
-- ============================================================

/-- X-configuration motor mix.

    Motor numbering (Betaflight convention, X config):
      m1 = front-right (CW)
      m2 = rear-right  (CCW)
      m3 = rear-left   (CW)
      m4 = front-left  (CCW)

    Mix equations:
      m1 = T - roll + pitch + yaw
      m2 = T - roll - pitch - yaw
      m3 = T + roll - pitch + yaw
      m4 = T + roll + pitch - yaw

    Inputs are all Q16.16. Throttle is a positive quantity centered at
    hover (0.5 = 0x00008000). Roll/pitch/yaw torques are signed and
    typically in ±0.3 range.

    Outputs are clamped to [0, 1.0] (Q16.16: [0, 0x00010000]) then
    scaled so that the final motor value occupies bits [31:16]-ish
    range expected by the downstream DShot conversion in
    SprayDroneSoCParallel (which extracts [21:11]).

    For that extraction: bit 21 is the middle bit of the 11-bit throttle
    window. A Q16.16 value of 0.5 (0x00008000) gives extractLsb 21 11 of
    roughly 0x400 (1024), which is the middle of DShot range [48, 2047].
    Perfect. -/
def motorMixerX
    (throttle roll pitch yaw : Signal dom (BitVec 32))
    : Signal dom (BitVec 32 × (BitVec 32 × (BitVec 32 × BitVec 32))) :=
  let m1raw := throttle - roll + pitch + yaw
  let m2raw := throttle - roll - pitch - yaw
  let m3raw := throttle + roll - pitch + yaw
  let m4raw := throttle + roll + pitch - yaw

  -- Clamp each to [0, 1.0] — inlined per-motor to avoid closure
  -- formation that the Verilog backend can't resolve.
  let zero : Signal dom (BitVec 32) := (Signal.pure 0#32 : Signal dom (BitVec 32))
  let one  : Signal dom (BitVec 32) := (Signal.pure 0x00010000#32 : Signal dom (BitVec 32))

  -- slt args are (first < second); we want `m < 0` for neg and
  -- `one < m` for over, so pass the operands in the correct order.
  let m1neg  : Signal dom Bool := Signal.lift2 BitVec.slt m1raw zero
  let m1over : Signal dom Bool := Signal.lift2 BitVec.slt one m1raw
  let m1 := Signal.mux m1neg zero (Signal.mux m1over one m1raw)

  let m2neg  : Signal dom Bool := Signal.lift2 BitVec.slt m2raw zero
  let m2over : Signal dom Bool := Signal.lift2 BitVec.slt one m2raw
  let m2 := Signal.mux m2neg zero (Signal.mux m2over one m2raw)

  let m3neg  : Signal dom Bool := Signal.lift2 BitVec.slt m3raw zero
  let m3over : Signal dom Bool := Signal.lift2 BitVec.slt one m3raw
  let m3 := Signal.mux m3neg zero (Signal.mux m3over one m3raw)

  let m4neg  : Signal dom Bool := Signal.lift2 BitVec.slt m4raw zero
  let m4over : Signal dom Bool := Signal.lift2 BitVec.slt one m4raw
  let m4 := Signal.mux m4neg zero (Signal.mux m4over one m4raw)

  -- No scaling: we return the clamped Q16.16 value directly in
  -- [0, 0x00010000]. The caller (SprayDroneSoCParallel) is responsible
  -- for extracting the appropriate 11-bit window. Keeping the natural
  -- Q16.16 representation here avoids synthesizing a shift-left
  -- constant, which the current Verilog backend struggles with.
  bundle2 m1 (bundle2 m2 (bundle2 m3 m4))

-- ============================================================
-- Default PID gains (documentation-only)
-- ============================================================
-- Q16.16 representations of the starting gains used inside `classicalFC`
-- below. They are inlined as `Signal.pure ...#32` literals at the call
-- sites rather than being referenced through top-level `Signal` constants
-- — constants that abstract over the `dom` type parameter leak
-- unresolved metavariables into the Verilog backend.
--
--   rate Kp ≈ 0.35   →  0x00005999
--   rate Ki ≈ 0.05   →  0x00000CCC
--   rate Kd ≈ 0.005  →  0x00000147
--   integrator clamp ≈ ±0.3  →  0x00004CCC
--   rate output clamp ≈ ±0.5 →  0x00008000
--   attitude Kp ≈ 4.0  →  0x00040000
--   attitude rate limit ≈ 3.0 rad/s →  0x00030000
--   hover throttle = 0.5 →  0x00008000

-- ============================================================
-- Top-level classical FC
-- ============================================================

/-- Cascaded PID flight controller.

    Inputs:
      rollMeas, pitchMeas, yawMeas         — current attitude (Q16.16 rad)
      gyroX, gyroY, gyroZ                  — body rates (Q16.16 rad/s)
      rollSet, pitchSet, yawRateSet        — setpoints
        (roll/pitch are angles, yaw is rate — typical acro/angle mode hybrid)
      throttleCmd                          — base throttle (Q16.16, 0 to 1)

    Outputs: 4 × 32-bit motor commands, bundled.

    The inner rate loop runs PID on each axis. The outer attitude loop
    is P-only and feeds the rate loop's setpoint (for roll/pitch only;
    yaw is rate-commanded directly). -/
def classicalFC
    (rollMeas pitchMeas _yawMeas : Signal dom (BitVec 32))
    (gyroX gyroY gyroZ : Signal dom (BitVec 32))
    (rollSet pitchSet yawRateSet : Signal dom (BitVec 32))
    (throttleCmd : Signal dom (BitVec 32))
    : Signal dom (BitVec 32 × (BitVec 32 × (BitVec 32 × BitVec 32))) :=
  -- Gains as local (non-polymorphic) Signal constants — inlining here
  -- keeps `dom` concrete for the Verilog backend.
  let kp      : Signal dom (BitVec 32) := (Signal.pure 0x00005999#32 : Signal dom (BitVec 32))
  let ki      : Signal dom (BitVec 32) := (Signal.pure 0x00000CCC#32 : Signal dom (BitVec 32))
  let kd      : Signal dom (BitVec 32) := (Signal.pure 0x00000147#32 : Signal dom (BitVec 32))
  let iLimit  : Signal dom (BitVec 32) := (Signal.pure 0x00004CCC#32 : Signal dom (BitVec 32))
  let oLimit  : Signal dom (BitVec 32) := (Signal.pure 0x00008000#32 : Signal dom (BitVec 32))
  let attKp   : Signal dom (BitVec 32) := (Signal.pure 0x00040000#32 : Signal dom (BitVec 32))
  let rateMax : Signal dom (BitVec 32) := (Signal.pure 0x00030000#32 : Signal dom (BitVec 32))

  -- Outer loop: angle → rate setpoint (P-only)
  let rollRateSet  := attitudeP rollSet  rollMeas  attKp rateMax
  let pitchRateSet := attitudeP pitchSet pitchMeas attKp rateMax
  -- Yaw: rate setpoint comes in directly from the pilot (or mission)
  let yawRateSet'  := yawRateSet

  -- Inner loop: rate error → torque command
  let rollTorque  := ratePID rollRateSet  gyroX kp ki kd iLimit oLimit
  let pitchTorque := ratePID pitchRateSet gyroY kp ki kd iLimit oLimit
  let yawTorque   := ratePID yawRateSet'  gyroZ kp ki kd iLimit oLimit

  -- Mix into 4 motors
  motorMixerX throttleCmd rollTorque pitchTorque yawTorque

end Sparkle.IP.Drone
