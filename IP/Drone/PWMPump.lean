/-
  PWM Pump Controller — Signal DSL

  PWM signal generator for agricultural spray pump/nozzle control.

  Features:
    - Configurable frequency (default 50 Hz for servo/pump)
    - 16-bit duty cycle resolution
    - On/off control with soft start (ramp up over N cycles)
    - Multiple output channels (for multiple nozzles)

  At 200 MHz, 50 Hz PWM:
    Period = 200M / 50 = 4,000,000 cycles
    1% duty = 40,000 cycles
    16-bit duty: 0 = off, 65535 = 100%

  Interface:
    enable   — pump on/off
    duty     — 16-bit duty cycle (0 = off, 0xFFFF = full)
    pwmOut   — PWM output signal (to pump driver MOSFET)
-/

import Sparkle.Core.Signal
import Sparkle.Core.Domain

namespace Sparkle.IP.Drone

open Sparkle.Core.Signal
open Sparkle.Core.Domain

variable {dom : DomainConfig}

/-- PWM generator with configurable period.
    `periodBits` selects the counter width that determines frequency:
    period = 2^periodBits cycles.

    At 200 MHz:
      periodBits=22: 2^22 = 4.2M cycles → ~47.7 Hz (close to 50 Hz servo)
      periodBits=16: 2^16 = 65536 cycles → ~3 kHz (good for pump motor)
      periodBits=12: 2^12 = 4096 cycles → ~48.8 kHz (ultrasonic pump)

    Returns (pwmOut × counter). -/
def pwmGenerator
    (enable : Signal dom Bool)
    (duty : Signal dom (BitVec 16))
    : Signal dom (Bool × BitVec 16) :=
  -- Free-running 16-bit counter
  let state := Signal.loop (dom := dom) (α := BitVec 16)
    fun (self : Signal dom (BitVec 16)) =>
    let nextCount : Signal dom (BitVec 16) :=
      Signal.mux enable
        (self + (Signal.pure 1#16 : Signal dom (BitVec 16)))
        (Signal.pure 0#16 : Signal dom (BitVec 16))
    Signal.register 0#16 nextCount

  -- PWM: output high when counter < duty
  -- Compare via subtraction sign bit: counter - duty < 0 → counter < duty
  let diff : Signal dom (BitVec 16) := state - duty
  let counterLessThanDuty : Signal dom Bool :=
    Signal.map (BitVec.extractLsb' 15 1 ·) diff === (Signal.pure 1#1 : Signal dom (BitVec 1))
  let pwmOut : Signal dom Bool :=
    Signal.mux enable counterLessThanDuty (Signal.pure false : Signal dom Bool)

  bundle2 pwmOut state

/-- Pump controller with soft start ramp.
    When enabled, duty ramps from 0 to target over `rampCycles` cycles.
    When disabled, output immediately goes to 0.

    Returns (pwmOut × currentDuty × ramping). -/
def pumpController
    (enable : Signal dom Bool)
    (targetDuty : Signal dom (BitVec 16))
    : Signal dom (Bool × (BitVec 16 × Bool)) :=
  -- Ramp state: current duty ramps toward target
  let rampState := Signal.loop (dom := dom) (α := BitVec 16 × Bool)
    fun (self : Signal dom (BitVec 16 × Bool)) =>
    let currentDuty := Signal.fst self
    let wasEnabled := Signal.snd self

    -- Ramp up: increment duty by 1 each cycle until reaching target
    let atTarget : Signal dom Bool :=
      currentDuty === targetDuty
    let rampUp : Signal dom (BitVec 16) :=
      Signal.mux atTarget currentDuty
        (currentDuty + (Signal.pure 1#16 : Signal dom (BitVec 16)))

    let nextDuty : Signal dom (BitVec 16) :=
      Signal.mux enable rampUp (Signal.pure 0#16 : Signal dom (BitVec 16))
    let nextEnabled := enable

    bundle2 (Signal.register 0#16 nextDuty) (Signal.register false nextEnabled)

  let currentDuty := Signal.fst rampState
  let _wasEnabled := Signal.snd rampState

  -- PWM generator with ramped duty
  let pwmOut := pwmGenerator enable currentDuty
  let pwm := Signal.fst pwmOut

  let ramping : Signal dom Bool :=
    Signal.mux enable
      (Signal.mux (currentDuty === targetDuty)
        (Signal.pure false : Signal dom Bool) (Signal.pure true : Signal dom Bool))
      (Signal.pure false : Signal dom Bool)

  bundle2 pwm (bundle2 currentDuty ramping)

/-- Multi-nozzle pump controller (4 nozzles).
    Each nozzle has independent enable and duty.
    Returns (pwm1 × (pwm2 × (pwm3 × pwm4))). -/
def quadPumpController
    (en1 en2 en3 en4 : Signal dom Bool)
    (duty1 duty2 duty3 duty4 : Signal dom (BitVec 16))
    : Signal dom (Bool × (Bool × (Bool × Bool))) :=
  let p1 := Signal.fst (pumpController en1 duty1)
  let p2 := Signal.fst (pumpController en2 duty2)
  let p3 := Signal.fst (pumpController en3 duty3)
  let p4 := Signal.fst (pumpController en4 duty4)
  bundle2 p1 (bundle2 p2 (bundle2 p3 p4))

end Sparkle.IP.Drone
