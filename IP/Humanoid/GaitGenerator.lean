/-
  Gait Generator — Bipedal Walking Pattern — Signal DSL

  Generates foot trajectory for bipedal walking.
  Cyclic pattern: left-stance/right-swing → right-stance/left-swing.

  Walking cycle (simplified inverted pendulum model):
    - Stance phase: foot on ground, body moves forward
    - Swing phase: foot lifts, swings forward, lands

  Foot trajectory (trapezoid in sagittal plane):
    - Lift: z ramps up over 25% of swing
    - Cruise: z stays at step_height, x advances
    - Land: z ramps down over 25% of swing

  Outputs: target foot positions (x, y, z) for left and right foot.
  These feed into limbIK6DOF for joint angle computation.

  All Q16.16 fixed-point.
-/

import Sparkle.Core.Signal
import Sparkle.Core.Domain

namespace Sparkle.IP.Humanoid

open Sparkle.Core.Signal
open Sparkle.Core.Domain

variable {dom : DomainConfig}

/-- Gait generator FSM.

    Inputs:
      enable      — walking enabled
      stepLength  — forward step size (Q16.16 meters)
      stepHeight  — foot lift height (Q16.16 meters)
      walkSpeed   — cycles per half-stride (controls walk speed)

    Returns (rFootX × (rFootZ × (lFootX × (lFootZ × (phase × isRightSwing))))). -/
def gaitGenerator
    (enable : Signal dom Bool)
    (stepLength stepHeight : Signal dom (BitVec 32))
    (stridePeriod : BitVec 16)  -- half-stride duration in cycles
    : Signal dom (BitVec 32 × (BitVec 32 × (BitVec 32 × (BitVec 32 × (BitVec 16 × Bool))))) :=
  let state := Signal.loop (dom := dom)
    (α := BitVec 16 × (Bool × (BitVec 32 × (BitVec 32 × (BitVec 32 × BitVec 32)))))
    fun (self : Signal dom (BitVec 16 × (Bool × (BitVec 32 × (BitVec 32 × (BitVec 32 × BitVec 32)))))) =>
    let phaseCounter := Signal.fst self
    let r1 := Signal.snd self
    let isRightSwing := Signal.fst r1
    let r2 := Signal.snd r1
    let rFootX := Signal.fst r2
    let r3 := Signal.snd r2
    let rFootZ := Signal.fst r3
    let r4 := Signal.snd r3
    let lFootX := Signal.fst r4
    let lFootZ := Signal.snd r4

    let periodLimit : Signal dom (BitVec 16) := (Signal.pure stridePeriod : Signal dom (BitVec 16))

    -- Phase counter: 0 → stridePeriod, then flip swing leg
    let atEnd : Signal dom Bool := phaseCounter === periodLimit
    let nextCounter : Signal dom (BitVec 16) :=
      Signal.mux enable
        (Signal.mux atEnd (Signal.pure 0#16 : Signal dom (BitVec 16))
          (phaseCounter + (Signal.pure 1#16 : Signal dom (BitVec 16))))
        (Signal.pure 0#16 : Signal dom (BitVec 16))

    -- Toggle swing leg at end of half-stride
    let nextIsRightSwing : Signal dom Bool :=
      Signal.mux atEnd
        (Signal.mux isRightSwing (Signal.pure false : Signal dom Bool) (Signal.pure true : Signal dom Bool))
        isRightSwing

    -- Swing foot trajectory: x advances linearly, z is trapezoidal
    -- Normalized phase: t = counter / period (0 to 1)
    -- x_swing = -stepLength/2 + stepLength × t
    -- z_swing = stepHeight × triangle(t) where triangle peaks at t=0.5

    -- Simplified: z = stepHeight when counter < period/2, else 0 (square lift)
    let halfPeriod : Signal dom (BitVec 16) :=
      Signal.map (fun p => BitVec.extractLsb' 1 16 (0#1 ++ p)) periodLimit
    let inLiftPhase : Signal dom Bool :=
      Signal.map (BitVec.extractLsb' 15 1 ·) (phaseCounter - halfPeriod)
        === (Signal.pure 1#1 : Signal dom (BitVec 1))  -- counter < halfPeriod

    let swingZ : Signal dom (BitVec 32) :=
      Signal.mux inLiftPhase stepHeight (Signal.pure 0#32 : Signal dom (BitVec 32))

    -- X: stance foot stays at -stepLength/2, swing foot at +stepLength/2
    let halfStep := Signal.map (fun v => BitVec.sshiftRight v 1) stepLength
    let negHalfStep := (Signal.pure 0#32 : Signal dom (BitVec 32)) - halfStep

    -- Right foot
    let nextRFootX : Signal dom (BitVec 32) :=
      Signal.mux enable
        (Signal.mux isRightSwing halfStep negHalfStep)
        (Signal.pure 0#32 : Signal dom (BitVec 32))
    let nextRFootZ : Signal dom (BitVec 32) :=
      Signal.mux enable
        (Signal.mux isRightSwing swingZ (Signal.pure 0#32 : Signal dom (BitVec 32)))
        (Signal.pure 0#32 : Signal dom (BitVec 32))
    -- Left foot: opposite of right
    let nextLFootX : Signal dom (BitVec 32) :=
      Signal.mux enable
        (Signal.mux isRightSwing negHalfStep halfStep)
        (Signal.pure 0#32 : Signal dom (BitVec 32))
    let nextLFootZ : Signal dom (BitVec 32) :=
      Signal.mux enable
        (Signal.mux isRightSwing (Signal.pure 0#32 : Signal dom (BitVec 32)) swingZ)
        (Signal.pure 0#32 : Signal dom (BitVec 32))

    bundle2
      (Signal.register 0#16 nextCounter)
      (bundle2
        (Signal.register true nextIsRightSwing)
        (bundle2
          (Signal.register 0#32 nextRFootX)
          (bundle2
            (Signal.register 0#32 nextRFootZ)
            (bundle2
              (Signal.register 0#32 nextLFootX)
              (Signal.register 0#32 nextLFootZ)))))

  let phaseCounter := Signal.fst state
  let r1 := Signal.snd state
  let isRightSwing := Signal.fst r1
  let r2 := Signal.snd r1
  let rFootX := Signal.fst r2
  let r3 := Signal.snd r2
  let rFootZ := Signal.fst r3
  let r4 := Signal.snd r3
  let lFootX := Signal.fst r4
  let lFootZ := Signal.snd r4

  bundle2 rFootX (bundle2 rFootZ (bundle2 lFootX (bundle2 lFootZ
    (bundle2 phaseCounter isRightSwing))))

end Sparkle.IP.Humanoid
