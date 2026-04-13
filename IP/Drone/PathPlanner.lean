/-
  Path Planner — Agricultural Spray Pattern — Signal DSL

  Generates waypoints for serpentine (lawn-mower) spray pattern
  over a rectangular field.

  Pattern:
    Start → fly north → turn east → fly south → turn east → repeat
    ┌──→──→──→──┐
    │            ↓
    │  ┌──←──←──┘
    ↓  │
    └──→──→──→──┐
                 ↓
    END──←──←──┘

  Parameters:
    fieldWidth   — east-west extent (Q16.16 meters)
    fieldLength  — north-south extent
    swathWidth   — spray width per pass (typically 3-5 m)
    sprayAlt     — target altitude
    startPos     — SW corner of field (lat, lon)

  FSM: IDLE → FLY_NORTH → TURN_EAST → FLY_SOUTH → TURN_EAST → ... → DONE

  Output: target position (lat, lon, alt) for the flight controller
-/

import Sparkle.Core.Signal
import Sparkle.Core.Domain

namespace Sparkle.IP.Drone

open Sparkle.Core.Signal
open Sparkle.Core.Domain

variable {dom : DomainConfig}

/-- Serpentine path planner for rectangular field spray.

    Inputs:
      go         — start mission
      currentPos — current position X (Q16.16, east)
      fieldWidth — total field width (Q16.16)
      fieldLength — total field length (Q16.16)
      swathWidth — width per pass (Q16.16)
      sprayAlt   — target altitude (Q16.16)
      atWaypoint — true when drone has reached current target

    Returns (targetX × (targetY × (targetAlt × (sprayEnable × (missionDone × phase))))). -/
def serpentinePlanner
    (go : Signal dom Bool)
    (atWaypoint : Signal dom Bool)
    (fieldWidth fieldLength swathWidth : Signal dom (BitVec 32))
    (sprayAlt : Signal dom (BitVec 32))
    : Signal dom (BitVec 32 × (BitVec 32 × (BitVec 32 × (Bool × (Bool × BitVec 4))))) :=
  -- State: phase(4) × passIdx(8) × targetX(32) × targetY(32) × goingNorth(1)
  let state := Signal.loop (dom := dom)
    (α := BitVec 4 × (BitVec 8 × (BitVec 32 × (BitVec 32 × Bool))))
    fun (self : Signal dom (BitVec 4 × (BitVec 8 × (BitVec 32 × (BitVec 32 × Bool))))) =>
    let phase := Signal.fst self
    let r1 := Signal.snd self
    let passIdx := Signal.fst r1
    let r2 := Signal.snd r1
    let targetX := Signal.fst r2
    let r3 := Signal.snd r2
    let targetY := Signal.fst r3
    let goingNorth := Signal.snd r3

    let isIdle : Signal dom Bool := phase === (Signal.pure 0#4 : Signal dom (BitVec 4))
    let isFlyLeg : Signal dom Bool := phase === (Signal.pure 1#4 : Signal dom (BitVec 4))
    let isTurn : Signal dom Bool := phase === (Signal.pure 2#4 : Signal dom (BitVec 4))
    let isDone : Signal dom Bool := phase === (Signal.pure 3#4 : Signal dom (BitVec 4))

    let goIdle : Signal dom Bool := Signal.mux isIdle go (Signal.pure false : Signal dom Bool)

    -- At waypoint during fly leg → turn
    let legDone : Signal dom Bool :=
      Signal.mux isFlyLeg atWaypoint (Signal.pure false : Signal dom Bool)
    -- At waypoint during turn → next leg or done
    let turnDone : Signal dom Bool :=
      Signal.mux isTurn atWaypoint (Signal.pure false : Signal dom Bool)

    -- Check if all passes complete: passIdx * swathWidth >= fieldWidth
    -- Simplified: compare passIdx against max passes (fieldWidth / swathWidth)
    -- For v0: use fixed 20 passes max
    let maxPasses : Signal dom (BitVec 8) := (Signal.pure 20#8 : Signal dom (BitVec 8))
    let allPassesDone : Signal dom Bool :=
      Signal.mux turnDone (passIdx === maxPasses) (Signal.pure false : Signal dom Bool)

    let nextPhase : Signal dom (BitVec 4) :=
      Signal.mux goIdle (Signal.pure 1#4 : Signal dom (BitVec 4))         -- → FLY_LEG
        (Signal.mux legDone (Signal.pure 2#4 : Signal dom (BitVec 4))    -- → TURN
          (Signal.mux allPassesDone (Signal.pure 3#4 : Signal dom (BitVec 4))  -- → DONE
            (Signal.mux turnDone (Signal.pure 1#4 : Signal dom (BitVec 4))    -- → next FLY_LEG
              (Signal.mux isDone
                (Signal.mux go (Signal.pure 1#4 : Signal dom (BitVec 4)) phase)
                phase))))

    -- Target Y: north or south end depending on direction
    let northEnd := fieldLength
    let southEnd : Signal dom (BitVec 32) := (Signal.pure 0#32 : Signal dom (BitVec 32))
    let nextTargetY : Signal dom (BitVec 32) :=
      Signal.mux goIdle northEnd
        (Signal.mux turnDone
          (Signal.mux goingNorth southEnd northEnd)  -- flip direction
          targetY)

    -- Target X: move east by swathWidth on each turn
    let nextTargetX : Signal dom (BitVec 32) :=
      Signal.mux goIdle (Signal.pure 0#32 : Signal dom (BitVec 32))
        (Signal.mux turnDone (targetX + swathWidth) targetX)

    let nextPassIdx : Signal dom (BitVec 8) :=
      Signal.mux goIdle (Signal.pure 0#8 : Signal dom (BitVec 8))
        (Signal.mux turnDone
          (passIdx + (Signal.pure 1#8 : Signal dom (BitVec 8)))
          passIdx)

    let nextGoingNorth : Signal dom Bool :=
      Signal.mux goIdle (Signal.pure true : Signal dom Bool)
        (Signal.mux turnDone
          (Signal.mux goingNorth (Signal.pure false : Signal dom Bool) (Signal.pure true : Signal dom Bool))
          goingNorth)

    bundle2
      (Signal.register 0#4 nextPhase)
      (bundle2
        (Signal.register 0#8 nextPassIdx)
        (bundle2
          (Signal.register 0#32 nextTargetX)
          (bundle2
            (Signal.register 0#32 nextTargetY)
            (Signal.register true nextGoingNorth))))

  let phase := Signal.fst state
  let r1 := Signal.snd state
  let _passIdx := Signal.fst r1
  let r2 := Signal.snd r1
  let targetX := Signal.fst r2
  let r3 := Signal.snd r2
  let targetY := Signal.fst r3

  let isFlyLeg : Signal dom Bool := phase === (Signal.pure 1#4 : Signal dom (BitVec 4))
  let isDone : Signal dom Bool := phase === (Signal.pure 3#4 : Signal dom (BitVec 4))

  bundle2 targetX (bundle2 targetY (bundle2 sprayAlt
    (bundle2 isFlyLeg (bundle2 isDone phase))))

end Sparkle.IP.Drone
