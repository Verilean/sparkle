/-
  Drone Closed-Loop Spray Mission Simulation — Lean 4

  Full closed-loop simulation with:
    1. 6DOF rigid-body physics
    2. Cascaded PID flight controller (attitude + rate)
    3. Position/velocity/altitude controller (navigation)
    4. Serpentine path planner
    5. Spray pump control

  Validates the complete stack: path planner → position PID → velocity PID
  → attitude PID → motor mixer → physics → sensors → (loop)
-/

-- ============================================================
-- Float helpers
-- ============================================================

def absF (x : Float) : Float := if x < 0.0 then -x else x

def clampF (lo hi x : Float) : Float :=
  if x < lo then lo else if x > hi then hi else x

-- ============================================================
-- Physical parameters
-- ============================================================

structure QuadParams where
  mass     : Float := 1.5
  armLen   : Float := 0.22
  Ixx      : Float := 0.015
  Iyy      : Float := 0.015
  Izz      : Float := 0.025
  kThrust  : Float := 3.5e-6
  kTorque  : Float := 1.2e-5
  gravity  : Float := 9.81

-- ============================================================
-- 6DOF state
-- ============================================================

structure QuadState where
  px : Float := 0.0
  py : Float := 0.0
  pz : Float := 0.0    -- altitude (positive = up, unlike NED)
  vx : Float := 0.0
  vy : Float := 0.0
  vz : Float := 0.0
  roll  : Float := 0.0
  pitch : Float := 0.0
  yaw   : Float := 0.0
  p : Float := 0.0
  q : Float := 0.0
  r : Float := 0.0
  deriving Repr, Inhabited

-- ============================================================
-- PID state
-- ============================================================

structure PIDState where
  integrator : Float := 0.0
  prevErr    : Float := 0.0

-- ============================================================
-- Full controller state
-- ============================================================

structure FCState where
  -- Attitude estimator
  estRoll  : Float := 0.0
  estPitch : Float := 0.0
  estYaw   : Float := 0.0
  -- Rate PID (inner loop) × 3
  rollRatePID  : PIDState := {}
  pitchRatePID : PIDState := {}
  yawRatePID   : PIDState := {}
  -- Velocity PID × 2
  velXPID : PIDState := {}
  velYPID : PIDState := {}
  -- Altitude PID
  altPID : PIDState := {}

-- ============================================================
-- Path planner state
-- ============================================================

structure PlannerState where
  phase     : Nat := 0   -- 0=idle, 1=fly_leg, 2=turn, 3=done
  passIdx   : Nat := 0
  targetX   : Float := 0.0
  targetY   : Float := 0.0
  goingNorth : Bool := true
  deriving Inhabited

-- ============================================================
-- Mission statistics
-- ============================================================

structure MissionStats where
  totalDistance  : Float := 0.0
  sprayDistance  : Float := 0.0
  sprayOnSteps  : Nat := 0
  maxRoll       : Float := 0.0
  maxPitch      : Float := 0.0
  maxAltError   : Float := 0.0
  waypointsHit  : Nat := 0

-- ============================================================
-- PID gains
-- ============================================================

-- Rate PID (continuous-time gains, scaled by dt in pidStep)
def rateKp : Float := 0.35
def rateKi : Float := 0.3
def rateKd : Float := 0.003
def rateIlim : Float := 0.3
def rateOlim : Float := 0.5

-- Attitude P
def attKpF : Float := 4.0
def attRateMax : Float := 3.0

-- Position P
def posKp : Float := 1.0
def posMaxVel : Float := 5.0

-- Velocity PID (conservative: limit tilt to avoid altitude coupling)
def velKp : Float := 0.1
def velKi : Float := 0.02
def velKd : Float := 0.01
def velIlim : Float := 0.1
def velOlim : Float := 0.15  -- max tilt ~8° to limit altitude coupling

-- Altitude PID
def altKp : Float := 0.2
def altKi : Float := 0.05
def altKd : Float := 0.4
def altIlim : Float := 0.05
def altOlim : Float := 0.1

def hoverThrottle : Float := 0.5

-- ============================================================
-- PID step (generic)
-- ============================================================

def simDt : Float := 0.001  -- shared dt for PID scaling

def pidStep (st : PIDState) (setpoint measured : Float)
    (kp ki kd ilim olim : Float) : PIDState × Float :=
  let err := setpoint - measured
  -- Scale I and D by dt so gains are rate-independent
  let rawI := st.integrator + ki * err * simDt
  let clI := clampF (-ilim) ilim rawI
  let dErr := (err - st.prevErr) / simDt
  let out := clampF (-olim) olim (kp * err + clI + kd * dErr)
  ({ integrator := clI, prevErr := err }, out)

-- ============================================================
-- Complementary filter
-- ============================================================

def attUpdate (est gyroRate accelAngle dt alpha : Float) : Float :=
  alpha * (est + gyroRate * dt) + (1.0 - alpha) * accelAngle

-- ============================================================
-- Full FC step
-- ============================================================

def fcStep (fc : FCState) (gyroX gyroY gyroZ accelX accelY : Float)
    (currentX currentY currentAlt velXm velYm velZm : Float)
    (targetX targetY targetAlt : Float) (dt : Float)
    : FCState × (Float × Float × Float × Float) :=
  let alpha := 0.98

  -- Attitude estimation
  let estRoll'  := attUpdate fc.estRoll  gyroX accelY  dt alpha
  let estPitch' := attUpdate fc.estPitch gyroY (-accelX) dt alpha
  let estYaw'   := fc.estYaw + gyroZ * dt

  -- Position P → velocity setpoint
  let velXset := clampF (-posMaxVel) posMaxVel (posKp * (targetX - currentX))
  let velYset := clampF (-posMaxVel) posMaxVel (posKp * (targetY - currentY))

  -- Velocity PID → attitude setpoint
  let (vxp, pitchDelta) := pidStep fc.velXPID velXset velXm velKp velKi velKd velIlim velOlim
  let (vyp, rollDelta)  := pidStep fc.velYPID velYset velYm velKp velKi velKd velIlim velOlim
  let pitchSet := pitchDelta     -- pitch > 0 → thrust in +X direction
  let rollSet  := -rollDelta    -- roll > 0 → thrust in -Y, so negate

  -- Altitude PID → throttle delta
  let (ap, altDelta) := pidStep fc.altPID targetAlt currentAlt altKp altKi altKd altIlim altOlim
  let throttle := hoverThrottle + altDelta

  -- Attitude P → rate setpoint
  let rollRateSet  := clampF (-attRateMax) attRateMax (attKpF * (rollSet - estRoll'))
  let pitchRateSet := clampF (-attRateMax) attRateMax (attKpF * (pitchSet - estPitch'))
  let yawRateSet   := 0.0

  -- Rate PID → torque
  let (rr, rollCmd)  := pidStep fc.rollRatePID  rollRateSet  gyroX rateKp rateKi rateKd rateIlim rateOlim
  let (pr, pitchCmd) := pidStep fc.pitchRatePID pitchRateSet gyroY rateKp rateKi rateKd rateIlim rateOlim
  let (yr, yawCmd)   := pidStep fc.yawRatePID   yawRateSet   gyroZ rateKp rateKi rateKd rateIlim rateOlim

  -- Motor mix (X config) in normalized thrust space.
  -- Torque commands are small relative to throttle, so we:
  -- 1. Mix linearly to get desired thrust per motor
  -- 2. Convert from thrust to duty: duty = sqrt(thrust / kThrust) / 2047
  --    Simplified: since dutyToThrust(d) = k*(d*2047)², thrust ∝ duty²,
  --    so duty = sqrt(thrust_fraction)
  let f1 := clampF 0.0 1.0 (throttle - rollCmd + pitchCmd + yawCmd)
  let f2 := clampF 0.0 1.0 (throttle - rollCmd - pitchCmd - yawCmd)
  let f3 := clampF 0.0 1.0 (throttle + rollCmd - pitchCmd + yawCmd)
  let f4 := clampF 0.0 1.0 (throttle + rollCmd + pitchCmd - yawCmd)
  let m1 := f1
  let m2 := f2
  let m3 := f3
  let m4 := f4

  let fc' : FCState := {
    estRoll := estRoll', estPitch := estPitch', estYaw := estYaw',
    rollRatePID := rr, pitchRatePID := pr, yawRatePID := yr,
    velXPID := vxp, velYPID := vyp, altPID := ap
  }
  (fc', (m1, m2, m3, m4))

-- ============================================================
-- Physics step (positive-up altitude convention)
-- ============================================================

def dutyToThrust (params : QuadParams) (duty : Float) : Float :=
  -- Linear thrust model: F = kLinear × duty. At duty=0.5, F = mg/4 for hover.
  -- kLinear = mg / (4 × 0.5) = mg / 2
  let kLinear := params.mass * params.gravity / 2.0
  kLinear * duty

def physicsStep (params : QuadParams) (dt : Float) (st : QuadState)
    (m1 m2 m3 m4 : Float) : QuadState :=
  let f1 := dutyToThrust params m1
  let f2 := dutyToThrust params m2
  let f3 := dutyToThrust params m3
  let f4 := dutyToThrust params m4
  let totalThrust := f1 + f2 + f3 + f4

  let tauRoll  := params.armLen * (f3 + f4 - f1 - f2)
  let tauPitch := params.armLen * (f1 + f4 - f2 - f3)
  -- Yaw torque: proportional to thrust difference between CW and CCW motors
  let tauYaw := params.kTorque * ((f1 + f3) - (f2 + f4)) * 1000.0

  let p' := st.p + tauRoll / params.Ixx * dt
  let q' := st.q + tauPitch / params.Iyy * dt
  let r' := st.r + tauYaw / params.Izz * dt

  let roll'  := st.roll  + p' * dt
  let pitch' := st.pitch + q' * dt
  let yaw'   := st.yaw   + r' * dt

  -- Thrust in world frame (positive-up)
  let thrustUp := totalThrust * Float.cos roll' * Float.cos pitch'
  let thrustX  := totalThrust * Float.sin pitch'
  let thrustY  := totalThrust * (-Float.sin roll') * Float.cos pitch'

  let ax := thrustX / params.mass
  let ay := thrustY / params.mass
  let az := thrustUp / params.mass - params.gravity

  let vx' := st.vx + ax * dt
  let vy' := st.vy + ay * dt
  let vz' := st.vz + az * dt
  { px := st.px + vx' * dt, py := st.py + vy' * dt, pz := st.pz + vz' * dt,
    vx := vx', vy := vy', vz := vz',
    roll := roll', pitch := pitch', yaw := yaw',
    p := p', q := q', r := r' }

-- ============================================================
-- Path planner step (Float version of serpentinePlanner)
-- ============================================================

def plannerStep (pl : PlannerState) (go atWaypoint : Bool)
    (fieldLength swathWidth : Float) (maxPasses : Nat)
    : PlannerState × (Float × Float × Bool × Bool) :=
  -- sprayEnable = during fly_leg, missionDone = phase==3
  let sprayEnable := pl.phase == 1
  let missionDone := pl.phase == 3

  let pl' : PlannerState :=
    match pl.phase with
    | 0 =>
      if go then
        ({ phase := 1, passIdx := 0, targetX := 0.0,
           targetY := fieldLength, goingNorth := true } : PlannerState)
      else pl
    | 1 =>
      if atWaypoint then ({ pl with phase := 2 } : PlannerState)
      else pl
    | 2 =>
      if atWaypoint then
        if pl.passIdx >= maxPasses then ({ pl with phase := 3 } : PlannerState)
        else
          let newTargetY := if pl.goingNorth then 0.0 else fieldLength
          ({ phase := 1, passIdx := pl.passIdx + 1,
             targetX := pl.targetX + swathWidth,
             targetY := newTargetY, goingNorth := !pl.goingNorth } : PlannerState)
      else pl
    | _ => pl

  (pl', (pl'.targetX, pl'.targetY, sprayEnable, missionDone))

-- ============================================================
-- Closed-loop spray mission simulation
-- ============================================================

def runSprayMission (params : QuadParams) (nSteps : Nat) (dt : Float)
    (fieldLength swathWidth sprayAlt : Float) (maxPasses : Nat)
    : IO MissionStats := do
  let mut state : QuadState := { pz := sprayAlt }  -- start at spray altitude
  let mut fc : FCState := {}
  let mut planner : PlannerState := {}
  let mut stats : MissionStats := {}
  let mut missionStarted := false
  let mut prevPx := state.px
  let mut prevPy := state.py

  for step in List.range nSteps do
    -- Start mission at step 100 (let hover settle first)
    let go := step >= 100
    if go && !missionStarted then
      missionStarted := true

    -- Waypoint reached check
    let distToWp := Float.sqrt (
      (state.px - planner.targetX) * (state.px - planner.targetX) +
      (state.py - planner.targetY) * (state.py - planner.targetY))
    let atWp := distToWp < 2.0 && missionStarted

    -- Path planner
    let (pl', (tgtX, tgtY, sprayOn, done)) :=
      plannerStep planner go atWp fieldLength swathWidth maxPasses

    planner := pl'

    -- Debug print moved below FC step

    -- Sensors
    let gyroX := state.p
    let gyroY := state.q
    let gyroZ := state.r
    let accelX := -params.gravity * Float.sin state.pitch
    let accelY :=  params.gravity * Float.sin state.roll

    -- FC step (full navigation + attitude + rate)
    let (fc', (m1, m2, m3, m4)) := fcStep fc gyroX gyroY gyroZ accelX accelY
      state.px state.py state.pz state.vx state.vy state.vz
      tgtX tgtY sprayAlt dt
    fc := fc'

    if step % 5000 == 0 && step > 0 then
      IO.println s!"  @{step}: pos=({state.px}, {state.py}, {state.pz}) vz={state.vz}"
      IO.println s!"    motors=({m1}, {m2}, {m3}, {m4}) altI={fc.altPID.integrator}"

    -- Physics
    let prevState := state
    state := physicsStep params dt state m1 m2 m3 m4

    -- Statistics
    let segDist := Float.sqrt (
      (state.px - prevPx) * (state.px - prevPx) +
      (state.py - prevPy) * (state.py - prevPy))
    stats := { stats with
      totalDistance := stats.totalDistance + segDist,
      sprayDistance := stats.sprayDistance + (if sprayOn then segDist else 0.0),
      sprayOnSteps := stats.sprayOnSteps + (if sprayOn then 1 else 0),
      maxRoll := if absF state.roll > stats.maxRoll then absF state.roll else stats.maxRoll,
      maxPitch := if absF state.pitch > stats.maxPitch then absF state.pitch else stats.maxPitch,
      maxAltError := let e := absF (state.pz - sprayAlt);
        if e > stats.maxAltError then e else stats.maxAltError
    }

    -- Track waypoint hits (state transitions to TURN or DONE)
    if atWp && (prevState.px != state.px || true) then
      if planner.phase == 2 || planner.phase == 3 then
        stats := { stats with waypointsHit := stats.waypointsHit + 1 }

    prevPx := state.px
    prevPy := state.py

  return stats

-- ============================================================
-- Main
-- ============================================================

def main : IO Unit := do
  let params : QuadParams := {}
  let dt := 0.001
  let fieldLength := 50.0   -- 50 m field (small for quick test)
  let swathWidth := 5.0
  let sprayAlt := 3.0
  let maxPasses := 3         -- 3 passes for quick test

  -- Test 1: Hover stability (same as before)
  IO.println "=== Test 1: Hover (2s) ==="
  let mut state : QuadState := { pz := 3.0 }
  let mut fc : FCState := {}
  for _ in List.range 2000 do
    let gyroX := state.p; let gyroY := state.q; let gyroZ := state.r
    let accelX := -params.gravity * Float.sin state.pitch
    let accelY :=  params.gravity * Float.sin state.roll
    let (fc', (m1, m2, m3, m4)) := fcStep fc gyroX gyroY gyroZ accelX accelY
      state.px state.py state.pz state.vx state.vy state.vz
      0.0 0.0 3.0 dt
    fc := fc'
    state := physicsStep params dt state m1 m2 m3 m4
  IO.println s!"  roll={state.roll} pitch={state.pitch} pz={state.pz}"
  let hoverOk := absF state.roll < 0.1 && absF state.pitch < 0.1 && absF (state.pz - 3.0) < 1.0
  IO.println s!"  {if hoverOk then "PASS" else "FAIL"}"

  -- Test 2: Altitude hold
  IO.println "\n=== Test 2: Climb to 3m from ground (5s) ==="
  state := { pz := 0.0 }
  fc := {}
  for _ in List.range 5000 do
    let gyroX := state.p; let gyroY := state.q; let gyroZ := state.r
    let accelX := -params.gravity * Float.sin state.pitch
    let accelY :=  params.gravity * Float.sin state.roll
    let (fc', (m1, m2, m3, m4)) := fcStep fc gyroX gyroY gyroZ accelX accelY
      state.px state.py state.pz state.vx state.vy state.vz
      0.0 0.0 3.0 dt
    fc := fc'
    state := physicsStep params dt state m1 m2 m3 m4
  IO.println s!"  pz={state.pz} vz={state.vz}"
  let altOk := absF (state.pz - 3.0) < 1.0 && absF state.vz < 1.0
  IO.println s!"  {if altOk then "PASS" else "FAIL"}"

  -- Test 3: Waypoint tracking
  IO.println "\n=== Test 3: Fly to (10, 0) from origin (10s) ==="
  state := { pz := 3.0 }
  fc := {}
  for _ in List.range 10000 do
    let gyroX := state.p; let gyroY := state.q; let gyroZ := state.r
    let accelX := -params.gravity * Float.sin state.pitch
    let accelY :=  params.gravity * Float.sin state.roll
    let (fc', (m1, m2, m3, m4)) := fcStep fc gyroX gyroY gyroZ accelX accelY
      state.px state.py state.pz state.vx state.vy state.vz
      10.0 0.0 3.0 dt
    fc := fc'
    state := physicsStep params dt state m1 m2 m3 m4
  let wpDist := Float.sqrt ((state.px - 10.0)*(state.px - 10.0) + state.py*state.py)
  IO.println s!"  pos=({state.px}, {state.py}) dist_to_wp={wpDist}"
  let wpOk := wpDist < 3.0
  IO.println s!"  {if wpOk then "PASS" else "FAIL"}"

  -- Test 4: Spray mission
  IO.println s!"\n=== Test 4: Spray mission ({maxPasses} passes, {fieldLength}m field) ==="
  let stats ← runSprayMission params 30000 dt fieldLength swathWidth sprayAlt maxPasses
  IO.println s!"  Total distance:  {stats.totalDistance} m"
  IO.println s!"  Spray distance:  {stats.sprayDistance} m"
  IO.println s!"  Spray on steps:  {stats.sprayOnSteps}"
  IO.println s!"  Waypoints hit:   {stats.waypointsHit}"
  IO.println s!"  Max |roll|:      {stats.maxRoll} rad"
  IO.println s!"  Max |pitch|:     {stats.maxPitch} rad"
  IO.println s!"  Max alt error:   {stats.maxAltError} m"

  let sprayOk := stats.sprayDistance > 10.0 && stats.maxRoll < 1.0 && stats.maxAltError < 5.0 && stats.waypointsHit > 0
  IO.println s!"  {if sprayOk then "PASS" else "FAIL"}"

  -- Summary
  let allPass := hoverOk && altOk && wpOk && sprayOk
  IO.println s!"\n=== Spray drone sim: {if allPass then "ALL PASS" else "SOME FAIL"} ==="
  if !allPass then IO.Process.exit 1
