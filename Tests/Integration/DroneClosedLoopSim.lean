/-
  Drone Closed-Loop Simulation — Lean 4

  Minimal 6DOF rigid-body physics for a quadrotor with a cascaded PID
  flight controller. This validates the PID algorithm (same as
  ClassicalFC.lean) in a closed-loop physics environment:

    Motor thrust → rigid body dynamics → IMU readings → PID → motor thrust

  The PID logic is written in plain Lean Float to avoid O(n²) Signal
  stream re-evaluation. The algorithm is identical to ClassicalFC:
    - Rate PID × 3 axes (Kp=0.35, Ki=0.05, Kd=0.005)
    - Attitude P × 2 axes (Kp=4.0, rateMax=3.0)
    - Motor mixer X config
    - Anti-windup clamp on integrator
-/

-- ============================================================
-- Float helpers
-- ============================================================

def absF (x : Float) : Float := if x < 0.0 then -x else x

def clampF (lo hi x : Float) : Float :=
  if x < lo then lo else if x > hi then hi else x

-- ============================================================
-- Quadrotor physical parameters
-- ============================================================

structure QuadParams where
  mass     : Float := 1.5      -- kg
  armLen   : Float := 0.22     -- motor-to-center, m
  Ixx      : Float := 0.015    -- roll inertia, kg·m²
  Iyy      : Float := 0.015    -- pitch inertia, kg·m²
  Izz      : Float := 0.025    -- yaw inertia, kg·m²
  kThrust  : Float := 3.5e-6   -- F = kThrust × dshot²  (hover: 3.5e-6 × 1024² × 4 ≈ 14.7N ≈ mg)
  kTorque  : Float := 1.2e-5   -- yaw torque coeff
  gravity  : Float := 9.81

-- ============================================================
-- 6DOF state
-- ============================================================

structure QuadState where
  px : Float := 0.0
  py : Float := 0.0
  pz : Float := -10.0   -- NED: negative = up
  vx : Float := 0.0
  vy : Float := 0.0
  vz : Float := 0.0
  roll  : Float := 0.0
  pitch : Float := 0.0
  yaw   : Float := 0.0
  p : Float := 0.0   -- roll rate (rad/s)
  q : Float := 0.0   -- pitch rate
  r : Float := 0.0   -- yaw rate
  deriving Repr, Inhabited

-- ============================================================
-- PID controller state (one axis)
-- ============================================================

structure PIDState where
  integrator : Float := 0.0
  prevErr    : Float := 0.0

-- ============================================================
-- Full FC state
-- ============================================================

structure FCState where
  rollPID  : PIDState := {}
  pitchPID : PIDState := {}
  yawPID   : PIDState := {}
  -- Attitude estimator state
  estRoll  : Float := 0.0
  estPitch : Float := 0.0
  estYaw   : Float := 0.0

-- ============================================================
-- PID gains (same as ClassicalFC.lean)
-- ============================================================

def rateKp : Float := 0.35
def rateKi : Float := 0.05
def rateKd : Float := 0.005
def iLimitF : Float := 0.3
def oLimitF : Float := 0.5
def attKpF : Float := 4.0
def rateMaxF : Float := 3.0
def hoverThrottleF : Float := 0.5

-- ============================================================
-- Complementary filter (attitude estimation)
-- ============================================================

def attitudeUpdate (est : Float) (gyroRate : Float) (accelAngle : Float)
    (dt : Float) (alpha : Float) : Float :=
  let gyroEst := est + gyroRate * dt
  alpha * gyroEst + (1.0 - alpha) * accelAngle

-- ============================================================
-- Rate PID step
-- ============================================================

def ratePIDStep (st : PIDState) (setpoint measured : Float) : PIDState × Float :=
  let err := setpoint - measured
  let pTerm := rateKp * err
  let rawInteg := st.integrator + rateKi * err
  let clampedInteg := clampF (-iLimitF) iLimitF rawInteg
  let dErr := err - st.prevErr
  let dTerm := rateKd * dErr
  let rawOut := pTerm + clampedInteg + dTerm
  let out := clampF (-oLimitF) oLimitF rawOut
  ({ integrator := clampedInteg, prevErr := err }, out)

-- ============================================================
-- Attitude P step
-- ============================================================

def attitudePStep (setpoint measured : Float) : Float :=
  let err := setpoint - measured
  clampF (-rateMaxF) rateMaxF (attKpF * err)

-- ============================================================
-- Motor mixer (X config)
-- ============================================================

def motorMix (throttle rollCmd pitchCmd yawCmd : Float) : Float × Float × Float × Float :=
  let m1 := clampF 0.0 1.0 (throttle - rollCmd + pitchCmd + yawCmd)
  let m2 := clampF 0.0 1.0 (throttle - rollCmd - pitchCmd - yawCmd)
  let m3 := clampF 0.0 1.0 (throttle + rollCmd - pitchCmd + yawCmd)
  let m4 := clampF 0.0 1.0 (throttle + rollCmd + pitchCmd - yawCmd)
  (m1, m2, m3, m4)

-- ============================================================
-- Full FC step
-- ============================================================

def fcStep (fc : FCState) (gyroX gyroY gyroZ accelX accelY : Float) (dt : Float)
    : FCState × (Float × Float × Float × Float) :=
  -- Attitude estimation (complementary filter, alpha=0.98)
  let alpha := 0.98
  let estRoll'  := attitudeUpdate fc.estRoll  gyroX accelY  dt alpha
  let estPitch' := attitudeUpdate fc.estPitch gyroY (-accelX) dt alpha
  let estYaw'   := fc.estYaw + gyroZ * dt

  -- Outer loop: attitude → rate setpoint (P-only)
  let rollRateSet  := attitudePStep 0.0 estRoll'
  let pitchRateSet := attitudePStep 0.0 estPitch'
  let yawRateSet   := 0.0  -- hold yaw rate at zero

  -- Inner loop: rate PID
  let (rpid, rollCmd)  := ratePIDStep fc.rollPID  rollRateSet  gyroX
  let (ppid, pitchCmd) := ratePIDStep fc.pitchPID pitchRateSet gyroY
  let (ypid, yawCmd)   := ratePIDStep fc.yawPID   yawRateSet   gyroZ

  -- Motor mix
  let motors := motorMix hoverThrottleF rollCmd pitchCmd yawCmd

  let fc' : FCState := {
    rollPID := rpid, pitchPID := ppid, yawPID := ypid,
    estRoll := estRoll', estPitch := estPitch', estYaw := estYaw'
  }
  (fc', motors)

-- ============================================================
-- Motor duty (0..1) to DShot (0..2047) to thrust
-- ============================================================

def dutyToThrust (params : QuadParams) (duty : Float) : Float :=
  let dshot := duty * 2047.0
  params.kThrust * dshot * dshot

-- ============================================================
-- Physics step
-- ============================================================

def physicsStep (params : QuadParams) (dt : Float) (state : QuadState)
    (m1 m2 m3 m4 : Float) : QuadState :=
  let f1 := dutyToThrust params m1
  let f2 := dutyToThrust params m2
  let f3 := dutyToThrust params m3
  let f4 := dutyToThrust params m4
  let totalThrust := f1 + f2 + f3 + f4

  -- Torques
  let tauRoll  := params.armLen * (f3 + f4 - f1 - f2)
  let tauPitch := params.armLen * (f1 + f4 - f2 - f3)
  let d1 := m1 * 2047.0
  let d2 := m2 * 2047.0
  let d3 := m3 * 2047.0
  let d4 := m4 * 2047.0
  let tauYaw := params.kTorque * ((d1*d1 + d3*d3) - (d2*d2 + d4*d4))

  -- Angular acceleration
  let pDot := tauRoll  / params.Ixx
  let qDot := tauPitch / params.Iyy
  let rDot := tauYaw   / params.Izz

  let p' := state.p + pDot * dt
  let q' := state.q + qDot * dt
  let r' := state.r + rDot * dt

  let roll'  := state.roll  + p' * dt
  let pitch' := state.pitch + q' * dt
  let yaw'   := state.yaw   + r' * dt

  -- Linear acceleration in NED
  let az_body := -totalThrust / params.mass
  let ax := az_body * Float.sin pitch'
  let ay := az_body * (-Float.sin roll') * Float.cos pitch'
  let az := az_body * Float.cos roll' * Float.cos pitch' + params.gravity

  let vx' := state.vx + ax * dt
  let vy' := state.vy + ay * dt
  let vz' := state.vz + az * dt
  let px' := state.px + vx' * dt
  let py' := state.py + vy' * dt
  let pz' := state.pz + vz' * dt

  { px := px', py := py', pz := pz',
    vx := vx', vy := vy', vz := vz',
    roll := roll', pitch := pitch', yaw := yaw',
    p := p', q := q', r := r' }

-- ============================================================
-- Closed-loop simulation
-- ============================================================

def runClosedLoop (params : QuadParams) (nSteps : Nat) (dt : Float)
    (initState : QuadState) : IO (Array QuadState) := do
  let mut state := initState
  let mut fc : FCState := {}
  let mut states : Array QuadState := #[initState]

  for _ in List.range nSteps do
    -- Sensor readings from physics state
    let gyroX := state.p
    let gyroY := state.q
    let gyroZ := state.r
    -- Accelerometer: body-frame specific force (gravity seen in body frame).
    -- For small angles: g projects as g×sin(roll) on Y, -g×sin(pitch) on X,
    -- and -g×cos(roll)×cos(pitch) on Z.
    let accelX := -params.gravity * Float.sin state.pitch
    let accelY :=  params.gravity * Float.sin state.roll

    -- FC step
    let (fc', (m1, m2, m3, m4)) := fcStep fc gyroX gyroY gyroZ accelX accelY dt
    fc := fc'

    -- Physics step
    state := physicsStep params dt state m1 m2 m3 m4
    states := states.push state

  return states

-- ============================================================
-- Test harness
-- ============================================================

def main : IO Unit := do
  let params : QuadParams := {}
  let dt := 0.001

  -- Test 1: Hover stability (2 seconds)
  IO.println "=== Test 1: Hover from rest (2s) ==="
  let hoverStates ← runClosedLoop params 2000 dt {}
  let fin := hoverStates.back!
  IO.println s!"  roll={fin.roll} pitch={fin.pitch} yaw={fin.yaw}"
  IO.println s!"  p={fin.p} q={fin.q} r={fin.r}"
  IO.println s!"  pz={fin.pz} vz={fin.vz}"

  let hoverOk :=
    absF fin.roll < 0.1 && absF fin.pitch < 0.1 &&
    absF fin.p < 0.5 && absF fin.q < 0.5
  IO.println s!"  {if hoverOk then "PASS" else "FAIL"}"

  -- Test 2: Recovery from 15° roll (3 seconds)
  IO.println "\n=== Test 2: Recover from 15° roll (3s) ==="
  let recStates ← runClosedLoop params 3000 dt { roll := 0.26 }
  let fin2 := recStates.back!
  IO.println s!"  roll={fin2.roll} pitch={fin2.pitch}"
  IO.println s!"  p={fin2.p} q={fin2.q}"
  -- Show some intermediate steps to confirm actual dynamics
  let step100 := recStates.getD 100 {}
  let step500 := recStates.getD 500 {}
  let step1000 := recStates.getD 1000 {}
  IO.println s!"  @100ms: roll={step100.roll} p={step100.p}"
  IO.println s!"  @500ms: roll={step500.roll} p={step500.p}"
  IO.println s!"  @1.0s:  roll={step1000.roll} p={step1000.p}"

  let recOk := absF fin2.roll < 0.15 && absF fin2.p < 0.5
  IO.println s!"  {if recOk then "PASS" else "FAIL"}"

  -- Test 3: No divergence (5 seconds)
  IO.println "\n=== Test 3: Long-run stability (5s) ==="
  let longStates ← runClosedLoop params 5000 dt {}
  let fin3 := longStates.back!
  let maxRoll := longStates.foldl (init := 0.0) fun acc st =>
    let v := absF st.roll; if v > acc then v else acc
  let maxPitch := longStates.foldl (init := 0.0) fun acc st =>
    let v := absF st.pitch; if v > acc then v else acc
  IO.println s!"  maxRoll={maxRoll} maxPitch={maxPitch}"
  IO.println s!"  final pz={fin3.pz} vz={fin3.vz}"

  let stableOk := maxRoll < 1.0 && maxPitch < 1.0
  IO.println s!"  {if stableOk then "PASS" else "FAIL"}"

  -- Summary
  let allPass := hoverOk && recOk && stableOk
  IO.println s!"\n=== Closed-loop sim: {if allPass then "ALL PASS" else "SOME FAIL"} ==="
  if !allPass then IO.Process.exit 1
