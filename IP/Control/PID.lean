/-
  Fixed-point PID controller with anti-windup — Q15.16, saturating.

  ## The circuit

      e[n]    = r[n] - y[n]
      I[n+1]  = clamp_iLim( I[n] + Ki*e[n] )        -- anti-windup by clamping
      u[n]    = clamp_uLim( Kp*e[n] + I[n] + Kd*(e[n] - e[n-1]) )

  Two state registers: the integrator `I` and the previous error `ePrev`.

  ## What is provable, and why the clamp placement matters

  The integrator clamp is *inside* the state update, not applied to the output
  afterwards.  That distinction is the whole anti-windup story and it is also
  what makes the boundedness proof trivial rather than impossible:

  - `I[n] ∈ [-iLim, iLim]` for all `n`, by construction, for **any** gains and
    **any** input — no stability assumption needed.  One case split on the two
    comparators.
  - `u[n] ∈ [-uLim, uLim]` likewise.

  So the circuit can never overflow.  What that does *not* give you is that the
  loop converges — a badly tuned PID will happily oscillate between the rails
  forever while satisfying both bounds.  Closing that gap is the job of the
  Lyapunov argument in `proofs/SparkleProofs/Control/PIDStability.lean`, which
  works over ℝ on the closed loop with a plant model, and then transports the
  conclusion to this fixed-point implementation with the quantization treated as
  a bounded disturbance (ISS).
-/

import Sparkle
import Sparkle.Compiler.Elab
import IP.Control.FixedPoint

set_option maxRecDepth 100000

namespace Sparkle.IP.Control.PID

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Control.FixedPoint

variable {dom : DomainConfig}

/-- PID gains in Q15.16. -/
structure Gains where
  kp : BitVec 32
  ki : BitVec 32
  kd : BitVec 32
  deriving Repr, DecidableEq

/-- PID state: integrator accumulator and previous error. -/
structure State where
  integ : BitVec 32
  ePrev : BitVec 32
  deriving Repr, DecidableEq, Inhabited

/-- One cycle of the PID.  `iLim` clamps the integrator (anti-windup), `uLim`
    clamps the control output. -/
def step (g : Gains) (iLim uLim : BitVec 32) (st : State) (r y : BitVec 32)
    : State × BitVec 32 :=
  let e := satAdd r (-y)
  let integ' := clampSym iLim (satAdd st.integ (mulQ g.ki e))
  let d := satAdd e (-st.ePrev)
  let u := clampSym uLim
    (satAdd (satAdd (mulQ g.kp e) integ') (mulQ g.kd d))
  (⟨integ', e⟩, u)

/-- Run the PID over a list of (setpoint, measurement) pairs. -/
def run (g : Gains) (iLim uLim : BitVec 32)
    : State → List (BitVec 32 × BitVec 32) → List (BitVec 32)
  | _, [] => []
  | st, (r, y) :: rest =>
    let (st', u) := step g iLim uLim st r y
    u :: run g iLim uLim st' rest

/-! ### The circuit -/

/-- Synthesizable PID with anti-windup.

    `iLim`/`uLim` are compile-time constants (see `IIRBiquad.biquad` for why);
    gains are `Signal` inputs so they can be retuned at runtime. -/
def pid (iLim uLim : BitVec 32)
    (r y kp ki kd : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  circuit do
    let integReg ← Signal.reg (0#32)
    let ePrevReg ← Signal.reg (0#32)

    let integ := (integReg : Signal dom (BitVec 32))
    let ePrev := (ePrevReg : Signal dom (BitVec 32))

    let e := r - y
    let integNext := clampSymC iLim (integ + mulQSig ki e)
    let d := e - ePrev
    let u := clampSymC uLim (mulQSig kp e + integNext + mulQSig kd d)

    integReg <~ integNext
    ePrevReg <~ e

    return u

/-! ### A concrete tuning

Gains for the first-order plant `x[n+1] = 0.9 x[n] + 0.1 u[n]` used in the
stability proof and the closed-loop simulation test. -/

/-- Q15.16 word nearest `n / d`. -/
def q (n d : Int) : BitVec 32 := BitVec.ofInt 32 (n * (2 ^ 16) / d)

/-- Kp = 2.0, Ki = 0.25, Kd = 0.125 — stabilises the demo plant with margin
    that survives Q15.16 quantization. -/
def demoGains : Gains where
  kp := q 2 1
  ki := q 1 4
  kd := q 1 8

/-- Integrator clamp: ±16.0. -/
def demoILim : BitVec 32 := BitVec.ofInt 32 (16 * (2 ^ 16))

/-- Output clamp: ±8.0 (a real actuator limit). -/
def demoULim : BitVec 32 := BitVec.ofInt 32 (8 * (2 ^ 16))

/-- The demo PID, fully specialised — the top the tests synthesize. -/
def demoPID (r y : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  pid demoILim demoULim r y
    (Signal.pure demoGains.kp) (Signal.pure demoGains.ki) (Signal.pure demoGains.kd)

/-! ### Closed loop

The plant is part of the *circuit* here, not just the proof: closing the loop
in hardware is what makes the demo a control system rather than a filter, and it
gives the simulation test something whose convergence it can actually observe. -/

/-- First-order plant `x[n+1] = a*x[n] + b*u[n]`, saturating. -/
def plantStep (a b : BitVec 32) (x u : BitVec 32) : BitVec 32 :=
  satAdd (mulQ a x) (mulQ b u)

/-- Demo plant coefficients: `a = 0.9`, `b = 0.1`. -/
def plantA : BitVec 32 := q 9 10
def plantB : BitVec 32 := q 1 10

/-- Pure closed-loop iterate: PID + first-order plant, constant setpoint `r`.
    Returns the measurement trajectory, which is what the stability claim is
    about.  This is the function `proofs/` transports the ℝ Lyapunov result onto. -/
def closedLoop (r : BitVec 32) : Nat → State × BitVec 32
  | 0 => (⟨0#32, 0#32⟩, 0#32)
  | n + 1 =>
    let (st, x) := closedLoop r n
    let (st', u) := step demoGains demoILim demoULim st r x
    (st', plantStep plantA plantB x u)

/-- Synthesizable closed loop: the PID drives the plant, the plant's state feeds
    back as the measurement.  One `circuit do` register closes the loop. -/
def closedLoopCircuit (r : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  circuit do
    let xReg ← Signal.reg (0#32)
    let x := (xReg : Signal dom (BitVec 32))
    let u := demoPID r x
    let xNext := clampSymC (BitVec.ofInt 32 (64 * (2 ^ 16)))
      (mulQSig (Signal.pure plantA) x + mulQSig (Signal.pure plantB) u)
    xReg <~ xNext
    return x

end Sparkle.IP.Control.PID
