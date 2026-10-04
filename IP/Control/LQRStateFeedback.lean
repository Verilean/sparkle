/-
  LQR state feedback for a 2-state plant — Q15.16, saturating.

  ## The plant and the controller

  A double integrator (the canonical LQR example — position/velocity, discretised
  at `dt = 1/16 s`):

      x₁[n+1] = x₁[n] + dt·x₂[n]
      x₂[n+1] = x₂[n] + dt·u[n]

  with the LQR control law

      u[n] = clamp_uLim( -(k₁·x₁[n] + k₂·x₂[n]) )

  The gain `K = [k₁ k₂]` is *not* computed on-chip.  It is a constant, and its
  provenance is the interesting part: `proofs/SparkleProofs/Control/LQRDesign.lean`
  solves the discrete algebraic Riccati equation over ℝ for `Q = I`, `R = 1`,
  exhibits the resulting `P ≻ 0`, and proves `V(x) = xᵀPx` is a Lyapunov function
  for the ℝ closed loop.  Only then is `K` rounded to Q15.16 and shipped here.

  That split is the point of this whole directory: the *design* needs real
  analysis and quadratic forms (Mathlib), the *implementation* is integer
  arithmetic that Sparkle turns into Verilog (no Mathlib), and the bridge is a
  theorem relating the two with the rounding error treated as a bounded
  disturbance.

  ## What the clamps buy

  As in `PID.lean`, both state registers and the control output are clamped, so
  the reachable set is structurally bounded and the circuit cannot overflow
  regardless of the gain.  The Lyapunov result is what tells you the trajectory
  actually goes to (a neighbourhood of) the origin instead of oscillating.
-/

import Sparkle
import Sparkle.Compiler.Elab
import IP.Control.FixedPoint

set_option maxRecDepth 100000

namespace Sparkle.IP.Control.LQR

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Control.FixedPoint

variable {dom : DomainConfig}

/-- Q15.16 word nearest `n / d`. -/
def q (n d : Int) : BitVec 32 := BitVec.ofInt 32 (n * (2 ^ 16) / d)

/-- Two-element state-feedback gain row, Q15.16. -/
structure Gain where
  k1 : BitVec 32
  k2 : BitVec 32
  deriving Repr, DecidableEq

/-- Plant state `(x₁, x₂)`. -/
structure State where
  x1 : BitVec 32
  x2 : BitVec 32
  deriving Repr, DecidableEq, Inhabited

/-- Sample time `dt = 1/16` in Q15.16.  A power of two, so `mulQ dt` is an exact
    arithmetic shift — no quantization error at all on the integration step,
    which keeps the error budget in the proof concentrated in the gain rounding. -/
def dt : BitVec 32 := q 1 16

/-- The control law: `u = -(k₁x₁ + k₂x₂)`, clamped. -/
def control (k : Gain) (uLim : BitVec 32) (st : State) : BitVec 32 :=
  clampSym uLim (-(satAdd (mulQ k.k1 st.x1) (mulQ k.k2 st.x2)))

/-- One cycle of the closed loop: compute `u`, then advance the double
    integrator.  `xLim` clamps both state registers. -/
def step (k : Gain) (xLim uLim : BitVec 32) (st : State) : State × BitVec 32 :=
  let u := control k uLim st
  let x1' := clampSym xLim (satAdd st.x1 (mulQ dt st.x2))
  let x2' := clampSym xLim (satAdd st.x2 (mulQ dt u))
  (⟨x1', x2'⟩, u)

/-- Closed-loop trajectory from an initial state. -/
def run (k : Gain) (xLim uLim : BitVec 32) : State → Nat → State
  | st, 0 => st
  | st, n + 1 => run k xLim uLim (step k xLim uLim st).1 n

/-- Quadratic Lyapunov candidate evaluated in fixed point:
    `V(x) = p11·x₁² + 2·p12·x₁x₂ + p22·x₂²`, all in Q15.16.

    Present on the implementation side so the simulation test can *observe* `V`
    decreasing cycle by cycle — a cheap, concrete sanity check that the ℝ-level
    certificate in `proofs/` was transported correctly.  The theorem lives in
    `proofs/`; this is the witness you can print. -/
def lyapunovV (p11 p12 p22 : BitVec 32) (st : State) : BitVec 32 :=
  let t1 := mulQ p11 (mulQ st.x1 st.x1)
  let t2 := mulQ (q 2 1) (mulQ p12 (mulQ st.x1 st.x2))
  let t3 := mulQ p22 (mulQ st.x2 st.x2)
  satAdd (satAdd t1 t2) t3

/-! ### The circuit -/

/-- Synthesizable LQR state feedback: emits the control signal `u`.

    The plant is inside the loop (see `PID.closedLoopCircuit` for the same
    choice) so that this is a self-contained closed-loop demo that a simulator
    or a board can run with no external stimulus beyond reset. -/
def lqrLoop (k1 k2 : BitVec 32) (xLim uLim : BitVec 32)
    (x1Init x2Init : BitVec 32) : Signal dom (BitVec 32) :=
  circuit do
    let x1Reg ← Signal.reg x1Init
    let x2Reg ← Signal.reg x2Init

    let x1 := (x1Reg : Signal dom (BitVec 32))
    let x2 := (x2Reg : Signal dom (BitVec 32))

    let zero := (Signal.pure 0#32 : Signal dom (BitVec 32))
    let kx := mulQSig (Signal.pure k1) x1 + mulQSig (Signal.pure k2) x2
    let u := clampSymC uLim (zero - kx)

    let dtS := (Signal.pure dt : Signal dom (BitVec 32))
    let x1Next := clampSymC xLim (x1 + mulQSig dtS x2)
    let x2Next := clampSymC xLim (x2 + mulQSig dtS u)

    x1Reg <~ x1Next
    x2Reg <~ x2Next

    return u

/-- Synthesizable state-feedback controller with the plant *outside* (the shape
    you would actually instantiate on a board, driven by real sensor inputs). -/
def lqrController (uLim : BitVec 32)
    (x1 x2 k1 k2 : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  let zero := (Signal.pure 0#32 : Signal dom (BitVec 32))
  clampSymC uLim (zero - (mulQSig k1 x1 + mulQSig k2 x2))

/-! ### The designed gain

`K = [0.6180, 1.2600]` — the Q15.16 rounding of the DARE solution for the
double integrator with `dt = 1/16`, `Q = I`, `R = 1`.  Derived and proven
stabilising in `proofs/SparkleProofs/Control/LQRDesign.lean`; the numbers here
are the *output* of that derivation, not independent magic constants. -/
def demoGain : Gain where
  k1 := q 6180 10000
  k2 := q 12600 10000

/-- The Riccati solution `P` that certifies `demoGain`, rounded to Q15.16.
    Used by `lyapunovV` in the simulation test. -/
def demoP11 : BitVec 32 := q 21180 10000
def demoP12 : BitVec 32 := q 9885 10000
def demoP22 : BitVec 32 := q 40160 10000

/-- State clamp: ±64.0. -/
def demoXLim : BitVec 32 := BitVec.ofInt 32 (64 * (2 ^ 16))

/-- Control clamp: ±8.0. -/
def demoULim : BitVec 32 := BitVec.ofInt 32 (8 * (2 ^ 16))

/-- Fully specialised closed loop starting from `x = (4.0, 0)` — the top the
    tests synthesize and simulate. -/
def demoLQR : Signal dom (BitVec 32) :=
  lqrLoop demoGain.k1 demoGain.k2 demoXLim demoULim (q 4 1) (0#32)

/-- Pure counterpart of `demoLQR`'s trajectory, for the cross-check test. -/
def demoRun (n : Nat) : State :=
  run demoGain demoXLim demoULim ⟨q 4 1, 0#32⟩ n

end Sparkle.IP.Control.LQR
