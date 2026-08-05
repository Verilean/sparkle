/-
  IP.Control — fixed-point control datapaths.

  Synthesizable, Mathlib-free, Q15.16 signed arithmetic on `BitVec 32`:

    FixedPoint       — Q15.16 multiply / saturating add / symmetric clamp,
                       plus the `Signal` counterparts that lower to Verilog
    IIRBiquad        — Direct-Form-II-transposed biquad, saturating state.
                       Ships a provably-contracting instance AND a naively
                       quantized one that limit-cycles, as a contrast.
    PID              — PID with anti-windup (integrator clamped inside the
                       state update), plus a closed loop against a
                       first-order plant
    LQRStateFeedback — 2-state LQR feedback on a double integrator, with the
                       Riccati certificate `P` carried alongside so the
                       simulation can watch `V(x) = xᵀPx` decrease

  ## Where the stability proofs live

  Not here.  Sparkle is an HDL; it has nothing to do with real analysis, and
  these modules are ordinary integer circuits.  The ℝ-level Lyapunov/LQR design
  that justifies the coefficients — and the theorem that transports it to this
  fixed-point implementation with quantization as a bounded disturbance — lives
  in the `proofs/` sidecar Lake package, which depends on Mathlib and is
  deliberately outside the main build graph.  `lake build` at the repo root (the
  path an RTL user takes) never pays for Mathlib.

  See `proofs/README.md`.
-/
import IP.Control.FixedPoint
import IP.Control.FixedPointGen
import IP.Control.IIRBiquad
import IP.Control.IIRBiquadGen
import IP.Control.PID
import IP.Control.LQRStateFeedback
