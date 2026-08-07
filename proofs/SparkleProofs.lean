/-
  SparkleProofs — the ℝ-level control-theory bridge for Sparkle's `IP/Control`
  fixed-point datapaths.

  Sparkle is an HDL and has nothing to do with real analysis; this package is
  deliberately separate so that `lake build` at the repo root (the path an RTL
  user takes) never depends on Mathlib.  See `proofs/README.md`.
-/
import SparkleProofs.Control.LQRDesign
import SparkleProofs.Control.Transport
import SparkleProofs.Control.Precision
import SparkleProofs.Control.EstimatorDesign
import SparkleProofs.Control.PIDDesign
import SparkleProofs.Control.StepError
import SparkleProofs.Control.QuantizedGains

-- The retype bridge: ℝ ⇒ Float (falsification search) and ℝ ⇒ Q15.16
-- (the fixed-point transport Ch12 §12.2 walks through).  Folded in from the
-- former `retypelab/` sidecar once every package reached Lean v4.32.1.
import SparkleProofs.Retype.Falsify
import SparkleProofs.Retype.FixedPointTransport
