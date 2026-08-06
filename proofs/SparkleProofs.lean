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
