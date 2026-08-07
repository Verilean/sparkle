/-
  RetypeLab — ℝ ⇒ Float falsification front-end for the IP/Control demo.

  Separate from `proofs/` because retype pins Lean v4.32.0 while Sparkle and
  `proofs/` are on v4.28.0.  See `RetypeLab/Falsify.lean`'s header for what that
  seam costs and why it is safe.
-/
import RetypeLab.Falsify
import RetypeLab.FixedPointTransport
