/-
  RetypeLab — ℝ ⇒ Float falsification front-end for the IP/Control demo.

  Still a separate Lake package from `proofs/` (its own mathlib copy), though
  the toolchain split that originally forced the split is gone — everything is
  on v4.32.1 now.  See `RetypeLab/Falsify.lean`'s header for what the remaining
  seam costs and why it is safe.
-/
import RetypeLab.Falsify
import RetypeLab.FixedPointTransport
