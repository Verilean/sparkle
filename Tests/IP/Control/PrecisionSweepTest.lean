/-
  Precision sweep — the same rational filter design instantiated at five
  fixed-point formats, with the measured behaviour pinned as assertions.

  Two claims are frozen here, both counter to a naive expectation and both
  matching what `proofs/SparkleProofs/Control/Precision.lean` proves about the
  bound's *shape*:

  1. **Accuracy depends on `f`, not `w`.**  Q7.8 (16-bit) and Q23.8 (32-bit)
     produce bit-identical output because they share `f = 8`.  If someone
     "improves" a datapath by widening it without adding fractional bits, this
     test says nothing changed.

  2. **Coarse quantization damps the marginal design instead of destabilising
     it.**  The residual is non-monotone in `f` (0 at `f=8`, 52 at `f=16`) because
     the coarse format's deadband kills the ringing.  Pinning this stops anyone
     from "fixing" the sweep to look monotone — it genuinely isn't.

  See `IP/Control/IIRBiquadGen.lean`'s header for the pole-radius analysis that
  explains the non-monotonicity.
-/

import Sparkle
import Sparkle.Compiler.Elab
import IP.Control.IIRBiquadGen
import LSpec

set_option maxRecDepth 100000

namespace Sparkle.Tests.IP.Control.PrecisionSweepTest

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Control.IIRBiquadGen
open Sparkle.IP.Control.FixedPointGen
open LSpec

/-- Impulse response of `c` at format `(w, f)`, in milliunits. -/
def response (w f : Nat) (c : RatCoeffs) (n : Nat) : List Int :=
  let impulse := (q w f 1 1) :: List.replicate n (BitVec.zero w)
  let ys := run w f (quantize w f c) (limOf w f)
    ⟨BitVec.zero w, BitVec.zero w⟩ impulse
  ys.map (fun y => y.toInt * 1000 / (2 ^ f : Int))

/-- Peak |residual| after `skip` samples — how much ringing is left. -/
def tailAmp (w f : Nat) (c : RatCoeffs) (n skip : Nat) : Nat :=
  (((response w f c n).drop skip).map (fun y => y.natAbs)).foldl Nat.max 0

def suite : TestSeq :=
  group "Precision sweep" <|
    -- ── Claim 1: f governs accuracy, w does not ────────────────────────────
    -- Q7.8 (w=16) and Q23.8 (w=32) share f=8, so they must agree exactly.
    test "stable: Q7.8 and Q23.8 agree (same f, different w)"
      (tailAmp 16 8 stableCoeffs 300 200 == tailAmp 32 8 stableCoeffs 300 200) $
    test "marginal: Q7.8 and Q23.8 agree (same f, different w)"
      (tailAmp 16 8 marginalCoeffs 300 200 == tailAmp 32 8 marginalCoeffs 300 200) $
    test "stable: widening w alone changes nothing (both 15)"
      (tailAmp 16 8 stableCoeffs 300 200 == 15
        && tailAmp 32 8 stableCoeffs 300 200 == 15) $
    -- ── Claim 2: finer f fixes the *stable* design monotonically ───────────
    test "stable: Q11.4 is badly quantized (tail 437)"
      (tailAmp 16 4 stableCoeffs 300 200 == 437) $
    test "stable: Q15.16 settles to exactly zero"
      (tailAmp 32 16 stableCoeffs 300 200 == 0) $
    test "stable: residual is non-increasing in f"
      (tailAmp 16 4 stableCoeffs 300 200 ≥ tailAmp 16 8 stableCoeffs 300 200
        && tailAmp 16 8 stableCoeffs 300 200 ≥ tailAmp 32 16 stableCoeffs 300 200) $
    -- ── Claim 3: the marginal design is NON-monotone in f ──────────────────
    -- Coarse f kills the ringing via the deadband; fine f reproduces it.
    test "marginal: Q7.8 rings down to zero (deadband damps it)"
      (tailAmp 16 8 marginalCoeffs 300 200 == 0) $
    test "marginal: Q15.16 is still ringing (faithful to the ℝ design)"
      (tailAmp 32 16 marginalCoeffs 300 200 == 52) $
    test "marginal: residual is NOT monotone in f — more bits is not 'better'"
      (tailAmp 16 8 marginalCoeffs 300 200 < tailAmp 32 16 marginalCoeffs 300 200) $
    -- The f=8 case dies early rather than decaying gracefully: that is the
    -- deadband signature, and it is what makes the non-monotonicity legitimate.
    test "marginal Q7.8 is dead by cycle 60 (deadband, not slow decay)"
      (tailAmp 16 8 marginalCoeffs 300 60 == 0) $
    test "marginal Q15.16 is very much alive at cycle 60"
      (tailAmp 32 16 marginalCoeffs 300 60 ≥ 50)

def main : IO UInt32 := do
  lspecIO (Std.HashMap.ofList [("all", [suite])]) []

/-- `IO Unit` wrapper for `Tests/AllTests.lean` (see the note in
    `Tests/IP/Control/IIRBiquadTest.lean`). -/
def mainUnit : IO Unit := do
  let code ← main
  if code != 0 then IO.Process.exit 1

/-! ### Synthesis checks

Every format in the sweep must be real hardware, not just a model — otherwise
"we compared five precisions" is a spreadsheet exercise.  These are the same
generic `biquad` instantiated at five `(w, f)` pairs. -/

section SynthesisChecks

set_option maxHeartbeats 80000000

def sweepQ7_8 (x : Signal defaultDomain (BitVec 16)) : Signal defaultDomain (BitVec 16) :=
  stableQ7_8 x

def sweepQ15_16 (x : Signal defaultDomain (BitVec 32)) : Signal defaultDomain (BitVec 32) :=
  stableQ15_16 x

def sweepQ23_8 (x : Signal defaultDomain (BitVec 32)) : Signal defaultDomain (BitVec 32) :=
  stableQ23_8 x

def sweepMarginalQ7_8 (x : Signal defaultDomain (BitVec 16)) : Signal defaultDomain (BitVec 16) :=
  marginalQ7_8 x

def sweepMarginalQ15_16 (x : Signal defaultDomain (BitVec 32)) : Signal defaultDomain (BitVec 32) :=
  marginalQ15_16 x

#synthesizeVerilog sweepQ7_8
#synthesizeVerilog sweepQ15_16
#synthesizeVerilog sweepQ23_8
#synthesizeVerilog sweepMarginalQ7_8
#synthesizeVerilog sweepMarginalQ15_16

end SynthesisChecks

end Sparkle.Tests.IP.Control.PrecisionSweepTest
