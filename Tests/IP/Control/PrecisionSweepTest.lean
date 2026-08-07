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
import IP.Control.FixedPoint
import Sparkle.Verification.FixedPointProps
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

/-! ### Transport agreement — the Sparkle half of Ch12 §12.2.2

`proofs/SparkleProofs/Retype/FixedPointTransport.lean` transports the ℝ controller
equation to Q15.16 with `retype`, giving a fixed-point multiply that is
`(a * b) / 2^16` on `Int`.  Sparkle's datapath uses `mulQ`, which is
`extractLsb' 16` on a sign-extended product.

The chapter claims those are the same function.  That claim is the joint
between the proved ℝ model and the shipped RTL, so it is checked here rather
than asserted — and checked on SIGN-CROSSING cases specifically, because
that is the only place the two could differ:

  * `extractLsb' 16` on a sign-extended product is an ARITHMETIC shift, so
    it rounds toward −∞;
  * Lean's `Int./` also floors.

Had either side truncated toward zero instead, every case below with a
negative product and a non-zero remainder would fail.  (The two packages
still do not import each other — the transport lives in the `proofs/` sidecar,
which is kept out of the root build graph so an RTL build never pays for
mathlib — so `refMul` restates the transported multiply rather than importing
it.  A drift between the two shows up as a failure here.) -/

/-- The transported multiply, as `FixQ.Mul` defines it. -/
def refMul (a b : Int) : Int := (a * b) / 65536

/-- Sparkle's datapath multiply, on the same numerators. -/
def hwMul (a b : Int) : Int :=
  (Sparkle.IP.Control.FixedPoint.mulQ (BitVec.ofInt 32 a) (BitVec.ofInt 32 b)).toInt

/-- Cases chosen to cross zero and to land on non-zero remainders, where a
    truncating implementation would disagree. -/
def transportCases : List (Int × Int) :=
  [(65536, 65536), (4096, 65536), (58982, 65536), (-65536, 65536),
   (65536, -65536), (-58982, -65536), (1, 1), (-1, 1), (1, -1),
   (123456, -7890), (-1, 65535), (3, -65537), (-58982, 65536),
   (43419, 58982), (-43419, 58982)]

/-- The `mulQ` identity at a SMALL width, checked exhaustively.

    Q15.16 has 2⁶⁴ input pairs, so §12.2.2's suite samples it.  The same shape
    at 8 bits / 4 fractional bits has only 65536, which is cheap to enumerate
    — and enumerating it pins two things the sampled version cannot:

    * the identity `(mulQ a b).toInt = (a.toInt * b.toInt) / 2^f` holds for
      EVERY pair whose result fits, not just the chosen fixtures;
    * it is genuinely FALSE without the no-overflow side condition
      (`a = 17, b = 121` → 128, one past the signed 8-bit max, which
      `extractLsb'` wraps to −128).

    That second point is why the pending `BitVec` lemma needs the hypothesis.
    Recorded here so nobody drops it as pedantry. -/
def mulQ84 (a b : BitVec 8) : Int :=
  (BitVec.extractLsb' 4 8 ((a.signExtend 16) * (b.signExtend 16))).toInt

def mulQ84Exhaustive : Bool × Bool := Id.run do
  let mut allAgree := true      -- with the fits-in-range guard
  let mut sawWrap  := false     -- without it
  for i in [0:256] do
    for j in [0:256] do
      let a : BitVec 8 := BitVec.ofNat 8 i
      let b : BitVec 8 := BitVec.ofNat 8 j
      let rhs := (a.toInt * b.toInt) / 16
      let lhs := mulQ84 a b
      if -128 ≤ rhs && rhs ≤ 127 then
        if lhs != rhs then allAgree := false
      else if lhs != rhs then sawWrap := true
  return (allAgree, sawWrap)

/-- `Sparkle/Verification/FixedPointProps.lean` restates `mulQ` rather than
    importing `IP.Control` (it stays free of the Signal/elaborator stack).
    This pins the restatement against the real definition so it cannot drift
    — if they ever diverge, the proved lemma would be about a function the
    hardware does not use. -/
def provedMulQ (a b : BitVec 32) : BitVec 32 :=
  Sparkle.Verification.FixedPointProps.mulQ a b

def restatementSuite : TestSeq :=
  group "the proved mulQ is the datapath mulQ" <|
    test "agree on every transport case"
      ((transportCases.filter (fun (a, b) =>
          provedMulQ (BitVec.ofInt 32 a) (BitVec.ofInt 32 b)
            != Sparkle.IP.Control.FixedPoint.mulQ (BitVec.ofInt 32 a) (BitVec.ofInt 32 b))).isEmpty)

/-! ### ℝ-equal, fixed-point-different (Ch12 §12.2.4)

`proofs/…/AlgebraicRewrite.lean` proves the two shapes of the PID output are
equal over ℝ and within 6 lsb of each other in Q15.16.  This is the
measurement behind that: the ℝ identity does NOT survive quantization, and
the disagreement is common rather than exotic. -/

def s16 : Int := 65536
def mq (a b : Int) : Int := (a * b) / s16
def kpQ : Int := 2 * s16
def kiQ : Int := s16 / 4
def kdQ : Int := s16 / 8

def uAq (e st p : Int) : Int := mq kpQ e + mq kiQ st + mq kdQ (e - p)
def uBq (e st p : Int) : Int := mq (kpQ + kdQ) e + mq kiQ st - mq kdQ p

/-- A deterministic sweep — no RNG, so the counts are reproducible. -/
def rewriteStats : Nat × Nat := Id.run do
  let mut diff := 0
  let mut worst := 0
  for i in [0:40] do
    for j in [0:40] do
      for k in [0:40] do
        let e := (i * 3251 % 196608) - 98304
        let st := (j * 5077 % 196608) - 98304
        let p := (k * 7919 % 196608) - 98304
        let d := (uAq e st p - uBq e st p).natAbs
        if d != 0 then diff := diff + 1
        if d > worst then worst := d
  return (diff, worst)

def rewriteSuite : TestSeq :=
  group "ℝ-equal rewrite is not fixed-point-equal" <|
    test "the two shapes disagree on a large fraction of states"
      (rewriteStats.1 > 1000) $
    test "but never by more than 1 lsb (proved bound is 6)"
      (rewriteStats.2 == 1) $
    -- The documented example from the file header.
    test "worked example: e=64336 s=81068 p=-149121 differs by 1"
      ((uAq 64336 81068 (-149121) - uBq 64336 81068 (-149121)).natAbs == 1)

def exhaustiveSuite : TestSeq :=
  group "mulQ identity, exhaustive at 8/4" <|
    test "holds for all 65536 pairs whose result fits"
      mulQ84Exhaustive.1 $
    test "and is FALSE without the no-overflow hypothesis"
      mulQ84Exhaustive.2 $
    test "the documented counterexample: 17 · 121 / 16 wraps 128 → −128"
      (mulQ84 (BitVec.ofNat 8 17) (BitVec.ofNat 8 121) == -128
        ∧ (17 * 121 : Int) / 16 == 128)

def transportSuite : TestSeq :=
  group "Transport agreement (ℝ →retype→ Q15.16 vs Sparkle mulQ)" <|
    test "every case agrees"
      ((transportCases.filter (fun (a, b) => hwMul a b != refMul a b)).isEmpty) $
    -- Spelled out, so a failure says WHICH direction the rounding went.
    test "negative product with remainder floors down (not toward zero)"
      (hwMul (-1) 1 == -1) $
    test "positive product with remainder floors to zero"
      (hwMul 1 1 == 0) $
    -- The constants the transport produced, re-derived on the Sparkle side.
    test "pa = 0.9 transports to 58982"
      ((q 32 16 9 10).toInt == 58982) $
    -- x = 1, I = 0, p = 0 gives nextX = pa − pb·(Kp+Ki+Kd) = 0.6625.
    -- The transported step evaluates that EXPRESSION in Q15.16, flooring at
    -- each product, and lands on 43419.  Quantizing the already-simplified
    -- constant 0.6625 in one go gives 43417.  The 2-LSB gap is not an error
    -- in either: it is the difference between "the equation, computed in
    -- fixed point" and "the ℝ answer, rounded once" — which is exactly the
    -- per-step error §12.4 has to bound.  Pinned so neither drifts.
    test "transported step evaluates the expression, not the rounded constant"
      (hwMul 43419 65536 == 43419 ∧ (q 32 16 6625 10000).toInt == 43417)

def main : IO UInt32 := do
  lspecIO (Std.HashMap.ofList [("all", [suite, transportSuite, exhaustiveSuite, restatementSuite, rewriteSuite])]) []

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
