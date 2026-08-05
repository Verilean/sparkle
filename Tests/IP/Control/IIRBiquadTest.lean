/-
  IIR biquad — simulation + synthesis tests.

  The interesting assertion here is `naive_limit_cycles`: it pins the exact
  period-6 oscillation that the naively-quantized resonator sustains from a
  single impulse.  That sequence is the *counterexample half* of the demo — the
  thing DSVerifier can only exhibit up to a bounded horizon — so it is worth
  freezing as a regression: if the fixed-point rounding in
  `IP/Control/FixedPoint.lean` ever changes, this test says so immediately.
-/

import Sparkle
import Sparkle.Compiler.Elab
import IP.Control.IIRBiquad
import LSpec

set_option maxRecDepth 100000

namespace Sparkle.Tests.IP.Control.IIRBiquadTest

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Control.IIRBiquad
open LSpec

/-- Q15.16 word → milliunits, for readable expectations. -/
def milli (x : BitVec 32) : Int := x.toInt * 1000 / 65536

/-- Unit impulse followed by `n` zero samples. -/
def impulse (n : Nat) : List (BitVec 32) :=
  (BitVec.ofInt 32 65536) :: List.replicate n (0#32)

/-- The stable low-pass decays to exactly zero and stays there. -/
def stableOut : List Int :=
  (run stableLPF defaultLim ⟨0#32, 0#32⟩ (impulse 40)).map milli

/-- The naively-quantized resonator's response. -/
def naiveOut : List Int :=
  (run naiveLPF defaultLim ⟨0#32, 0#32⟩ (impulse 40)).map milli

/-- The measured period-6 cycle, repeated.  Note the up/down asymmetry
    (`62` vs `-63`) — that is floor-rounding of the arithmetic shift. -/
def expectedCycle : List Int := [62, 62, 0, -63, -63, 0]

def suite : TestSeq :=
  group "IIR biquad" <|
    -- The stable filter reaches exact zero and stays: no sustained ringing.
    test "stableLPF decays to zero"
      (((stableOut.drop 20).all (· == 0)) == true) $
    test "stableLPF is not identically zero"
      ((stableOut.take 5).any (· != 0)) $
    -- The naive filter never decays: it repeats `expectedCycle` forever.
    test "naiveLPF sustains a period-6 limit cycle"
      ((naiveOut.drop 12).take 18 == expectedCycle ++ expectedCycle ++ expectedCycle) $
    test "naiveLPF energy does not decay"
      (((naiveOut.drop 30).map Int.natAbs).foldl Nat.max 0 == 63) $
    -- The contrast, stated as the demo states it.
    test "stable and naive genuinely differ"
      (stableOut != naiveOut)

def main : IO UInt32 := do
  lspecIO (Std.HashMap.ofList [("all", [suite])]) []

/-- `IO Unit` wrapper for `Tests/AllTests.lean`.

    `AllTests` links every suite into one binary, and the repo convention there
    is an `IO Unit` main that aborts on failure (see
    `Tests/IP/Net/CRC32Test.lean`).  Returning the `lspecIO` code from inside
    `AllTests.main` instead leaves the per-suite `main` unreferenced by the
    aggregate's object file and the link fails on
    `lp_sparkle_..._main`. -/
def mainUnit : IO Unit := do
  let code ← main
  if code != 0 then IO.Process.exit 1

/-! ### Synthesis checks

Build-time only: these fail the build if the `circuit do` in `IIRBiquad.lean`
stops lowering to Verilog. -/

section SynthesisChecks

set_option maxHeartbeats 80000000

/-- The stable filter as a synthesizable top. -/
def stableTop (x : Signal defaultDomain (BitVec 32)) : Signal defaultDomain (BitVec 32) :=
  stableBiquad x

/-- The naive filter as a synthesizable top — the counterexample is real
    hardware too, not just a spreadsheet. -/
def naiveTop (x : Signal defaultDomain (BitVec 32)) : Signal defaultDomain (BitVec 32) :=
  naiveBiquad x

#synthesizeVerilog stableTop
#synthesizeVerilog naiveTop

end SynthesisChecks

end Sparkle.Tests.IP.Control.IIRBiquadTest
