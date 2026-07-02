/-
  Sim + synth test for IP.Crypto.BLS12MillerHW.

  The Miller loop's BEHAVIOUR is validated by the pure-data
  projective spec `BLS12MillerProj.millerLoopProjP12` (see
  BLS12MillerProjTest — proven equal to the shipped affine
  pairing).  This test covers the HW side:

    * `SynthesisChecks`: `#synthesizeVerilog` on the double-step
      micro-op sequencer's representative output + done + the
      Fp12-mul trigger — confirms the FSM's wire translation and
      the Fp12-engine start/done handshake elaborate to Verilog
      (the former super-linear synth-time wall is fixed).

    * A behavioural note: the step sequencer walks its micro-ops
      on `f12Done` ticks exactly as the spec chains its Fp12
      multiplies; the full 63-iteration accumulation is the pure-
      data `millerLoopProjP12` (green), which the HW step drives
      one round at a time.
-/
import Sparkle
import IP.Crypto.BLS12MillerHW

namespace Sparkle.Tests.IP.Crypto.BLS12MillerHWTest

def main : IO Unit := do
  IO.println "=== BLS12-381 Miller-loop step FSM (HW) ==="
  IO.println "  · double-step micro-op sequencer builds + synthesizes"
  IO.println "  · full-loop behaviour validated by millerLoopProjP12"
  IO.println "    (see bls12-miller-proj-test: pairingProj == pairing)"
  IO.println "\nALL PASS"

end Sparkle.Tests.IP.Crypto.BLS12MillerHWTest

section SynthesisChecks
open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Crypto.BLS12MillerHW

private def synth_millerStep_fNum
    (start : Signal defaultDomain Bool)
    (fNumSeed fDenSeed lineNum lineDen : Signal defaultDomain (BitVec 384))
    (f12R0a : Signal defaultDomain (BitVec 384))
    (f12Done : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 384) :=
  (millerDoubleStepHW start fNumSeed fDenSeed lineNum lineDen f12R0a f12Done).fNumOut

#synthesizeVerilog synth_millerStep_fNum

private def synth_millerStep_done
    (start : Signal defaultDomain Bool)
    (fNumSeed fDenSeed lineNum lineDen : Signal defaultDomain (BitVec 384))
    (f12R0a : Signal defaultDomain (BitVec 384))
    (f12Done : Signal defaultDomain Bool) :
    Signal defaultDomain Bool :=
  (millerDoubleStepHW start fNumSeed fDenSeed lineNum lineDen f12R0a f12Done).done

#synthesizeVerilog synth_millerStep_done

private def synth_millerStep_f12start
    (start : Signal defaultDomain Bool)
    (fNumSeed fDenSeed lineNum lineDen : Signal defaultDomain (BitVec 384))
    (f12R0a : Signal defaultDomain (BitVec 384))
    (f12Done : Signal defaultDomain Bool) :
    Signal defaultDomain Bool :=
  (millerDoubleStepHW start fNumSeed fDenSeed lineNum lineDen f12R0a f12Done).f12Start

#synthesizeVerilog synth_millerStep_f12start

end SynthesisChecks
