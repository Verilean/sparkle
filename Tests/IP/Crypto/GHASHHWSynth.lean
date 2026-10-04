/-
  Synthesis checks for GHASHHW.  Kept in a separate file so the
  GHASHHWTest exe doesn't drag in the elaborator's synth output
  (which makes the linked exe slow to load).
-/
import IP.Crypto.GHASHHW

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Crypto.GHASHHW

private def synth_gmulHWResult
    (start : Signal defaultDomain Bool)
    (xIn yIn : Signal defaultDomain (BitVec 128)) :
    Signal defaultDomain (BitVec 128) :=
  (gmulHW start xIn yIn).result

#synthesizeVerilog synth_gmulHWResult

private def synth_gmulHWDone
    (start : Signal defaultDomain Bool)
    (xIn yIn : Signal defaultDomain (BitVec 128)) :
    Signal defaultDomain Bool :=
  (gmulHW start xIn yIn).done

#synthesizeVerilog synth_gmulHWDone
