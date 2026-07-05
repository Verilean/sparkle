-- Emit the full ECDSA sign orchestrator to hierarchical Verilog for the
-- Tang Nano 20k area check.
--   lake env lean fpga/tangNano20k/build/GenSignSynth.lean
import Sparkle
import IP.Crypto.EcdsaSignSmall

open Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.IP.Crypto.EcdsaSignSmall

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def signSynthTop
    (signStart extLoadEn : Signal defaultDomain Bool) (extLoadAddr : Signal defaultDomain (BitVec 6))
    (extLoadData : Signal defaultDomain (BitVec 256))
    (kIn : Signal defaultDomain (BitVec 256))
    (probeAddr : Signal defaultDomain (BitVec 6)) : LadderOut defaultDomain :=
  signCtrl signStart extLoadEn extLoadAddr extLoadData kIn probeAddr

#writeVerilogDesign signSynthTop "fpga/tangNano20k/build/sign_core.v"
