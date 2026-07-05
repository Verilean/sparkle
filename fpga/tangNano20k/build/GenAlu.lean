-- Emit the modular ALU to Verilog for simulation + area check.
--   lake env lean fpga/tangNano20k/build/GenAlu.lean
import Sparkle
import IP.Crypto.EcdsaSignSmall

open Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.IP.Crypto.EcdsaSignSmall

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def aluTop
    (start : Signal defaultDomain Bool)
    (op : Signal defaultDomain (BitVec 3))
    (srcA srcB dst : Signal defaultDomain (BitVec 6))
    (loadEn : Signal defaultDomain Bool)
    (loadAddr : Signal defaultDomain (BitVec 6))
    (loadData : Signal defaultDomain (BitVec 256)) :
    Signal defaultDomain (BitVec 256) :=
  (bignumALU start op srcA srcB dst loadEn loadAddr loadData).outVal

#writeVerilogDesign aluTop "fpga/tangNano20k/build/alu.v"
