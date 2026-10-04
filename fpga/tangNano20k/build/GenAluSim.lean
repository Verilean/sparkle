-- Emit the JIT-C simulator for the modular ALU via #sim.
--   lake env lean fpga/tangNano20k/build/GenAluSim.lean
-- writes .lake/build/gen/sim/<mangled aluTop>_jit.c
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

#sim aluTop
