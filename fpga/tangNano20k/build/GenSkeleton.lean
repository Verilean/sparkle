-- Emit the small-signer skeleton (BRAM regfile + shared mulHW) to Verilog.
--   lake env lean fpga/tangNano20k/build/GenSkeleton.lean
import Sparkle
import IP.Crypto.EcdsaSignSmall

open Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.IP.Crypto.EcdsaSignSmall

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def skelTop
    (start : Signal defaultDomain Bool)
    (srcA srcB dst : Signal defaultDomain (BitVec 6)) :
    Signal defaultDomain (BitVec 256) :=
  (bignumSkeleton start srcA srcB dst).outVal

#writeVerilogDesign skelTop "fpga/tangNano20k/build/skel.v"
