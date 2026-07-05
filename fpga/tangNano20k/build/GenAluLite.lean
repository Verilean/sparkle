import Sparkle
import IP.Crypto.EcdsaSignSmall
open Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.IP.Crypto.EcdsaSignSmall

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def aluLiteTop
    (start : Signal defaultDomain Bool)
    (srcA srcB dst : Signal defaultDomain (BitVec 6))
    (loadEn : Signal defaultDomain Bool)
    (loadAddr : Signal defaultDomain (BitVec 6))
    (loadData : Signal defaultDomain (BitVec 256)) :
    Signal defaultDomain (BitVec 256) :=
  (bignumALUlite start srcA srcB dst loadEn loadAddr loadData).outVal

#sim aluLiteTop
