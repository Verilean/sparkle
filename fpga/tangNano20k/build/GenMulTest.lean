import Sparkle
import IP.Crypto.EcdsaSignSmall
open Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.IP.Crypto.EcdsaSignSmall
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
def mulPTop (start : Signal defaultDomain Bool) (a b : Signal defaultDomain (BitVec 256)) : Signal defaultDomain (BitVec 256) :=
  (wMulP start a b).result
#sim mulPTop
