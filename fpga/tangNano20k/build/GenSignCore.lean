import Sparkle
import IP.Crypto.EcdsaSignSmallDemo
open Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.IP.Crypto.EcdsaSignSmallDemo
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
def signCoreTop
    (start : Signal defaultDomain Bool)
    (d k z : Signal defaultDomain (BitVec 256)) : SignSmallOut defaultDomain :=
  signCoreSmall start d k z
#sim signCoreTop
