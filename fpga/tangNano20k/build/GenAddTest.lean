import Sparkle
import IP.Crypto.EcdsaSignSmall
open Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.IP.Crypto.EcdsaSignSmall
set_option maxRecDepth 100000
def addTop (a b : Signal defaultDomain (BitVec 256)) : Signal defaultDomain (BitVec 256) :=
  addModPPub a b
#sim addTop
