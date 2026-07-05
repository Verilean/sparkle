import Sparkle
import IP.Crypto.EcdsaSignSmall
open Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.IP.Crypto.EcdsaSignSmall
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
def signTop
    (signStart extLoadEn : Signal defaultDomain Bool) (extLoadAddr : Signal defaultDomain (BitVec 6))
    (extLoadData : Signal defaultDomain (BitVec 256))
    (kIn : Signal defaultDomain (BitVec 256))
    (probeAddr : Signal defaultDomain (BitVec 6)) : LadderOut defaultDomain :=
  signCtrl signStart extLoadEn extLoadAddr extLoadData kIn probeAddr
#sim signTop
