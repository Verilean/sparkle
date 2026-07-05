import Sparkle
import IP.Crypto.EcdsaSignSmall
open Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.IP.Crypto.EcdsaSignSmall
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
def expTop
    (modN expStart extLoadEn : Signal defaultDomain Bool) (extLoadAddr : Signal defaultDomain (BitVec 6))
    (extLoadData : Signal defaultDomain (BitVec 256))
    (scalarLoadEn : Signal defaultDomain Bool) (scalarIn : Signal defaultDomain (BitVec 256))
    (probeAddr : Signal defaultDomain (BitVec 6)) : LadderOut defaultDomain :=
  expCtrl modN expStart extLoadEn extLoadAddr extLoadData scalarLoadEn scalarIn probeAddr
#sim expTop
