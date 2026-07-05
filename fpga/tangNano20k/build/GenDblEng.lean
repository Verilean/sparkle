import Sparkle
import IP.Crypto.EcdsaSignSmall
open Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.IP.Crypto.EcdsaSignSmall
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
def dblEngTop
    (runStart loadEn : Signal defaultDomain Bool) (loadAddr : Signal defaultDomain (BitVec 6))
    (loadData : Signal defaultDomain (BitVec 256)) (probeAddr : Signal defaultDomain (BitVec 6))
    (progStart : Signal defaultDomain (BitVec 8)) : PdOut defaultDomain :=
  ladderEngine runStart loadEn loadAddr loadData probeAddr progStart
#sim dblEngTop
