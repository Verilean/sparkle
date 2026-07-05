import Sparkle
import IP.Crypto.HMACSHA256HW
open Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.IP.Crypto.HMACSHA256HW
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
def hmacTop
    (start : Signal defaultDomain Bool) (key : Signal defaultDomain (BitVec 256))
    (blk1 blk2 : Signal defaultDomain (BitVec 512)) (threeBlk : Signal defaultDomain Bool) : HmacOut defaultDomain :=
  hmacSha256 start key blk1 blk2 threeBlk
#sim hmacTop
