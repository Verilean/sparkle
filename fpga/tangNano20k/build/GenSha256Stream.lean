import Sparkle
import IP.Crypto.SHA256Stream
open Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.IP.Crypto.SHA256Stream
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
def shaStreamTop
    (start : Signal defaultDomain Bool) (nBlocks : Signal defaultDomain (BitVec 2))
    (blk0 blk1 : Signal defaultDomain (BitVec 512)) : StreamOut defaultDomain :=
  sha256StreamHW start nBlocks blk0 blk1
#sim shaStreamTop
