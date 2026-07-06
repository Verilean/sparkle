import Sparkle
import IP.Crypto.Rfc6979HW
open Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.IP.Crypto.Rfc6979HW
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
-- Baked demo key d = 12345.
def rfcTop (start : Signal defaultDomain Bool) (z : Signal defaultDomain (BitVec 256)) : NonceOut defaultDomain :=
  rfc6979HW (BitVec.ofNat 256 12345) start z
#sim rfcTop
